// SPDX-License-Identifier: GPL-2.0-or-later
/*
 *  History:
 *  Started: Aug 9 by Lawrence Foard (entropy@world.std.com),
 *           to allow user process control of SCSI devices.
 *  Development Sponsored by Killy Corp. NY NY   [guess: 1992]
 *
 * Original driver (sg.c):
 *        Copyright (C) 1992 Lawrence Foard
 * Version 2, 3 and 4 extensions to driver:
 *        Copyright (C) 1998 - 2021 Douglas Gilbert
 *
 */

static int sg_version_num = 40012;  /* [x]xyyzz where [x] empty when x=0 */
#define SG_VERSION_STR "4.0.12"		/* [x]x.[y]y.zz */
static char *sg_version_date = "20210522";

#include <linux/module.h>

#include <linux/fs.h>
#include <linux/kernel.h>
#include <linux/sched.h>
#include <linux/string.h>
#include <linux/mm.h>
#include <linux/errno.h>
#include <linux/mtio.h>
#include <linux/ioctl.h>
#include <linux/slab.h>
#include <linux/fcntl.h>
#include <linux/init.h>
#include <linux/poll.h>
#include <linux/moduleparam.h>
#include <linux/cdev.h>
#include <linux/idr.h>
#include <linux/file.h>		/* for fget() and fput() */
#include <linux/seq_file.h>
#include <linux/blkdev.h>
#include <linux/delay.h>
#include <linux/blktrace_api.h>
#include <linux/mutex.h>
#include <linux/atomic.h>
#include <linux/ratelimit.h>
#include <linux/uio.h>
#include <linux/cred.h>			/* for sg_check_file_access() */
#include <linux/timekeeping.h>
#include <linux/proc_fs.h>		/* used if CONFIG_SCSI_PROC_FS */
#include <linux/xarray.h>
#include <linux/eventfd.h>
#include <linux/debugfs.h>

#include <scsi/scsi.h>
#include <scsi/scsi_eh.h>
#include <scsi/scsi_dbg.h>
#include <scsi/scsi_host.h>
#include <scsi/scsi_driver.h>
#include <scsi/scsi_ioctl.h>
#include <scsi/sg.h>

#include "scsi_logging.h"

#define SG_ALLOW_DIO_DEF 0

#define SG_MAX_DEVS 32768
#define SG_MAX_MULTI_REQ_SZ (2 * 1024 * 1024)

/* Comment out the following line to compile out SCSI_LOGGING stuff */
#define SG_DEBUG 1

#if !IS_ENABLED(SG_DEBUG)
#if IS_ENABLED(DEBUG)	/* If SG_DEBUG not defined, check for DEBUG */
#define SG_DEBUG DEBUG
#endif
#endif

#if IS_ENABLED(CONFIG_SCSI_PROC_FS) || IS_ENABLED(CONFIG_DEBUG_FS)
#define SG_PROC_OR_DEBUG_FS 1
#endif

/*
 * SG_MAX_CDB_SIZE should be 260 (spc4r37 section 3.1.30) however the type
 * of sg_io_hdr::cmd_len can only represent 255. All SCSI commands greater
 * than 16 bytes are "variable length" whose length is a multiple of 4, so:
 */
#define SG_MAX_CDB_SIZE 252

static struct kmem_cache *sg_sense_cache;
#define SG_MEMPOOL_MIN_NR 4
static mempool_t *sg_sense_pool;

#define uptr64(usp_val) ((void __user *)(uintptr_t)(usp_val))
#define cuptr64(usp_val) ((const void __user *)(uintptr_t)(usp_val))

/* Following enum contains the states of sg_request::rq_st */
enum sg_rq_state {	/* N.B. sg_rq_state_arr assumes SG_RQ_AWAIT_RCV==2 */
	SG_RQ_INACTIVE = 0,	/* request not in use (e.g. on fl) */
	SG_RQ_INFLIGHT,		/* active: cmd/req issued, no response yet */
	SG_RQ_AWAIT_RCV,	/* have response from LLD, awaiting receive */
	SG_RQ_BUSY,		/* temporary state should rarely be seen */
	SG_RQ_SHR_SWAP,		/* read-side: is finished, await swap to write-side */
	SG_RQ_SHR_IN_WS,	/* read-side: waits while write-side inflight */
};

/* these varieties of share requests are known before a request is created */
enum sg_shr_var {
	SG_SHR_NONE = 0,	/* no sharing on owning fd */
	SG_SHR_RS_NOT_SRQ,	/* read-side sharing on fd but not on this req */
	SG_SHR_RS_RQ,		/* read-side sharing on this data carrying req */
	SG_SHR_WS_NOT_SRQ,	/* write-side sharing on fd but not on this req */
	SG_SHR_WS_RQ,		/* write-side sharing on this data carrying req */
};

/* If sum_of(dlen) of a fd exceeds this, write() will yield E2BIG */
#define SG_TOT_FD_THRESHOLD (32 * 1024 * 1024)

#define SG_TIME_UNIT_MS 0	/* milliseconds */
/* #define SG_TIME_UNIT_NS 1	   nanoseconds */
#define SG_DEF_TIME_UNIT SG_TIME_UNIT_MS
#define SG_DEFAULT_TIMEOUT mult_frac(SG_DEFAULT_TIMEOUT_USER, HZ, USER_HZ)
#define SG_FD_Q_AT_HEAD 0
#define SG_DEFAULT_Q_AT SG_FD_Q_AT_HEAD /* for backward compatibility */
#define SG_FL_MMAP_DIRECT (SG_FLAG_MMAP_IO | SG_FLAG_DIRECT_IO)

#define SG_MAX_RSV_REQS 8

#define SG_PACK_ID_WILDCARD (-1)
#define SG_TAG_WILDCARD (-1)

#define SG_ADD_RQ_MAX_RETRIES 40	/* to stop infinite _trylock(s) */

/* Bit positions (flags) for sg_request::frq_bm bitmask follow */
#define SG_FRQ_IS_V4I		0	/* true (set) when is v4 interface */
#define SG_FRQ_IS_ORPHAN	1	/* owner of request gone */
#define SG_FRQ_SYNC_INVOC	2	/* synchronous (blocking) invocation */
#define SG_FRQ_US_XFER		3	/* kernel<-->user_space data transfer */
#define SG_FRQ_ABORTING		4	/* in process of aborting this cmd */
#define SG_FRQ_DEACT_ORPHAN	5	/* not keeping orphan so de-activate */
#define SG_FRQ_RECEIVING	6	/* guard against multiple receivers */
#define SG_FRQ_FOR_MMAP		7	/* request needs PAGE_SIZE elements */
#define SG_FRQ_COUNT_ACTIVE	8	/* sfp->submitted + waiting active */
#define SG_FRQ_ISSUED		9	/* blk_execute_rq_nowait() finished */
#define SG_FRQ_POLL_SLEPT	10	/* stop re-entry of hybrid_sleep() */
#define SG_FRQ_RESERVED		11	/* marks a reserved request */

/* Bit positions (flags) for sg_fd::ffd_bm bitmask follow */
#define SG_FFD_FORCE_PACKID	0	/* receive only given pack_id/tag */
#define SG_FFD_NO_CMD_Q		1	/* set: only 1 active req per fd */
#define SG_FFD_KEEP_ORPHAN	2	/* policy for this fd */
#define SG_FFD_HIPRI_SEEN	3	/* could have HIPRI requests active */
#define SG_FFD_TIME_IN_NS	4	/* set: time in nanoseconds, else ms */
#define SG_FFD_Q_AT_TAIL	5	/* set: queue reqs at tail of blk q */
#define SG_FFD_READ_SIDE_ERR	6	/* prior read-side of share failed */
#define SG_FFD_PREFER_TAG	7	/* prefer tag over pack_id (def) */
#define SG_FFD_RELEASE		8	/* release (close) underway */
#define SG_FFD_NO_DURATION	9	/* don't do command duration calc */
#define SG_FFD_MORE_ASYNC	10	/* yield EBUSY more often */
#define SG_FFD_MRQ_ABORT	11	/* SG_IOABORT + FLAG_MULTIPLE_REQS */
#define SG_FFD_EXCL_WAITQ	12	/* append _exclusive to wait_event */
#define SG_FFD_SVB_ACTIVE	13	/* shared variable blocking active */
#define SG_FFD_RESHARE		14	/* reshare limits to single rsv req */

/* Bit positions (flags) for sg_device::fdev_bm bitmask follow */
#define SG_FDEV_EXCLUDE		0	/* have fd open with O_EXCL */
#define SG_FDEV_DETACHING	1	/* may be unexpected device removal */
#define SG_FDEV_LOG_SENSE	2	/* set by ioctl(SG_SET_DEBUG) */

/* xarray 'mark's allow sub-lists within main array/list. */
#define SG_XA_FD_FREE XA_MARK_0		/* xarray sets+clears */
#define SG_XA_FD_UNSHARED XA_MARK_1
#define SG_XA_FD_RS_SHARE XA_MARK_2

#define SG_XA_RQ_FREE XA_MARK_0		/* xarray sets+clears */
#define SG_XA_RQ_INACTIVE XA_MARK_1
#define SG_XA_RQ_AWAIT XA_MARK_2

int sg_big_buff = SG_DEF_RESERVED_SIZE;
/*
 * This variable is accessible via /proc/scsi/sg/def_reserved_size . Each
 * time sg_open() is called a sg_request of this size (or less if there is
 * not enough memory) will be reserved for use by this file descriptor.
 */
static int def_reserved_size = -1;	/* picks up init parameter */
static int sg_allow_dio = SG_ALLOW_DIO_DEF;	/* ignored by code */

static int scatter_elem_sz = SG_SCATTER_SZ;

#define SG_DEF_SECTOR_SZ 512

static int sg_add_device(struct device *, struct class_interface *);
static void sg_remove_device(struct device *, struct class_interface *);

static DEFINE_IDR(sg_index_idr);
static DEFINE_RWLOCK(sg_index_lock); /* Also used to lock fd list for device */

static struct class_interface sg_interface = {
	.add_dev        = sg_add_device,
	.remove_dev     = sg_remove_device,
};

static DEFINE_MUTEX(snapped_mutex);
static char *snapped_buf;

/* Subset of sg_io_hdr found in <scsi/sg.h>, has only [i] and [i->o] fields */
struct sg_slice_hdr3 {
	int interface_id;
	int dxfer_direction;
	u8 cmd_len;
	u8 mx_sb_len;
	u16 iovec_count;
	unsigned int dxfer_len;
	void __user *dxferp;
	u8 __user *cmdp;
	void __user *sbp;
	unsigned int timeout;
	unsigned int flags;
	int pack_id;
	void __user *usr_ptr;
};

struct sg_slice_hdr4 {	/* parts of sg_io_v4 object needed in async usage */
	void __user *sbp;	/* derived from sg_io_v4::response */
	u64 usr_ptr;		/* hold sg_io_v4::usr_ptr as given (u64) */
	int out_resid;
	u32 wr_offset;		/* from v4::spare_in when flagged; in bytes */
	u32 wr_len;		/* for shared reqs maybe < read-side */
	s16 dir;		/* data xfer direction; SG_DXFER_*  */
	u16 cmd_len;		/* truncated of sg_io_v4::request_len */
	u16 max_sb_len;		/* truncated of sg_io_v4::max_response_len */
	u16 mrq_ind;		/* mrq submit order, origin 0 */
	atomic_t pack_id_of_mrq;	/* mrq pack_id, active when > 0 */
};

struct sg_scatter_hold {     /* holding area for scsi scatter gather info */
	struct page **pages;	/* num_sgat element array of struct page* */
	int buflen;		/* capacity in bytes (dlen<=buflen) */
	int dlen;		/* current valid data length of this req */
	u16 page_order;		/* byte_len = (page_size*(2**page_order)) */
	u16 num_sgat;		/* actual number of scatter-gather segments */
};

struct sg_device;		/* forward declarations */
struct sg_fd;

struct sg_request {	/* active SCSI command or inactive request */
	struct sg_scatter_hold sgat_h;	/* hold buffer, perhaps scatter list */
	struct sg_scatter_hold *sgatp;	/* ptr to prev unless write-side shr req */
	union {
		struct sg_slice_hdr3 s_hdr3;  /* subset of sg_io_hdr */
		struct sg_slice_hdr4 s_hdr4; /* reduced size struct sg_io_v4 */
	};
	u32 duration;		/* cmd duration in milli or nano seconds */
	u32 rq_flags;		/* flags given in v3 and v4 */
	u32 rq_idx;		/* my index within parent's srp_arr */
	u32 rq_info;		/* info supplied by v3 and v4 interfaces */
	u32 rq_result;		/* packed scsi request result from LLD */
	int in_resid;		/* requested-actual byte count on data-in */
	int pack_id;		/* v3 pack_id or in v4 request_extra field */
	int sense_len;		/* actual sense buffer length (data-in) */
	atomic_t rq_st;		/* request state, holds a enum sg_rq_state */
	enum sg_shr_var sh_var;	/* sharing variety, SG_SHR_NONE=0 if none */
	u8 cmd_opcode;		/* first byte of SCSI cdb */
	int tag;		/* block layer identifier of request */
	blk_qc_t cookie;	/* ids 1 or more queues for blk_poll() */
	u64 start_ns;		/* starting point of command duration calc */
	unsigned long frq_bm[1];	/* see SG_FRQ_* defines above */
	u8 *sense_bp;		/* mempool alloc-ed sense buffer, as needed */
	struct sg_fd *parentfp;	/* pointer to owning fd, even when on fl */
	struct request *rqq;	/* released in sg_rq_end_io(), bio kept */
	struct sg_request *sh_srp; /* read-side's write srp (or vice versa) */
	struct bio *bio;	/* kept until this req -->SG_RQ_INACTIVE */
	struct execute_work ew_orph;	/* harvest orphan request */
};

struct sg_fd {		/* holds the state of a file descriptor */
	struct sg_device *parentdp;	/* owning device */
	wait_queue_head_t cmpl_wait;	/* queue awaiting req completion */
	struct mutex f_mutex;	/* serialize ioctls on this fd */
	int timeout;		/* defaults to SG_DEFAULT_TIMEOUT      */
	int timeout_user;	/* defaults to SG_DEFAULT_TIMEOUT_USER */
	int low_used_idx;	/* previous or lower used index */
	int low_await_idx;	/* previous or lower await index */
	u32 idx;		/* my index within parent's sfp_arr */
	atomic_t submitted;	/* number inflight or awaiting receive */
	atomic_t waiting;	/* number of requests awaiting receive */
	atomic_t inactives;	/* number of inactive requests */
	atomic_t sum_fd_dlens;	/* when tot_fd_thresh>0 this is sum_of(dlen) */
	atomic_t mrq_id_abort;	/* inactive when 0, else id if aborted */
	int tot_fd_thresh;	/* E2BIG if sum_of(dlen) > this, 0: ignore */
	int sgat_elem_sz;	/* initialized to scatter_elem_sz */
	int mmap_sz;		/* byte size of previous mmap() call */
	pid_t tid;		/* thread id when opened */
	u8 next_cmd_len;	/* 0: automatic, >0: use on next write() */
	unsigned long ffd_bm[1];	/* see SG_FFD_* defines above */
	struct file *filp;	/* my identity when sharing */
	struct sg_fd __rcu *share_sfp;/* fd share cross-references, else NULL */
	struct fasync_struct *async_qp; /* used by asynchronous notification */
	struct eventfd_ctx *efd_ctxp;	/* eventfd context or NULL */
	struct xarray srp_arr;	/* xarray of sg_request object pointers */
	struct sg_request *rsv_arr[SG_MAX_RSV_REQS];
	struct kref f_ref;
	struct execute_work ew_fd;  /* harvest all fd resources and lists */
};

struct sg_device { /* holds the state of each scsi generic device */
	struct scsi_device *device;
	wait_queue_head_t open_wait;    /* queue open() when O_EXCL present */
	struct mutex open_rel_lock;     /* held when in open() or release() */
	struct list_head sfds;
	int max_sgat_elems;     /* adapter's max number of elements in sgat */
	int max_sgat_sz;	/* max number of bytes in sgat list */
	u32 index;		/* device index number */
	u64 create_ns;		/* nanoseconds since bootup device created */
	atomic_t open_cnt;	/* count of opens (perhaps < num(sfds) ) */
	unsigned long fdev_bm[1];	/* see SG_FDEV_* defines above */
	struct gendisk *disk;
	struct cdev *cdev;
	struct xarray sfp_arr;
	struct kref d_ref;
};

struct sg_comm_wr_t {  /* arguments to sg_common_write() */
	bool keep_share;
	int timeout;
	int cmd_len;
	int rsv_idx;		/* wanted rsv_arr index, def: -1 (anyone) */
	int dlen;		/* dout or din length in bytes */
	int wr_offset;		/* non-zero if v4 and DOUT_OFFSET set */
	unsigned long frq_bm[1];	/* see SG_FRQ_* defines above */
	union {		/* selector is frq_bm.SG_FRQ_IS_V4I */
		struct sg_io_hdr *h3p;
		struct sg_io_v4 *h4p;
	};
	struct sg_fd *sfp;
	const u8 __user *u_cmdp;
	const u8 *cmdp;
};

struct sg_mrq_hold {	/* for passing context between mrq functions */
	bool blocking;
	bool chk_abort;
	bool immed;
	bool stop_if;
	bool co_mmap;
	int id_of_mrq;
	int s_res;		/* secondary error: some-good-then-error */
	u32 cdb_mxlen;		/* cdb length in cdb_ap, actual be may less */
	u32 tot_reqs;		/* total number of requests and cdb_s */
	struct sg_comm_wr_t *cwrp;	/* cwrp->h4p is mrq control object */
	u8 *cdb_ap;		/* array of commands */
	struct sg_io_v4 *a_hds;	/* array of request to execute */
	struct sg_scatter_hold *co_mmap_sgatp;
};

/* tasklet or soft irq callback */
static void sg_rq_end_io(struct request *rqq, blk_status_t status);
/* Declarations of other static functions used before they are defined */
static int sg_proc_init(void);
static void sg_dfs_init(void);
static void sg_dfs_exit(void);
static int sg_start_req(struct sg_request *srp, struct sg_comm_wr_t *cwrp,
			int dxfer_dir);
static void sg_finish_scsi_blk_rq(struct sg_request *srp);
static int sg_mk_sgat(struct sg_scatter_hold *schp, struct sg_fd *sfp, int minlen);
static void sg_remove_sgat(struct sg_fd *sfp, struct sg_scatter_hold *schp);
static int sg_receive_v3(struct sg_fd *sfp, struct sg_request *srp,
			 void __user *p);
static int sg_submit_v3(struct sg_fd *sfp, struct sg_io_hdr *hp, bool sync,
			struct sg_request **o_srp);
static struct sg_request *sg_common_write(struct sg_comm_wr_t *cwrp);
static int sg_wait_event_srp(struct sg_fd *sfp, void __user *p,
			     struct sg_io_v4 *h4p, struct sg_request *srp);
static int sg_receive_v4(struct sg_fd *sfp, struct sg_request *srp,
			 void __user *p, struct sg_io_v4 *h4p);
static int sg_read_append(struct sg_request *srp, void __user *outp,
			  int num_xfer);
static void sg_remove_srp(struct sg_request *srp);
static struct sg_fd *sg_add_sfp(struct sg_device *sdp, struct file *filp);
static void sg_remove_sfp(struct kref *);
static void sg_remove_sfp_share(struct sg_fd *sfp, bool is_rd_side);
static struct sg_request *sg_find_srp_by_id(struct sg_fd *sfp, int id,
					    bool is_tag);
static bool sg_mrq_get_ready_srp(struct sg_fd *sfp, struct sg_request **srpp);
static struct sg_request *sg_setup_req(struct sg_comm_wr_t *cwrp,
				       enum sg_shr_var sh_var);
static void sg_deact_request(struct sg_fd *sfp, struct sg_request *srp);
static struct sg_device *sg_get_dev(int min_dev);
static void sg_device_destroy(struct kref *kref);
static struct sg_request *sg_mk_srp_sgat(struct sg_fd *sfp, bool first,
					 int db_len);
static int sg_abort_req(struct sg_fd *sfp, struct sg_request *srp);
static int sg_sfp_blk_poll(struct sg_fd *sfp, int loop_count);
static int sg_srp_q_blk_poll(struct sg_request *srp, struct request_queue *q,
			     int loop_count);
#if IS_ENABLED(CONFIG_SCSI_LOGGING) && IS_ENABLED(SG_DEBUG)
static const char *sg_rq_st_str(enum sg_rq_state rq_st, bool long_str);
static const char *sg_shr_str(enum sg_shr_var sh_var, bool long_str);
#endif
#if IS_ENABLED(SG_PROC_OR_DEBUG_FS)
static int sg_proc_debug_sdev(struct sg_device *sdp, char *obp, int len,
			      int *fd_counterp, bool reduced);
static void sg_take_snap(struct sg_fd *sfp, bool clear_first);
#endif

#define SG_WRITE_COUNT_LIMIT (32 * 1024 * 1024)

#define SZ_SG_HEADER ((int)sizeof(struct sg_header))	/* v1 and v2 header */
#define SZ_SG_IO_HDR ((int)sizeof(struct sg_io_hdr))	/* v3 header */
#define SZ_SG_IO_V4 ((int)sizeof(struct sg_io_v4))  /* v4 header (in bsg.h) */
#define SZ_SG_REQ_INFO ((int)sizeof(struct sg_req_info))
#define SZ_SG_EXTENDED_INFO ((int)sizeof(struct sg_extended_info))

/* There is a assert that SZ_SG_IO_V4 >= SZ_SG_IO_HDR in first function */

#define SG_IS_DETACHING(sdp) unlikely(test_bit(SG_FDEV_DETACHING, (sdp)->fdev_bm))
#define SG_HAVE_EXCLUDE(sdp) test_bit(SG_FDEV_EXCLUDE, (sdp)->fdev_bm)
#define SG_IS_O_NONBLOCK(sfp) (!!((sfp)->filp->f_flags & O_NONBLOCK))
#define SG_RQ_ACTIVE(srp) (atomic_read(&(srp)->rq_st) != SG_RQ_INACTIVE)
#define SG_IS_V4I(srp) test_bit(SG_FRQ_IS_V4I, (srp)->frq_bm)

/*
 * Kernel needs to be built with CONFIG_SCSI_LOGGING to see log messages.
 * 'depth' is a number between 1 (most severe) and 7 (most noisy, most
 * information). All messages are logged as informational (KERN_INFO). In
 * the unexpected situation where sfp or sdp is NULL the macro reverts to
 * a pr_info and ignores SCSI_LOG_TIMEOUT and always prints to the log.
 * Example: this invocation: 'scsi_logging_level -s -T 3' will print
 * depth (aka level) 1 and 2 SG_LOG() messages.
 */

#define SG_PROC_DEBUG_SZ 8192
#define SG_SNAP_BUFF_SZ (SG_PROC_DEBUG_SZ * 8)

#if IS_ENABLED(CONFIG_SCSI_LOGGING) && IS_ENABLED(SG_DEBUG)
#define SG_LOG_BUFF_SZ 48
#define SG_LOG_ACTIVE 1

#define SG_LOG(depth, sfp, fmt, a...)					\
	do {								\
		char _b[SG_LOG_BUFF_SZ];				\
		int _tid = (current ? current->pid : -1);		\
		struct sg_fd *_fp = sfp;				\
		struct sg_device *_sdp = _fp ? _fp->parentdp : NULL;	\
									\
		if (likely(_sdp && _sdp->disk)) {			\
			snprintf(_b, sizeof(_b), "sg%u: tid=%d",	\
				 _sdp->index, _tid);			\
			SCSI_LOG_TIMEOUT(depth,				\
					 sdev_prefix_printk(KERN_INFO,	\
					 _sdp->device, _b, fmt, ##a));	\
		} else							\
			pr_info("sg: sdp or sfp NULL, " fmt, ##a);	\
	} while (0)
#else
#define SG_LOG(depth, sfp, fmt, a...) do { } while (0)
#endif	/* end of CONFIG_SCSI_LOGGING && SG_DEBUG conditional */

/*
 * The SCSI interfaces that use read() and write() as an asynchronous variant of
 * ioctl(..., SG_IO, ...) are fundamentally unsafe, since there are lots of ways
 * to trigger read() and write() calls from various contexts with elevated
 * privileges. This can lead to kernel memory corruption (e.g. if these
 * interfaces are called through splice()) and privilege escalation inside
 * userspace (e.g. if a process with access to such a device passes a file
 * descriptor to a SUID binary as stdin/stdout/stderr).
 *
 * This function provides protection for the legacy API by restricting the
 * calling context.
 */
static int
sg_check_file_access(struct file *filp, const char *caller)
{
	/* can't put following in declarations where it belongs */
	compiletime_assert(SZ_SG_IO_V4 >= SZ_SG_IO_HDR,
			   "struct sg_io_v4 should be larger than sg_io_hdr");

	if (unlikely(filp->f_cred != current_real_cred())) {
		pr_err_once("%s: process %d (%s) changed security contexts after opening file descriptor, this is not allowed.\n",
			caller, task_tgid_vnr(current), current->comm);
		return -EPERM;
	}
	if (unlikely(uaccess_kernel())) {
		pr_err_once("%s: process %d (%s) called from kernel context, this is not allowed.\n",
			caller, task_tgid_vnr(current), current->comm);
		return -EACCES;
	}
	return 0;
}

static int
sg_wait_open_event(struct sg_device *sdp, bool o_excl)
		__must_hold(sdp->open_rel_lock)
{
	int res = 0;

	if (o_excl) {
		while (atomic_read(&sdp->open_cnt) > 0) {
			mutex_unlock(&sdp->open_rel_lock);
			res = wait_event_interruptible
				(sdp->open_wait,
				 (SG_IS_DETACHING(sdp) || atomic_read(&sdp->open_cnt) == 0));
			mutex_lock(&sdp->open_rel_lock);

			if (res) /* -ERESTARTSYS */
				return res;
			if (SG_IS_DETACHING(sdp))
				return -ENODEV;
		}
	} else {
		while (SG_HAVE_EXCLUDE(sdp)) {
			mutex_unlock(&sdp->open_rel_lock);
			res = wait_event_interruptible
				(sdp->open_wait, (SG_IS_DETACHING(sdp) || !SG_HAVE_EXCLUDE(sdp)));
			mutex_lock(&sdp->open_rel_lock);

			if (res) /* -ERESTARTSYS */
				return res;
			if (SG_IS_DETACHING(sdp))
				return -ENODEV;
		}
	}

	return res;
}

/*
 * scsi_block_when_processing_errors() returns 0 when dev was taken offline by
 * error recovery, 1 otherwise (i.e. okay). Even if in error recovery, let
 * user continue if O_NONBLOCK set. Permits SCSI commands to be issued during
 * error recovery. Tread carefully.
 * Returns 0 for ok (i.e. allow), -EPROTO if sdp is NULL, otherwise -ENXIO .
 */
static inline int
sg_allow_if_err_recovery(struct sg_device *sdp, bool non_block)
{
	if (!sdp)
		return -EPROTO;
	if (SG_IS_DETACHING(sdp))
		return -ENODEV;
	if (non_block)
		return 0;
	if (likely(scsi_block_when_processing_errors(sdp->device)))
		return 0;
	return -ENXIO;
}

/*
 * Corresponds to the open() system call on sg devices. Implements O_EXCL on
 * a per device basis using 'open_cnt'. If O_EXCL and O_NONBLOCK and there is
 * already a sg handle open on this device then it fails with an errno of
 * EBUSY. Without the O_NONBLOCK flag then this thread enters an interruptible
 * wait until the other handle(s) are closed.
 */
static int
sg_open(struct inode *inode, struct file *filp)
{
	bool o_excl, non_block;
	int res;
	__maybe_unused int o_count;
	int min_dev = iminor(inode);
	int op_flags = filp->f_flags;
	struct sg_device *sdp;
	struct sg_fd *sfp;

	nonseekable_open(inode, filp);
	o_excl = !!(op_flags & O_EXCL);
	non_block = !!(op_flags & O_NONBLOCK);
	if (unlikely(o_excl) && ((op_flags & O_ACCMODE) == O_RDONLY))
		return -EPERM;/* not permitted, need write access for O_EXCL */
	sdp = sg_get_dev(min_dev);	/* increments sdp->d_ref */
	if (IS_ERR(sdp))
		return PTR_ERR(sdp);

	/* Prevent the device driver from vanishing while we sleep */
	res = scsi_device_get(sdp->device);
	if (unlikely(res))
		goto sg_put;
	res = scsi_autopm_get_device(sdp->device);
	if (unlikely(res))
		goto sdp_put;
	res = sg_allow_if_err_recovery(sdp, non_block);
	if (unlikely(res))
		goto error_out;

	mutex_lock(&sdp->open_rel_lock);
	if (non_block) {
		if (unlikely(o_excl)) {
			if (atomic_read(&sdp->open_cnt) > 0) {
				res = -EBUSY;
				goto error_mutex_locked;
			}
		} else {
			if (unlikely(SG_HAVE_EXCLUDE(sdp))) {
				res = -EBUSY;
				goto error_mutex_locked;
			}
		}
	} else {
		res = sg_wait_open_event(sdp, o_excl);
		if (unlikely(res)) /* -ERESTARTSYS or -ENODEV */
			goto error_mutex_locked;
	}

	/* N.B. at this point we are holding the open_rel_lock */
	if (unlikely(o_excl))
		set_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm);

	o_count = atomic_inc_return(&sdp->open_cnt);
	sfp = sg_add_sfp(sdp, filp);	/* increments sdp->d_ref */
	if (IS_ERR(sfp)) {
		atomic_dec(&sdp->open_cnt);
		res = PTR_ERR(sfp);
		goto out_undo;
	}

	filp->private_data = sfp;
	sfp->tid = (current ? current->pid : -1);
	mutex_unlock(&sdp->open_rel_lock);
	SG_LOG(3, sfp, "%s: o_count after=%d on minor=%d, op_flags=0x%x%s\n",
	       __func__, o_count, min_dev, op_flags,
	       (non_block ? " O_NONBLOCK" : ""));

	res = 0;
sg_put:
	kref_put(&sdp->d_ref, sg_device_destroy);  /* get: sg_get_dev() */
	return res;

out_undo:
	if (unlikely(o_excl)) {		/* undo if error */
		clear_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm);
		wake_up_interruptible(&sdp->open_wait);
	}
error_mutex_locked:
	mutex_unlock(&sdp->open_rel_lock);
error_out:
	scsi_autopm_put_device(sdp->device);
sdp_put:
	scsi_device_put(sdp->device);
	goto sg_put;
}

static inline bool
sg_fd_is_shared(struct sg_fd *sfp)
{
	return !xa_get_mark(&sfp->parentdp->sfp_arr, sfp->idx,
			    SG_XA_FD_UNSHARED);
}

static inline struct sg_fd *
sg_fd_share_ptr(struct sg_fd *sfp)
{
	struct sg_fd *res_sfp;
	struct sg_device *sdp = sfp->parentdp;

	rcu_read_lock();
	if (xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_UNSHARED))
		res_sfp = NULL;
	else
		res_sfp = sfp->share_sfp;
	rcu_read_unlock();
	return res_sfp;
}

/*
 * Picks up driver or host (transport) errors and actual SCSI status problems.
 * Specifically SAM_STAT_CONDITION_MET is _not_ an error.
 */
static inline bool
sg_result_is_good(int rq_result)
{
	/* Take lower 4 bits of driver byte and all host byte */
	const int ml_result_msk = 0x0fff0000;

	return !(rq_result & ml_result_msk) && scsi_status_is_good(rq_result);
}

/*
 * Release resources associated with a prior, successful sg_open(). It can be
 * seen as the (final) close() call on a sg device file descriptor in the user
 * space. The real work releasing all resources associated with this file
 * descriptor is done by sg_uc_remove_sfp() which is scheduled by
 * sg_remove_sfp().
 */
static int
sg_release(struct inode *inode, struct file *filp)
{
	int o_count;
	struct sg_device *sdp;
	struct sg_fd *sfp;

	sfp = filp->private_data;
	sdp = sfp ? sfp->parentdp : NULL;
	if (unlikely(!sdp))
		return -ENXIO;

	if (unlikely(xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_FREE))) {
		SG_LOG(1, sfp, "%s: sfp already erased!!!\n", __func__);
		return 0;	/* yell out but can't fail */
	}

	mutex_lock(&sdp->open_rel_lock);
	o_count = atomic_read(&sdp->open_cnt);
	SG_LOG(3, sfp, "%s: open count before=%d\n", __func__, o_count);
	if (unlikely(test_and_set_bit(SG_FFD_RELEASE, sfp->ffd_bm)))
		SG_LOG(1, sfp, "%s: second release on this fd ? ?\n",
		       __func__);
	scsi_autopm_put_device(sdp->device);
	if (likely(!xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_FREE)) &&
	    sg_fd_is_shared(sfp))
		sg_remove_sfp_share(sfp, xa_get_mark(&sdp->sfp_arr, sfp->idx,
						     SG_XA_FD_RS_SHARE));
	kref_put(&sfp->f_ref, sg_remove_sfp);	/* init=1: sg_add_sfp() */
	/*
	 * Possibly many open()s waiting on exclude clearing, start many;
	 * only open(O_EXCL)'s wait when open_cnt<2 and only start one.
	 */
	if (test_and_clear_bit(SG_FDEV_EXCLUDE, sdp->fdev_bm))
		wake_up_interruptible_all(&sdp->open_wait);
	else if (o_count < 2)
		wake_up_interruptible(&sdp->open_wait);
	mutex_unlock(&sdp->open_rel_lock);
	return 0;
}

static inline void
sg_comm_wr_init(struct sg_comm_wr_t *cwrp)
{
	memset(cwrp, 0, sizeof(*cwrp));
	WRITE_ONCE(cwrp->frq_bm[0], 0);
	cwrp->rsv_idx = -1;
}

/*
 * ***********************************************************************
 * write(2) related functions follow. They are shown before read(2) related
 * functions. That is because SCSI commands/requests are first "written" to
 * the SCSI device by using write(2), ioctl(SG_IOSUBMIT) or the first half
 * of the synchronous ioctl(SG_IO) system call.
 * ***********************************************************************
 */

/* This is the write(2) system call entry point. v4 interface disallowed. */
static ssize_t
sg_write(struct file *filp, const char __user *p, size_t count, loff_t *ppos)
{
	bool get_v3_hdr;
	int mxsize, cmd_size, input_size, res;
	u8 opcode;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	struct sg_request *srp;
	struct sg_header ov2hdr;
	struct sg_io_hdr v3hdr;
	struct sg_header *ohp = &ov2hdr;
	struct sg_io_hdr *h3p = &v3hdr;
	struct sg_comm_wr_t cwr;

	res = sg_check_file_access(filp, __func__);
	if (unlikely(res))
		return res;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: write(3rd arg) count=%d\n", __func__, (int)count);
	res = sg_allow_if_err_recovery(sdp, !!(filp->f_flags & O_NONBLOCK));
	if (unlikely(res))
		return res;
	if (unlikely(count < SZ_SG_HEADER || count > SG_WRITE_COUNT_LIMIT))
		return -EIO;
#ifdef CONFIG_COMPAT
	if (in_compat_syscall())
		get_v3_hdr = (count == sizeof(struct compat_sg_io_hdr));
	else
		get_v3_hdr = (count == sizeof(struct sg_io_hdr));
#else
	get_v3_hdr = (count == sizeof(struct sg_io_hdr));
#endif
	if (get_v3_hdr) {
		if (get_sg_io_hdr(h3p, p))
			return -EFAULT;
	} else {
		if (copy_from_user(ohp, p, SZ_SG_HEADER))
			return -EFAULT;
		if (ohp->reply_len < 0) {	/* not v2, may be v3 */
			bool lt = false;

#ifdef CONFIG_COMPAT
			if (in_compat_syscall())
				lt = (count < sizeof(struct compat_sg_io_hdr));
			else
				lt = (count < sizeof(struct sg_io_hdr));
#else
			lt = (count < sizeof(struct sg_io_hdr));
#endif
			if (unlikely(lt))
				return -EIO;
			get_v3_hdr = true;
			if (unlikely(get_sg_io_hdr(h3p, p)))
				return -EFAULT;
		}
	}
	if (get_v3_hdr) {
		/* v3 dxfer_direction_s are all negative values by design */
		if (h3p->dxfer_direction >= 0) {	/* so it is not v3 */
			memcpy(ohp, h3p, count);
			goto to_v2;
		}
		if (h3p->interface_id != 'S') {
			pr_info_once("sg: %s: v3 interface only here\n",
				     __func__);
			return -EPERM;
		}
		pr_warn_once("Please use %s instead of write(),\n%s\n",
			     "ioctl(SG_SUBMIT_V3)",
			     "  See: https://sg.danny.cz/sg/sg_v40.html");
		res = sg_submit_v3(sfp, h3p, false, NULL);
		return res < 0 ? res : (int)count;
	}
to_v2:
	/* v1 and v2 interfaces processed below this point */
	if (unlikely(count < SZ_SG_HEADER + 6))
		return -EIO;    /* minimum scsi command length is 6 bytes */
	p += SZ_SG_HEADER;
	if (unlikely(get_user(opcode, p)))
		return -EFAULT;
	mutex_lock(&sfp->f_mutex);
	if (unlikely(sfp->next_cmd_len > 0)) {
		cmd_size = sfp->next_cmd_len;
		sfp->next_cmd_len = 0;	/* reset, only this write() effected */
	} else {
		cmd_size = COMMAND_SIZE(opcode);  /* old: SCSI command group */
		if (opcode >= 0xc0 && ohp->twelve_byte)
			cmd_size = 12;
	}
	mutex_unlock(&sfp->f_mutex);
	SG_LOG(4, sfp, "%s:   scsi opcode=0x%02x, cmd_size=%d\n", __func__,
	       (unsigned int)opcode, cmd_size);
	input_size = count - cmd_size;
	mxsize = max_t(int, input_size, ohp->reply_len);
	mxsize -= SZ_SG_HEADER;
	input_size -= SZ_SG_HEADER;
	if (unlikely(input_size < 0))
		return -EIO; /* Insufficient bytes passed for this command. */
	memset(h3p, 0, sizeof(*h3p));
	h3p->interface_id = '\0';/* indicate v1 or v2 interface (tunnelled) */
	h3p->cmd_len = (u8)cmd_size;
	h3p->iovec_count = 0;
	h3p->mx_sb_len = 0;
	if (input_size > 0)
		h3p->dxfer_direction = (ohp->reply_len > SZ_SG_HEADER) ?
		    SG_DXFER_TO_FROM_DEV : SG_DXFER_TO_DEV;
	else
		h3p->dxfer_direction = (mxsize > 0) ? SG_DXFER_FROM_DEV :
						      SG_DXFER_NONE;
	h3p->dxfer_len = mxsize;
	if (h3p->dxfer_direction == SG_DXFER_TO_DEV ||
	    h3p->dxfer_direction == SG_DXFER_TO_FROM_DEV)
		h3p->dxferp = (u8 __user *)p + cmd_size;
	else
		h3p->dxferp = NULL;
	h3p->sbp = NULL;
	h3p->timeout = ohp->reply_len;	/* structure abuse ... */
	h3p->flags = input_size;	/* structure abuse ... */
	h3p->pack_id = ohp->pack_id;
	h3p->usr_ptr = NULL;
	/*
	 * SG_DXFER_TO_FROM_DEV is functionally equivalent to SG_DXFER_FROM_DEV,
	 * but it is possible that the app intended SG_DXFER_TO_DEV, because
	 * there is a non-zero input_size, so emit a warning.
	 */
	if (unlikely(h3p->dxfer_direction == SG_DXFER_TO_FROM_DEV)) {
		printk_ratelimited
			(KERN_WARNING
			 "%s: data in/out %d/%d bytes for SCSI command 0x%x-- guessing data in;\n"
			 "   program %s not setting count and/or reply_len properly\n",
			 __func__, ohp->reply_len - (int)SZ_SG_HEADER,
			 input_size, (unsigned int)opcode, current->comm);
	}
	sg_comm_wr_init(&cwr);
	cwr.h3p = h3p;
	cwr.dlen = h3p->dxfer_len;
	cwr.timeout = sfp->timeout;
	cwr.cmd_len = cmd_size;
	cwr.sfp = sfp;
	cwr.u_cmdp = p;
	srp = sg_common_write(&cwr);
	return (IS_ERR(srp)) ? PTR_ERR(srp) : (int)count;
}

static inline int
sg_chk_mmap(struct sg_fd *sfp, int rq_flags, int len)
{
	struct sg_request *rsv_srp = sfp->rsv_arr[0];

	if (unlikely(sfp->mmap_sz == 0))
		return -EBADFD;
	if (unlikely(atomic_read(&sfp->submitted) > 0))
		return -EBUSY;  /* already active requests on fd */
	if (IS_ERR_OR_NULL(rsv_srp))
		return -EPROTO;	/* first element always a reserve req */
	if (unlikely(len > rsv_srp->sgatp->buflen))
		return -ENOMEM; /* MMAP_IO size must fit in reserve */
	if (unlikely(len > sfp->mmap_sz))
		return -ENOMEM; /* MMAP_IO size can't exceed mmap() size */
	if (unlikely(rq_flags & SG_FLAG_DIRECT_IO))
		return -EINVAL; /* not both MMAP_IO and DIRECT_IO */
	return 0;
}

static int
sg_fetch_cmnd(struct sg_fd *sfp, const u8 __user *u_cdbp, int len, u8 *cdbp)
{
	if (unlikely(!u_cdbp || len < 6 || len > SG_MAX_CDB_SIZE))
		return -EMSGSIZE;
	if (copy_from_user(cdbp, u_cdbp, len))
		return -EFAULT;
	if (O_RDWR != (sfp->filp->f_flags & O_ACCMODE)) {	/* read-only */
		switch (sfp->parentdp->device->type) {
		case TYPE_DISK:
		case TYPE_RBC:
		case TYPE_ZBC:
			return blk_verify_command(cdbp, sfp->filp->f_mode);
		default:	/* SSC, SES, etc cbd_s may differ from SBC */
			break;
		}
	}
	return 0;
}

static int
sg_submit_v3(struct sg_fd *sfp, struct sg_io_hdr *hp, bool sync,
	     struct sg_request **o_srp)
{
	unsigned long ul_timeout;
	struct sg_request *srp;
	struct sg_comm_wr_t cwr;

	/* now doing v3 blocking (sync) or non-blocking submission */
	if (unlikely(hp->flags & SGV4_FLAG_MULTIPLE_REQS))
		return -ERANGE;		/* need to use v4 interface */
	if (unlikely(hp->flags & SG_FLAG_MMAP_IO)) {
		int res = sg_chk_mmap(sfp, hp->flags, hp->dxfer_len);

		if (unlikely(res))
			return res;
	}
	/* when v3 seen, allow cmd_q on this fd (def: cmd_q) */
	if (test_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm))
		clear_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm);
	ul_timeout = msecs_to_jiffies(hp->timeout);
	sg_comm_wr_init(&cwr);
	__assign_bit(SG_FRQ_SYNC_INVOC, cwr.frq_bm, (int)sync);
	cwr.h3p = hp;
	cwr.dlen = hp->dxfer_len;
	cwr.timeout = min_t(unsigned long, ul_timeout, INT_MAX);
	cwr.cmd_len = hp->cmd_len;
	cwr.sfp = sfp;
	cwr.u_cmdp = hp->cmdp;
	srp = sg_common_write(&cwr);
	if (IS_ERR(srp))
		return PTR_ERR(srp);
	if (o_srp)
		*o_srp = srp;
	return 0;
}

/* Clear from and including driver_status to end of sg_io_v4 object */
static inline void
sg_v4h_partial_zero(struct sg_io_v4 *h4p)
{
	static const int off = offsetof(struct sg_io_v4, driver_status);

	memset((u8 *)h4p + off, 0, SZ_SG_IO_V4 - off);
}

static void
sg_sgat_zero(struct sg_scatter_hold *sgatp, int off, int nbytes)
{
	int k, rem, off_pl_nbyt;
	int ind = 0;
	int pg_ind = 0;
	int num_sgat = sgatp->num_sgat;
	int elem_sz = PAGE_SIZE * (1 << sgatp->page_order);
	struct page *pg_ep = sgatp->pages[pg_ind];

	if (off >= sgatp->dlen)
		return;
	off_pl_nbyt = off + nbytes;
	if (off_pl_nbyt >= sgatp->dlen) {
		nbytes = sgatp->dlen - off;
		off_pl_nbyt = off + nbytes;
	}
	/* first loop steps over off bytes, second loop zeros nbytes */
	for (k = 0; k < off; k += rem) {
		rem = off - k;
		if (rem >= elem_sz) {
			++pg_ind;
			if (pg_ind >= num_sgat)
				return;
			rem = elem_sz;
			ind = 0;
		} else {
			ind = elem_sz - rem;
		}
	}
	pg_ep = sgatp->pages[pg_ind];
	for ( ; k < off_pl_nbyt; k += rem) {
		rem = off_pl_nbyt - k;
		if (rem >= elem_sz) {
			memset((u8 *)pg_ep + ind, 0, elem_sz - ind);
			if (++pg_ind >= num_sgat)
				return;
			pg_ep = sgatp->pages[pg_ind];
			rem = elem_sz;
			ind = 0;
		} else {
			memset((u8 *)pg_ep + ind, 0, rem - ind);
			ind = elem_sz - rem;
		}
	}
}

/*
 * Copies nbytes from the start of 'fromp' into sgatp (this driver's scatter
 * gather list representation) starting at byte offset 'off'. If nbytes is
 * too long then it is trimmed.
 */
static void
sg_sgat_cp_into(struct sg_scatter_hold *sgatp, int off, const u8 *fromp,
		int nbytes)
{
	int k, rem, off_pl_nbyt;
	int ind = 0;
	int from_off = 0;
	int pg_ind = 0;
	int num_sgat = sgatp->num_sgat;
	int elem_sz = PAGE_SIZE * (1 << sgatp->page_order);
	struct page *pg_ep = sgatp->pages[pg_ind];

	if (off >= sgatp->dlen)
		return;
	off_pl_nbyt = off + nbytes;
	if (off_pl_nbyt >= sgatp->dlen) {
		nbytes = sgatp->dlen - off;
		off_pl_nbyt = off + nbytes;
	}
	/* first loop steps over off bytes, second loop zeros nbytes */
	for (k = 0; k < off; k += rem) {
		rem = off - k;
		if (rem >= elem_sz) {
			++pg_ind;
			if (pg_ind >= num_sgat)
				return;
			rem = elem_sz;
			ind = 0;
		} else {
			ind = elem_sz - rem;
		}
	}
	pg_ep = sgatp->pages[pg_ind];
	for ( ; k < off_pl_nbyt; k += rem) {
		rem = off_pl_nbyt - k;
		if (rem >= elem_sz) {
			memcpy((u8 *)pg_ep + ind, fromp + from_off,
			       elem_sz - ind);
			if (++pg_ind >= num_sgat)
				return;
			pg_ep = sgatp->pages[pg_ind];
			rem = elem_sz;
			ind = 0;
			from_off += elem_sz - ind;
		} else {
			memcpy((u8 *)pg_ep + ind, fromp + from_off, rem - ind);
			/* last time around, no need to update indexes */
		}
	}
}

/*
 * Takes a pointer (cop) to the multiple request (mrq) control object and
 * a pointer to the command array. The command array (with tot_reqs elements)
 * is written out (flushed) to user space pointer cop->din_xferp. The
 * secondary error value (s_res) is placed in the cop->spare_out field.
 */
static int
sg_mrq_arr_flush(struct sg_mrq_hold *mhp)
{
	int s_res = mhp->s_res;
	struct sg_io_v4 *cop = mhp->cwrp->h4p;
	void __user *p = uptr64(cop->din_xferp);
	struct sg_io_v4 *a_hds = mhp->a_hds;
	u32 sz = min(mhp->tot_reqs * SZ_SG_IO_V4, cop->din_xfer_len);

	if (unlikely(s_res))
		cop->spare_out = -s_res;
	if (unlikely(!p))
		return 0;
	if (sz > 0) {
		if (copy_to_user(p, a_hds, sz))
			return -EFAULT;
	}
	return 0;
}

static int
sg_mrq_1complet(struct sg_mrq_hold *mhp, struct sg_fd *sfp,
		struct sg_request *srp)
{
	int s_res, indx;
	int tot_reqs = mhp->tot_reqs;
	struct sg_io_v4 *hp;
	struct sg_io_v4 *a_hds = mhp->a_hds;

	if (unlikely(!srp))
		return -EPROTO;
	indx = srp->s_hdr4.mrq_ind;
	if (unlikely(srp->parentfp != sfp)) {
		SG_LOG(1, sfp, "%s: mrq_ind=%d, sfp out-of-sync\n",
		       __func__, indx);
		return -EPROTO;
	}
	SG_LOG(3, sfp, "%s: mrq_ind=%d, pack_id=%d\n", __func__, indx,
	       srp->pack_id);
	if (unlikely(indx < 0 || indx >= tot_reqs))
		return -EPROTO;
	hp = a_hds + indx;
	s_res = sg_receive_v4(sfp, srp, NULL, hp);
	if (unlikely(s_res == -EFAULT))
		return s_res;
	hp->info |= SG_INFO_MRQ_FINI;
	if (mhp->co_mmap) {
		sg_sgat_cp_into(mhp->co_mmap_sgatp, indx * SZ_SG_IO_V4,
				(const u8 *)hp, SZ_SG_IO_V4);
		if (sfp->async_qp && (hp->flags & SGV4_FLAG_SIGNAL))
			kill_fasync(&sfp->async_qp, SIGPOLL, POLL_IN);
		if (sfp->efd_ctxp && (srp->rq_flags & SGV4_FLAG_EVENTFD)) {
			u64 n = eventfd_signal(sfp->efd_ctxp, 1);

			if (n != 1)
				pr_info("%s: srp=%pK eventfd_signal problem\n",
					__func__, srp);
		}
	} else if (sfp->async_qp && (hp->flags & SGV4_FLAG_SIGNAL)) {
		s_res = sg_mrq_arr_flush(mhp);
		if (unlikely(s_res))	/* can only be -EFAULT */
			return s_res;
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_IN);
	}
	return 0;
}

static int
sg_wait_mrq_event(struct sg_fd *sfp, struct sg_request **srpp)
{
	if (test_bit(SG_FFD_EXCL_WAITQ, sfp->ffd_bm))
		return __wait_event_interruptible_exclusive
					(sfp->cmpl_wait,
					 sg_mrq_get_ready_srp(sfp, srpp));
	return __wait_event_interruptible(sfp->cmpl_wait,
					  sg_mrq_get_ready_srp(sfp, srpp));
}

/*
 * This is a fair-ish algorithm for an interruptible wait on two file
 * descriptors. It favours the main fd over the secondary fd (sec_sfp).
 * Increments cop->info for each successful completion.
 */
static int
sg_mrq_complets(struct sg_mrq_hold *mhp, struct sg_fd *sfp,
		struct sg_fd *sec_sfp, int mreqs, int sec_reqs)
{
	int res = 0;
	int rres;
	struct sg_request *srp;
	struct sg_io_v4 *cop = mhp->cwrp->h4p;

	SG_LOG(3, sfp, "%s: mreqs=%d, sec_reqs=%d\n", __func__, mreqs,
	       sec_reqs);
	while (mreqs + sec_reqs > 0) {
		while (mreqs > 0 && sg_mrq_get_ready_srp(sfp, &srp)) {
			if (IS_ERR(srp)) {	/* -ENODATA: no mrqs here */
				if (PTR_ERR(srp) == -ENODATA)
					break;
				res = PTR_ERR(srp);
				break;
			}
			--mreqs;
			res = sg_mrq_1complet(mhp, sfp, srp);
			if (unlikely(res))
				return res;
			++cop->info;
			if (cop->din_xfer_len > 0)
				--cop->din_resid;
		}
		while (sec_reqs > 0 && sg_mrq_get_ready_srp(sec_sfp, &srp)) {
			if (IS_ERR(srp)) {
				if (PTR_ERR(srp) == -ENODATA)
					break;
				res = PTR_ERR(srp);
				break;
			}
			--sec_reqs;
			rres = sg_mrq_1complet(mhp, sec_sfp, srp);
			if (unlikely(rres))
				return rres;
			++cop->info;
			if (cop->din_xfer_len > 0)
				--cop->din_resid;
		}
		if (res)
			break;
		if (mreqs > 0) {
			res = sg_wait_mrq_event(sfp, &srp);
			if (unlikely(res))
				return res;	/* signal --> -ERESTARTSYS */
			if (IS_ERR(srp)) {
				mreqs = 0;
			} else {
				--mreqs;
				res = sg_mrq_1complet(mhp, sfp, srp);
				if (unlikely(res))
					return res;
				++cop->info;
				if (cop->din_xfer_len > 0)
					--cop->din_resid;
			}
		}
		if (sec_reqs > 0) {
			res = sg_wait_mrq_event(sec_sfp, &srp);
			if (unlikely(res))
				return res;	/* signal --> -ERESTARTSYS */
			if (IS_ERR(srp)) {
				sec_reqs = 0;
			} else {
				--sec_reqs;
				res = sg_mrq_1complet(mhp, sec_sfp, srp);
				if (unlikely(res))
					return res;
				++cop->info;
				if (cop->din_xfer_len > 0)
					--cop->din_resid;
			}
		}
	}	/* end of outer while loop (while requests still inflight) */
	return res;
}

static int
sg_mrq_sanity(struct sg_mrq_hold *mhp)
{
	bool last_is_keep_share = false;
	bool share, have_mrq_sense;
	int k;
	struct sg_io_v4 *cop = mhp->cwrp->h4p;
	u32 cdb_alen = cop->request_len;
	u32 cdb_mxlen = cdb_alen / mhp->tot_reqs;
	u32 flags;
	struct sg_fd *sfp = mhp->cwrp->sfp;
	struct sg_io_v4 *a_hds = mhp->a_hds;
	u8 *cdb_ap = mhp->cdb_ap;
	struct sg_io_v4 *hp;
	__maybe_unused const char *rip = "request index";

	have_mrq_sense = (cop->response && cop->max_response_len);
	/* Pre-check each request for anomalies, plus some preparation */
	for (k = 0, hp = a_hds; k < mhp->tot_reqs; ++k, ++hp) {
		flags = hp->flags;
		sg_v4h_partial_zero(hp);
		if (unlikely(hp->guard != 'Q' || hp->protocol != 0 ||
			     hp->subprotocol != 0)) {
			SG_LOG(1, sfp, "%s: req index %u: %s or protocol\n",
			       __func__, k, "bad guard");
			return -ERANGE;
		}
		last_is_keep_share = !!(flags & SGV4_FLAG_KEEP_SHARE);
		if (unlikely(flags & SGV4_FLAG_MULTIPLE_REQS)) {
			SG_LOG(1, sfp, "%s: %s %u: no nested multi-reqs\n",
			       __func__, rip, k);
			return -ERANGE;
		}
		share = !!(flags & SGV4_FLAG_SHARE);
		if (mhp->immed) {/* only accept async submits on current fd */
			if (unlikely(flags & SGV4_FLAG_DO_ON_OTHER)) {
				SG_LOG(1, sfp, "%s: %s %u, %s\n", __func__,
				       rip, k, "no IMMED with ON_OTHER");
				return -ERANGE;
			} else if (unlikely(share)) {
				SG_LOG(1, sfp, "%s: %s %u, %s\n", __func__,
				       rip, k, "no IMMED with FLAG_SHARE");
				return -ERANGE;
			} else if (unlikely(flags & SGV4_FLAG_COMPLETE_B4)) {
				SG_LOG(1, sfp, "%s: %s %u, %s\n", __func__,
				       rip, k, "no IMMED with COMPLETE_B4");
				return -ERANGE;
			}
		}
		if (mhp->co_mmap && (flags & SGV4_FLAG_MMAP_IO)) {
			SG_LOG(1, sfp, "%s: %s %u, MMAP in co AND here\n",
			       __func__, rip, k);
			return -ERANGE;
		}
		if (!sg_fd_is_shared(sfp)) {
			if (unlikely(share)) {
				SG_LOG(1, sfp, "%s: %s %u, no share\n",
				       __func__, rip, k);
				return -ERANGE;
			} else if (unlikely(flags & SGV4_FLAG_DO_ON_OTHER)) {
				SG_LOG(1, sfp, "%s: %s %u, %s do on\n",
				       __func__, rip, k, "no other fd to");
				return -ERANGE;
			}
		}
		if (cdb_ap) {
			if (unlikely(hp->request_len > cdb_mxlen)) {
				SG_LOG(1, sfp, "%s: %s %u, cdb too long\n",
				       __func__, rip, k);
				return -ERANGE;
			}
		}
		if (have_mrq_sense && hp->response == 0 &&
		    hp->max_response_len == 0) {
			hp->response = cop->response;
			hp->max_response_len = cop->max_response_len;
		}
	}
	if (last_is_keep_share) {
		SG_LOG(1, sfp,
		       "%s: Can't set SGV4_FLAG_KEEP_SHARE on last mrq req\n",
		       __func__);
		return -ERANGE;
	}
	return 0;
}

/*
 * Read operation (din) must precede any write (dout) operations and a din
 * operation can't be last (data transferring) operations. Non data
 * transferring operations can appear anywhere. Data transferring operations
 * must have SGV4_FLAG_SHARE set. Dout operations must additionally have
 * SGV4_FLAG_NO_DXFER and SGV4_FLAG_DO_ON_OTHER set. Din operations must
 * not set SGV4_FLAG_DO_ON_OTHER.
 */
static bool
sg_mrq_svb_chk(struct sg_io_v4 *a_hds, u32 tot_reqs)
{
	bool last_rd = false;
	bool seen_wr = false;
	int k;
	u32 flags;
	struct sg_io_v4 *hp;

	/* expect read-write pairs, all with SGV4_FLAG_NO_DXFER set */
	for (k = 0, hp = a_hds; k < tot_reqs; ++k, ++hp) {
		flags = hp->flags;
		if (flags & SGV4_FLAG_COMPLETE_B4)
			return false;
		if (!seen_wr) {
			if (hp->dout_xfer_len > 0)
				return false;
			if (hp->din_xfer_len > 0) {
				if (!(flags & SGV4_FLAG_SHARE))
					return false;
				if (flags & SGV4_FLAG_DO_ON_OTHER)
					return false;
				seen_wr = true;
				last_rd = true;
			}
			/* allowing commands with no dxfer */
		} else {	/* checking write side */
			if (hp->dout_xfer_len > 0) {
				if (~flags &
				    (SGV4_FLAG_NO_DXFER | SGV4_FLAG_SHARE |
				     SGV4_FLAG_DO_ON_OTHER))
					return false;
				last_rd = false;
			}
			if (hp->din_xfer_len > 0) {
				if (!(flags & SGV4_FLAG_SHARE))
					return false;
				if (flags & SGV4_FLAG_DO_ON_OTHER)
					return false;
				last_rd = true;
			}
		}
	}
	return !last_rd;
}

static struct sg_request *
sg_mrq_submit(struct sg_fd *rq_sfp, struct sg_mrq_hold *mhp, int pos_hdr,
	      int rsv_idx, bool keep_share)
{
	unsigned long ul_timeout;
	struct sg_comm_wr_t r_cwr;
	struct sg_comm_wr_t *r_cwrp = &r_cwr;
	struct sg_io_v4 *hp = mhp->a_hds + pos_hdr;

	sg_comm_wr_init(r_cwrp);
	if (mhp->cdb_ap)	/* already have array of cdbs */
		r_cwrp->cmdp = mhp->cdb_ap + (pos_hdr * mhp->cdb_mxlen);
	else			/* fetch each cdb from user space */
		r_cwrp->u_cmdp = cuptr64(hp->request);
	r_cwrp->cmd_len = hp->request_len;
	r_cwrp->rsv_idx = rsv_idx;
	ul_timeout = msecs_to_jiffies(hp->timeout);
	__assign_bit(SG_FRQ_SYNC_INVOC, r_cwrp->frq_bm,
		     (int)mhp->blocking);
	__set_bit(SG_FRQ_IS_V4I, r_cwrp->frq_bm);
	r_cwrp->h4p = hp;
	r_cwrp->dlen = hp->din_xfer_len ? hp->din_xfer_len : hp->dout_xfer_len;
	r_cwrp->timeout = min_t(unsigned long, ul_timeout, INT_MAX);
	if (hp->flags & SGV4_FLAG_DOUT_OFFSET)
		r_cwrp->wr_offset = hp->spare_in;
	r_cwrp->sfp = rq_sfp;
	r_cwrp->keep_share = keep_share;
	return sg_common_write(r_cwrp);
}

/*
 * Processes most mrq requests apart from those from "shared variable
 * blocking" (svb) method which is processed in sg_process_svb_mrq().
 */
static int
sg_process_most_mrq(struct sg_fd *fp, struct sg_fd *o_sfp,
		    struct sg_mrq_hold *mhp)
{
	int flags, j;
	int num_subm = 0;
	int num_cmpl = 0;
	int res = 0;
	int other_fp_sent = 0;
	int this_fp_sent = 0;
	const int shr_complet_b4 = SGV4_FLAG_SHARE | SGV4_FLAG_COMPLETE_B4;
	struct sg_fd *rq_sfp;
	struct sg_io_v4 *cop = mhp->cwrp->h4p;
	struct sg_io_v4 *hp;		/* ptr to request object in a_hds */
	struct sg_request *srp;

	SG_LOG(3, fp, "%s: id_of_mrq=%d, tot_reqs=%d, enter\n", __func__,
	       mhp->id_of_mrq, mhp->tot_reqs);
	/* Dispatch (submit) requests and optionally wait for response */
	for (hp = mhp->a_hds, j = 0; num_subm < mhp->tot_reqs; ++hp, ++j) {
		if (mhp->chk_abort && test_and_clear_bit(SG_FFD_MRQ_ABORT,
							 fp->ffd_bm)) {
			SG_LOG(1, fp, "%s: id_of_mrq=%d aborting at ind=%d\n",
			       __func__, mhp->id_of_mrq, num_subm);
			break;	/* N.B. rest not submitted */
		}
		flags = hp->flags;
		rq_sfp = (flags & SGV4_FLAG_DO_ON_OTHER) ? o_sfp : fp;
		srp = sg_mrq_submit(rq_sfp, mhp, j, -1, false);
		if (IS_ERR(srp)) {
			mhp->s_res = PTR_ERR(srp);
			break;
		}
		srp->s_hdr4.mrq_ind = num_subm++;
		if (mhp->chk_abort)
			atomic_set(&srp->s_hdr4.pack_id_of_mrq,
				   mhp->id_of_mrq);
		if (mhp->immed ||
		    (!(mhp->blocking || (flags & shr_complet_b4)))) {
			if (fp == rq_sfp)
				++this_fp_sent;
			else
				++other_fp_sent;
			continue;  /* defer completion until all submitted */
		}
		mhp->s_res = sg_wait_event_srp(rq_sfp, NULL, hp, srp);
		if (unlikely(mhp->s_res)) {
			if (mhp->s_res == -ERESTARTSYS)
				return mhp->s_res;
			break;
		}
		++num_cmpl;
		hp->info |= SG_INFO_MRQ_FINI;
		if (mhp->stop_if && !sg_result_is_good(srp->rq_result)) {
			SG_LOG(2, fp, "%s: %s=0x%x/0x%x/0x%x] cause exit\n",
			       __func__, "STOP_IF and status [drv/tran/scsi",
			       hp->driver_status, hp->transport_status,
			       hp->device_status);
			break;	/* cop->driver_status <-- 0 in this case */
		}
		if (mhp->co_mmap) {
			sg_sgat_cp_into(mhp->co_mmap_sgatp, j * SZ_SG_IO_V4,
					(const u8 *)hp, SZ_SG_IO_V4);
			if (rq_sfp->async_qp && (hp->flags & SGV4_FLAG_SIGNAL))
				kill_fasync(&rq_sfp->async_qp, SIGPOLL,
					    POLL_IN);
			if (rq_sfp->efd_ctxp &&
			    (srp->rq_flags & SGV4_FLAG_EVENTFD)) {
				u64 n = eventfd_signal(rq_sfp->efd_ctxp, 1);

				if (n != 1)
					pr_info("%s: eventfd_signal prob\n",
						__func__);
			}
		} else if (rq_sfp->async_qp &&
			   (hp->flags & SGV4_FLAG_SIGNAL)) {
			res = sg_mrq_arr_flush(mhp);
			if (unlikely(res))
				break;
			kill_fasync(&rq_sfp->async_qp, SIGPOLL, POLL_IN);
		}
	}	/* end of dispatch request and optionally wait response loop */
	cop->dout_resid = mhp->tot_reqs - num_subm;
	cop->info = mhp->immed ? num_subm : num_cmpl;
	if (cop->din_xfer_len > 0) {
		cop->din_resid = mhp->tot_reqs - num_cmpl;
		cop->spare_out = -mhp->s_res;
	}

	if (mhp->immed)
		return res;
	if (likely(res == 0 && (this_fp_sent + other_fp_sent) > 0)) {
		mhp->s_res = sg_mrq_complets(mhp, fp, o_sfp, this_fp_sent,
					     other_fp_sent);
		if (unlikely(mhp->s_res == -EFAULT ||
			     mhp->s_res == -ERESTARTSYS))
			res = mhp->s_res;	/* this may leave orphans */
	}
	if (mhp->id_of_mrq)	/* can no longer do a mrq abort */
		atomic_set(&fp->mrq_id_abort, 0);
	return res;
}

static int
sg_find_srp_idx(struct sg_fd *sfp, const struct sg_request *srp)
{
	int k;
	struct sg_request **rapp = sfp->rsv_arr;

	for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
		if (*rapp == srp)
			return k;
	}
	return -1;
}

/*
 * Processes shared variable blocking. First inner loop submits a chunk of
 * requests (some read-side, some non-data) but defers any write-side requests. The
 * second inner loop processes the completions from the first inner loop, plus
 * for any completed read-side request it submits the paired write-side request. The
 * second inner loop also waits for the completions of those write-side requests.
 * The outer loop then moves onto the next chunk, working its way through
 * the multiple requests. The user sees a blocking command, but the chunks
 * are run in parallel apart from read-write ordering requirement.
 * N.B. Only one svb mrq permitted per file descriptor at a time.
 */
static int
sg_process_svb_mrq(struct sg_fd *fp, struct sg_fd *o_sfp,
		   struct sg_mrq_hold *mhp)
{
	bool aborted = false;
	bool chk_oth_first, keep_share;
	int k, j, i, m, rcv_before, idx, ws_pos, sent;
	int this_fp_sent, other_fp_sent;
	int num_subm = 0;
	int num_cmpl = 0;
	int res = 0;
	struct sg_fd *rq_sfp;
	struct sg_io_v4 *cop = mhp->cwrp->h4p;
	struct sg_io_v4 *hp;		/* ptr to request object in a_hds */
	struct sg_request *srp;
	struct sg_request *rs_srp;
	struct sg_io_v4 *a_hds = mhp->a_hds;
	int ws_pos_a[SG_MAX_RSV_REQS];	/* write-side hdr pos within a_hds */
	struct sg_request *rs_srp_a[SG_MAX_RSV_REQS];

	SG_LOG(3, fp, "%s: id_of_mrq=%d, tot_reqs=%d, enter\n", __func__,
	       mhp->id_of_mrq, mhp->tot_reqs);

	/* work through mrq array, SG_MAX_RSV_REQS read-side requests at a time */
	for (hp = a_hds, j = 0; j < mhp->tot_reqs; ) {
		this_fp_sent = 0;
		other_fp_sent = 0;
		chk_oth_first = false;
		for (k = 0; k < SG_MAX_RSV_REQS && j < mhp->tot_reqs;
		     ++hp, ++j) {
			if (mhp->chk_abort &&
			    test_and_clear_bit(SG_FFD_MRQ_ABORT, fp->ffd_bm)) {
				SG_LOG(1, fp,
				       "%s: id_of_mrq=%d aborting at pos=%d\n",
				       __func__, mhp->id_of_mrq, num_subm);
				aborted = true;
				/*
				 * after mrq abort detected, complete those
				 * already submitted, but don't submit any more
				 */
			}
			if (aborted)
				break;
			if (hp->flags & SGV4_FLAG_DO_ON_OTHER) {
				if (hp->dout_xfer_len > 0) {
					/* need to await read-side completion */
					ws_pos_a[k] = j;
					++k;
					continue;  /* deferred to next loop */
				}
				chk_oth_first = true;
				SG_LOG(6, o_sfp,
				       "%s: subm-nodat p_id=%d on write-side\n",
				       __func__, (int)hp->request_extra);
				rq_sfp = o_sfp;
			} else {
				SG_LOG(6, fp, "%s: submit p_id=%d on read-side\n",
				       __func__, (int)hp->request_extra);
				rq_sfp = fp;
			}
			srp = sg_mrq_submit(rq_sfp, mhp, j, -1, false);
			if (IS_ERR(srp)) {
				mhp->s_res = PTR_ERR(srp);
				res = mhp->s_res;	/* don't loop again */
				SG_LOG(1, rq_sfp, "%s: mrq_submit()->%d\n",
				       __func__, res);
				break;
			}
			num_subm++;
			if (hp->din_xfer_len > 0)
				rs_srp_a[k] = srp;
			srp->s_hdr4.mrq_ind = j;
			if (mhp->chk_abort)
				atomic_set(&srp->s_hdr4.pack_id_of_mrq,
					   mhp->id_of_mrq);
			if (fp == rq_sfp)
				++this_fp_sent;
			else
				++other_fp_sent;
		}
		sent = this_fp_sent + other_fp_sent;
		if (sent <= 0)
			break;
		/*
		 * We have just submitted a fixed number read-side reqs and any
		 * others (that don't move data). Now we pick up their
		 * responses. Any responses that were read-side requests have
		 * their paired write-side submitted. Finally we wait for those
		 * paired write-side to complete.
		 */
		rcv_before = cop->info;
		for (i = 0; i < sent; ++i) {	/* now process responses */
			if (other_fp_sent > 0 &&
			    sg_mrq_get_ready_srp(o_sfp, &srp)) {
other_found:
				if (IS_ERR(srp)) {
					res = PTR_ERR(srp);
					break;
				}
				--other_fp_sent;
				res = sg_mrq_1complet(mhp, o_sfp, srp);
				if (unlikely(res))
					return res;
				++cop->info;
				if (cop->din_xfer_len > 0)
					--cop->din_resid;
				continue;  /* do available submits first */
			}
			if (this_fp_sent > 0 &&
			    sg_mrq_get_ready_srp(fp, &srp)) {
this_found:
				if (IS_ERR(srp)) {
					res = PTR_ERR(srp);
					break;
				}
				--this_fp_sent;
				res = sg_mrq_1complet(mhp, fp, srp);
				if (unlikely(res))
					return res;
				++cop->info;
				if (cop->din_xfer_len > 0)
					--cop->din_resid;
				if (srp->s_hdr4.dir != SG_DXFER_FROM_DEV)
					continue;
				if (test_bit(SG_FFD_READ_SIDE_ERR, fp->ffd_bm))
					continue;
				/* read-side req completed, submit its write-side */
				rs_srp = srp;
				for (m = 0; m < k; ++m) {
					if (rs_srp == rs_srp_a[m])
						break;
				}
				if (m >= k) {
					SG_LOG(1, rs_srp->parentfp,
					       "%s: m >= %d, pack_id=%d\n",
					       __func__, k, rs_srp->pack_id);
					res = -EPROTO;
					break;
				}
				ws_pos = ws_pos_a[m];
				idx = sg_find_srp_idx(fp, rs_srp);
				if (idx < 0) {
					SG_LOG(1, rs_srp->parentfp,
					       "%s: idx < 0\n", __func__);
					res = -EPROTO;
					break;
				}
				keep_share = false;
another_dout:
				SG_LOG(6, o_sfp,
				       "%s: submit ws_pos=%d, rs_idx=%d\n",
				       __func__, ws_pos, idx);
				srp = sg_mrq_submit(o_sfp, mhp, ws_pos, idx,
						    keep_share);
				if (IS_ERR(srp)) {
					mhp->s_res = PTR_ERR(srp);
					res = mhp->s_res;
					SG_LOG(1, o_sfp,
					       "%s: mrq_submit(oth)->%d\n",
						__func__, res);
					break;
				}
				++num_subm;
				++other_fp_sent;
				++sent;
				srp->s_hdr4.mrq_ind = ws_pos;
				if (srp->rq_flags & SGV4_FLAG_KEEP_SHARE) {
					++ws_pos;  /* next for same read-side */
					keep_share = true;
					goto another_dout;
				}
				if (mhp->chk_abort)
					atomic_set(&srp->s_hdr4.pack_id_of_mrq,
						   mhp->id_of_mrq);
				continue;  /* do available submits first */
			}
			/* waits maybe interrupted by signals (-ERESTARTSYS) */
			if (chk_oth_first)
				goto oth_first;
this_second:
			if (this_fp_sent > 0) {
				res = sg_wait_mrq_event(fp, &srp);
				if (unlikely(res))
					return res;
				goto this_found;
			}
			if (chk_oth_first)
				continue;
oth_first:
			if (other_fp_sent > 0) {
				res = sg_wait_mrq_event(o_sfp, &srp);
				if (unlikely(res))
					return res;
				goto other_found;
			}
			if (chk_oth_first)
				goto this_second;
		}	/* end of response/write_side_submit/write_side_response loop */
		if (unlikely(mhp->s_res == -EFAULT ||
			     mhp->s_res == -ERESTARTSYS))
			res = mhp->s_res;	/* this may leave orphans */
		num_cmpl += (cop->info - rcv_before);
		if (res)
			break;
		if (aborted)
			break;
	}	/* end of outer for loop */

	cop->dout_resid = mhp->tot_reqs - num_subm;
	if (cop->din_xfer_len > 0) {
		cop->din_resid = mhp->tot_reqs - num_cmpl;
		cop->spare_out = -mhp->s_res;
	}
	if (mhp->id_of_mrq)	/* can no longer do a mrq abort */
		atomic_set(&fp->mrq_id_abort, 0);
	return res;
}

#if IS_ENABLED(SG_LOG_ACTIVE)
static const char *
sg_mrq_name(bool blocking, u32 flags)
{
	if (!(flags & SGV4_FLAG_MULTIPLE_REQS))
		return "_not_ multiple requests control object";
	if (blocking)
		return "ordered blocking";
	if (flags & SGV4_FLAG_IMMED)
		return "submit or full non-blocking";
	if (flags & SGV4_FLAG_SHARE)
		return "shared variable blocking";
	return "variable blocking";
}
#endif

/*
 * Implements the multiple request functionality. When 'blocking' is true
 * invocation was via ioctl(SG_IO), otherwise it was via ioctl(SG_IOSUBMIT).
 * Submit non-blocking if IMMED flag given or when ioctl(SG_IOSUBMIT)
 * is used with O_NONBLOCK set on its file descriptor. Hipri non-blocking
 * is when the HIPRI flag is given.
 */
static int
sg_do_multi_req(struct sg_comm_wr_t *cwrp, bool blocking)
{
	bool f_non_block, co_share;
	int res = 0;
	int existing_id;
	u32 cdb_mxlen;
	struct sg_io_v4 *cop = cwrp->h4p;	/* controlling object */
	u32 dout_len = cop->dout_xfer_len;
	u32 din_len = cwrp->dlen;
	u32 cdb_alen = cop->request_len;
	u32 tot_reqs = dout_len / SZ_SG_IO_V4;
	u8 *cdb_ap = NULL;
	struct sg_io_v4 *a_hds;		/* array of request objects */
	struct sg_fd *fp = cwrp->sfp;
	struct sg_fd *o_sfp = sg_fd_share_ptr(fp);
	struct sg_device *sdp = fp->parentdp;
	struct sg_mrq_hold mh;
	struct sg_mrq_hold *mhp = &mh;
#if IS_ENABLED(SG_LOG_ACTIVE)
	const char *mrq_name;
#endif

	mhp->cwrp = cwrp;
	mhp->blocking = blocking;
#if IS_ENABLED(SG_LOG_ACTIVE)
	mrq_name = sg_mrq_name(blocking, cop->flags);
#endif
	f_non_block = !!(fp->filp->f_flags & O_NONBLOCK);
	co_share = !!(cop->flags & SGV4_FLAG_SHARE);
	mhp->immed = !!(cop->flags & SGV4_FLAG_IMMED);
	mhp->stop_if = !!(cop->flags & SGV4_FLAG_STOP_IF);
	mhp->co_mmap = !!(cop->flags & SGV4_FLAG_MMAP_IO);
	if (mhp->co_mmap)
		mhp->co_mmap_sgatp = fp->rsv_arr[0]->sgatp;
	mhp->id_of_mrq = (int)cop->request_extra;
	mhp->tot_reqs = tot_reqs;
	mhp->s_res = 0;
	if (mhp->id_of_mrq) {
		existing_id = atomic_cmpxchg(&fp->mrq_id_abort, 0,
					     mhp->id_of_mrq);
		if (existing_id && existing_id != mhp->id_of_mrq) {
			SG_LOG(1, fp, "%s: existing id=%d id_of_mrq=%d\n",
			       __func__, existing_id, mhp->id_of_mrq);
			return -EDOM;
		}
		clear_bit(SG_FFD_MRQ_ABORT, fp->ffd_bm);
		mhp->chk_abort = true;
	} else {
		mhp->chk_abort = false;
	}
	if (blocking) {		/* came from ioctl(SG_IO) */
		if (unlikely(mhp->immed)) {
			SG_LOG(1, fp, "%s: ioctl(SG_IO) %s contradicts\n",
			       __func__, "with SGV4_FLAG_IMMED");
			return -ERANGE;
		}
		if (unlikely(co_share)) {
			SG_LOG(1, fp, "%s: ioctl(SG_IO) %s contradicts\n",
			       __func__, "with SGV4_FLAG_SHARE");
			return -ERANGE;
		}
		if (unlikely(f_non_block)) {
			SG_LOG(6, fp, "%s: ioctl(SG_IO) %s O_NONBLOCK\n",
			       __func__, "ignoring");
			f_non_block = false;
		}
	}
	if (!mhp->immed && f_non_block)
		mhp->immed = true;
	SG_LOG(3, fp, "%s: %s, tot_reqs=%u, id_of_mrq=%d\n", __func__,
	       mrq_name, tot_reqs, mhp->id_of_mrq);
	sg_v4h_partial_zero(cop);

	if (mhp->co_mmap) {
		struct sg_request *srp = fp->rsv_arr[0];

		if (unlikely(fp->mmap_sz == 0))
			return -EBADFD;	/* want mmap() active on fd */
		if ((int)din_len > fp->mmap_sz)
			return  -E2BIG;
		if (cop->din_xferp)
			pr_info_once("%s: co::din_xferp ignored due to SGV4_FLAG_MMAP_IO\n",
				     __func__);
		if (srp)
			sg_sgat_zero(srp->sgatp, 0 /* offset */, fp->mmap_sz);
		else
			return -EPROTO;
	}
	if (unlikely(tot_reqs > U16_MAX)) {
		return -ERANGE;
	} else if (unlikely(dout_len > SG_MAX_MULTI_REQ_SZ ||
			    din_len > SG_MAX_MULTI_REQ_SZ ||
			    cdb_alen > SG_MAX_MULTI_REQ_SZ)) {
		return  -E2BIG;
	} else if (unlikely(mhp->immed && mhp->stop_if)) {
		return -ERANGE;
	} else if (unlikely(tot_reqs == 0)) {
		return 0;
	} else if (unlikely(!!cdb_alen != !!cop->request)) {
		return -ERANGE;	/* both must be zero or both non-zero */
	} else if (cdb_alen) {
		if (unlikely(cdb_alen % tot_reqs))
			return -ERANGE;
		cdb_mxlen = cdb_alen / tot_reqs;
		if (unlikely(cdb_mxlen < 6))
			return -ERANGE;	/* too short for SCSI cdbs */
	} else {
		cdb_mxlen = 0;
	}

	if (SG_IS_DETACHING(sdp) || (o_sfp && SG_IS_DETACHING(o_sfp->parentdp)))
		return -ENODEV;

	a_hds = kcalloc(tot_reqs, SZ_SG_IO_V4, GFP_KERNEL | __GFP_NOWARN);
	if (unlikely(!a_hds))
		return -ENOMEM;
	if (copy_from_user(a_hds, cuptr64(cop->dout_xferp),
			   tot_reqs * SZ_SG_IO_V4)) {
		res = -EFAULT;
		goto fini;
	}
	if (cdb_alen > 0) {
		cdb_ap = kzalloc(cdb_alen, GFP_KERNEL | __GFP_NOWARN);
		if (unlikely(!cdb_ap)) {
			res = -ENOMEM;
			goto fini;
		}
		if (copy_from_user(cdb_ap, cuptr64(cop->request), cdb_alen)) {
			res = -EFAULT;
			goto fini;
		}
	}
	mhp->cdb_ap = cdb_ap;
	mhp->a_hds = a_hds;
	mhp->cdb_mxlen = cdb_mxlen;
	/* do sanity checks on all requests before starting */
	res = sg_mrq_sanity(mhp);
	if (unlikely(res))
		goto fini;

	/* override cmd queuing setting to allow */
	clear_bit(SG_FFD_NO_CMD_Q, fp->ffd_bm);
	if (o_sfp)
		clear_bit(SG_FFD_NO_CMD_Q, o_sfp->ffd_bm);

	if (co_share) {
		bool ok;

		/* check for 'shared' variable blocking (svb) */
		ok = sg_mrq_svb_chk(a_hds, tot_reqs);
		if (!ok) {
			SG_LOG(1, fp, "%s: %s failed on req(s)\n", __func__,
			       mrq_name);
			res = -ERANGE;
			goto fini;
		}
		if (test_and_set_bit(SG_FFD_SVB_ACTIVE, fp->ffd_bm)) {
			SG_LOG(1, fp, "%s: %s already active\n", __func__,
			       mrq_name);
			res = -EBUSY;
			goto fini;
		}
		res = sg_process_svb_mrq(fp, o_sfp, mhp);
		clear_bit(SG_FFD_SVB_ACTIVE, fp->ffd_bm);
	} else {
		res = sg_process_most_mrq(fp, o_sfp, mhp);
	}
fini:
	if (likely(res == 0) && !mhp->immed)
		res = sg_mrq_arr_flush(mhp);
	kfree(cdb_ap);
	kfree(a_hds);
	return res;
}

static int
sg_submit_v4(struct sg_fd *sfp, void __user *p, struct sg_io_v4 *h4p,
	     bool sync, struct sg_request **o_srp)
{
	int res = 0;
	int dlen;
	unsigned long ul_timeout;
	struct sg_request *srp;
	struct sg_comm_wr_t cwr;

	sg_comm_wr_init(&cwr);
	dlen = h4p->din_xfer_len ? h4p->din_xfer_len : h4p->dout_xfer_len;
	cwr.dlen = dlen;
	if (h4p->flags & SGV4_FLAG_MULTIPLE_REQS) {
		/* want v4 async or sync with guard, din and dout and flags */
		if (!h4p->dout_xferp || h4p->din_iovec_count ||
		    h4p->dout_iovec_count ||
		    (h4p->dout_xfer_len % SZ_SG_IO_V4))
			return -ERANGE;
		if (o_srp)
			*o_srp = NULL;
		cwr.sfp = sfp;
		cwr.h4p = h4p;
		res = sg_do_multi_req(&cwr, sync);
		if (unlikely(res))
			return res;
		if (likely(p)) {
			/* Write back sg_io_v4 object for error/warning info */
			if (copy_to_user(p, h4p, SZ_SG_IO_V4))
				return -EFAULT;
		}
		return 0;
	}
	if (h4p->flags & SG_FLAG_MMAP_IO) {
		res = sg_chk_mmap(sfp, h4p->flags, dlen);
		if (unlikely(res))
			return res;
	}
	/* once v4 (or v3) seen, allow cmd_q on this fd (def: no cmd_q) */
	if (test_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm))
		clear_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm);
	ul_timeout = msecs_to_jiffies(h4p->timeout);
	cwr.sfp = sfp;
	__assign_bit(SG_FRQ_SYNC_INVOC, cwr.frq_bm, (int)sync);
	__set_bit(SG_FRQ_IS_V4I, cwr.frq_bm);
	cwr.h4p = h4p;
	cwr.timeout = min_t(unsigned long, ul_timeout, INT_MAX);
	cwr.cmd_len = h4p->request_len;
	if (h4p->flags & SGV4_FLAG_DOUT_OFFSET)
		cwr.wr_offset = h4p->spare_in;
	cwr.u_cmdp = cuptr64(h4p->request);
	srp = sg_common_write(&cwr);
	if (IS_ERR(srp))
		return PTR_ERR(srp);
	if (o_srp)
		*o_srp = srp;
	if (p && !sync && (srp->rq_flags & SGV4_FLAG_YIELD_TAG)) {
		u64 gen_tag = srp->tag;
		struct sg_io_v4 __user *h4_up = (struct sg_io_v4 __user *)p;

		if (copy_to_user(&h4_up->generated_tag, &gen_tag,
				 sizeof(gen_tag)))
			return -EFAULT;
	}
	return res;
}

static int
sg_ctl_iosubmit(struct sg_fd *sfp, void __user *p)
{
	int res;
	struct sg_io_v4 h4;
	struct sg_io_v4 *h4p = &h4;
	struct sg_device *sdp = sfp->parentdp;

	res = sg_allow_if_err_recovery(sdp, SG_IS_O_NONBLOCK(sfp));
	if (unlikely(res))
		return res;
	if (copy_from_user(h4p, p, SZ_SG_IO_V4))
		return -EFAULT;
	if (likely(h4p->guard == 'Q'))
		return sg_submit_v4(sfp, p, h4p, false, NULL);
	return -EPERM;
}

static int
sg_ctl_iosubmit_v3(struct sg_fd *sfp, void __user *p)
{
	int res;
	struct sg_io_hdr h3;
	struct sg_io_hdr *h3p = &h3;
	struct sg_device *sdp = sfp->parentdp;

	res = sg_allow_if_err_recovery(sdp, SG_IS_O_NONBLOCK(sfp));
	if (unlikely(res))
		return res;
	if (copy_from_user(h3p, p, SZ_SG_IO_HDR))
		return -EFAULT;
	if (likely(h3p->interface_id == 'S'))
		return sg_submit_v3(sfp, h3p, false, NULL);
	return -EPERM;
}

/*
 * Assumes sharing has been established at the file descriptor level and now we
 * check the rq_flags of a new request/command. SGV4_FLAG_NO_DXFER may or may
 * not be used on the read-side, it must be used on the write-side. Also
 * returns (via *sh_varp) the proposed sg_request::sh_var of the new request
 * yet to be built/re-used.
 */
static int
sg_share_chk_flags(struct sg_fd *sfp, u32 rq_flags, int dxfer_len, int dir,
		   enum sg_shr_var *sh_varp)
{
	bool is_read_side = xa_get_mark(&sfp->parentdp->sfp_arr, sfp->idx,
					SG_XA_FD_RS_SHARE);
	int result = 0;
	enum sg_shr_var sh_var = SG_SHR_NONE;

	if (rq_flags & SGV4_FLAG_SHARE) {
		if (unlikely(rq_flags & SG_FLAG_DIRECT_IO)) {
			result = -EINVAL; /* since no control of data buffer */
		} else if (unlikely(dxfer_len < 1)) {
			sh_var = is_read_side ? SG_SHR_RS_NOT_SRQ :
						SG_SHR_WS_NOT_SRQ;
		} else if (is_read_side) {
			sh_var = SG_SHR_RS_RQ;
			if (unlikely(dir != SG_DXFER_FROM_DEV))
				result = -ENOMSG;
			if (rq_flags & SGV4_FLAG_NO_DXFER) {
				/* rule out some contradictions */
				if (unlikely(rq_flags & SG_FL_MMAP_DIRECT))
					result = -ENODATA;
			}
		} else {
			sh_var = SG_SHR_WS_RQ;
			if (unlikely(dir != SG_DXFER_TO_DEV))
				result = -ENOMSG;
			if (unlikely(!(rq_flags & SGV4_FLAG_NO_DXFER)))
				result = -ENOMSG;
			if (unlikely(rq_flags & SG_FL_MMAP_DIRECT))
				result = -ENODATA;
		}
	} else if (is_read_side) {
		sh_var = SG_SHR_RS_NOT_SRQ;
	} else {
		sh_var = SG_SHR_WS_NOT_SRQ;
	}
	*sh_varp = sh_var;
	return result;
}

#if IS_ENABLED(SG_LOG_ACTIVE)
static void
sg_rq_state_fail_msg(struct sg_fd *sfp, enum sg_rq_state exp_old_st,
		     enum sg_rq_state want_st, const char *fromp)
{
	const char *eaw_rs = "expected_old,wanted rq_st";

	if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
		SG_LOG(1, sfp, "%s: %s: %s,%s,%s\n",
		       __func__, fromp, eaw_rs,
		       sg_rq_st_str(exp_old_st, false),
		       sg_rq_st_str(want_st, false));
	else
		pr_info("sg: %s: %s: %s: %d,%d\n", __func__, fromp, eaw_rs,
			(int)exp_old_st, (int)want_st);
}
#endif

/* Functions ending in '_ulck' assume sfp->xa_lock held by caller. */
static void
sg_rq_chg_state_force_ulck(struct sg_request *srp, enum sg_rq_state new_st)
{
	bool prev, want;
	struct sg_fd *sfp = srp->parentfp;
	struct xarray *xafp = &sfp->srp_arr;

	atomic_set(&srp->rq_st, new_st);
	want = (new_st == SG_RQ_AWAIT_RCV);
	prev = xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	if (prev != want) {
		if (want)
			__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
		else
			__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	}
	want = (new_st == SG_RQ_INACTIVE);
	prev = xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
	if (prev != want) {
		if (want) {
			int prev_idx = READ_ONCE(sfp->low_used_idx);

			if (prev_idx < 0 || srp->rq_idx < prev_idx ||
			    !xa_get_mark(xafp, prev_idx, SG_XA_RQ_INACTIVE))
				WRITE_ONCE(sfp->low_used_idx, srp->rq_idx);
			__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
		} else {
			__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
		}
	}
}

static void
sg_rq_chg_state_force(struct sg_request *srp, enum sg_rq_state new_st)
{
	unsigned long iflags;
	struct xarray *xafp = &srp->parentfp->srp_arr;

	xa_lock_irqsave(xafp, iflags);
	sg_rq_chg_state_force_ulck(srp, new_st);
	xa_unlock_irqrestore(xafp, iflags);
}

static inline void
sg_rq_chg_state_help(struct xarray *xafp, struct sg_request *srp, int indic)
{
	if (indic & 1)		/* from inactive state */
		__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);
	else if (indic & 2)	/* to inactive state */
		__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE);

	if (indic & 4)		/* from await state */
		__xa_clear_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
	else if (indic & 8)	/* to await state */
		__xa_set_mark(xafp, srp->rq_idx, SG_XA_RQ_AWAIT);
}

/* Following array indexed by enum sg_rq_state, 0 means no xa mark change */
static const int sg_rq_state_arr[] = {1, 0, 4, 0, 0, 0};
static const int sg_rq_state_mul2arr[] = {2, 0, 8, 0, 0, 0};

/*
 * This function keeps the srp->rq_st state and associated marks on the
 * owning xarray's element in sync. An attempt si made to change state with
 * a call to atomic_cmpxchg(). If the actual srp->rq_st is not old_st, then
 * -EPROTOTYPE is returned. If the actual srp->rq_st is old_st then it is
 * replaced by new_st and the xarray marks are setup accordingly and 0 is
 * returned. This assumes srp_arr xarray spinlock is held.
 */
static int
sg_rq_chg_state_ulck(struct sg_request *srp, enum sg_rq_state old_st,
		     enum sg_rq_state new_st)
{
	enum sg_rq_state act_old_st =
			(enum sg_rq_state)atomic_cmpxchg_relaxed(&srp->rq_st, old_st, new_st);
	int indic = sg_rq_state_arr[(int)old_st] + sg_rq_state_mul2arr[(int)new_st];

	if (unlikely(act_old_st != old_st)) {
#if IS_ENABLED(SG_LOG_ACTIVE)
		SG_LOG(1, srp->parentfp, "%s: unexpected old state: %s\n",
		       __func__, sg_rq_st_str(act_old_st, false));
#endif
		return -EPROTOTYPE;	/* only used for this error type */
	}
	if (indic) {
		struct sg_fd *sfp = srp->parentfp;

		if (new_st == SG_RQ_INACTIVE) {
			int prev_idx = READ_ONCE(sfp->low_used_idx);
			struct xarray *xafp = &sfp->srp_arr;

			if (prev_idx < 0 || srp->rq_idx < prev_idx ||
			    !xa_get_mark(xafp, prev_idx, SG_XA_RQ_INACTIVE))
				WRITE_ONCE(sfp->low_used_idx, srp->rq_idx);
		}
		sg_rq_chg_state_help(&sfp->srp_arr, srp, indic);
	}
	return 0;
}

/* Similar to sg_rq_chg_state_ulck() but uses the xarray spinlock */
static int
sg_rq_chg_state(struct sg_request *srp, enum sg_rq_state old_st,
		enum sg_rq_state new_st)
{
	enum sg_rq_state act_old_st;
	int indic = sg_rq_state_arr[(int)old_st] + sg_rq_state_mul2arr[(int)new_st];
	struct sg_fd *sfp = srp->parentfp;

	if (indic) {
		unsigned long iflags;
		struct xarray *xafp = &sfp->srp_arr;

		xa_lock_irqsave(xafp, iflags);
		act_old_st = (enum sg_rq_state)atomic_cmpxchg_relaxed(&srp->rq_st, old_st, new_st);
		if (unlikely(act_old_st != old_st)) {
			xa_unlock_irqrestore(xafp, iflags);
			SG_LOG(1, sfp, "%s: unexpected old state: %s\n", __func__,
			       sg_rq_st_str(act_old_st, false));
			return -EPROTOTYPE;     /* only used for this error type */
		}
		if (new_st == SG_RQ_INACTIVE) {
			int prev_idx = READ_ONCE(sfp->low_used_idx);

			if (prev_idx < 0 || srp->rq_idx < prev_idx ||
			    !xa_get_mark(xafp, prev_idx, SG_XA_RQ_INACTIVE))
				WRITE_ONCE(sfp->low_used_idx, srp->rq_idx);
		}
		sg_rq_chg_state_help(xafp, srp, indic);
		xa_unlock_irqrestore(xafp, iflags);
	} else {
		act_old_st = (enum sg_rq_state)atomic_cmpxchg(&srp->rq_st, old_st, new_st);
		if (unlikely(act_old_st != old_st)) {
			SG_LOG(1, sfp, "%s: unexpected old state: %s\n", __func__,
			       sg_rq_st_str(act_old_st, false));
			return -EPROTOTYPE;     /* only used for this error type */
		}
	}
	return 0;
}

/*
 * Returns index of an unused element in sfp's rsv_arr, or -1 if it is full.
 * Marks that element's rsv_srp with ERR_PTR(-EBUSY) to reserve that index.
 */
static int
sg_get_idx_new(struct sg_fd *sfp)
{
	int k;
	struct sg_request **rapp = sfp->rsv_arr;

	for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
		if (!*rapp) {
			*rapp = ERR_PTR(-EBUSY);
			return k;
		}
	}
	return -1;
}

static int
sg_get_idx_new_lck(struct sg_fd *sfp)
{
	int res;
	unsigned long iflags;

	xa_lock_irqsave(&sfp->srp_arr, iflags);
	res = sg_get_idx_new(sfp);
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
	return res;
}

/*
 * Looks for an available element index in sfp's rsv_arr. That element's
 * sh_srp must be NULL and will be set to ERR_PTR(-EBUSY). If no element
 * is available then returns -1.
 */
static int
sg_get_idx_available(struct sg_fd *sfp)
{
	int k;
	struct sg_request **rapp = sfp->rsv_arr;
	struct sg_request *srp;

	for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
		srp = *rapp;
		if (!IS_ERR_OR_NULL(srp)) {
			if (!srp->sh_srp && !SG_RQ_ACTIVE(srp)) {
				srp->sh_srp = ERR_PTR(-EBUSY);
				return k;
			}
		}
	}
	return -1;
}

static struct sg_request *
sg_get_probable_read_side(struct sg_fd *sfp)
{
	struct sg_request **rapp = sfp->rsv_arr;
	struct sg_request **end_rapp = rapp + SG_MAX_RSV_REQS;
	struct sg_request *rs_srp;

	for ( ; rapp < end_rapp; ++rapp) {
		rs_srp = *rapp;
		if (IS_ERR_OR_NULL(rs_srp) || rs_srp->sh_srp)
			continue;
		switch (atomic_read(&rs_srp->rq_st)) {
		case SG_RQ_INFLIGHT:
		case SG_RQ_AWAIT_RCV:
		case SG_RQ_BUSY:
		case SG_RQ_SHR_SWAP:
			return rs_srp;
		default:
			break;
		}
	}
	/* Subsequent dout data transfers (e.g. WRITE) on a request share */
	for (rapp = sfp->rsv_arr; rapp < end_rapp; ++rapp) {
		rs_srp = *rapp;
		if (IS_ERR_OR_NULL(rs_srp) || rs_srp->sh_srp)
			continue;
		switch (atomic_read(&rs_srp->rq_st)) {
		case SG_RQ_INACTIVE:
			return rs_srp;
		default:
			break;
		}
	}
	return NULL;
}

/*
 * Returns string of the form: <leadin>rsv<num><leadout> if srp is one of
 * the reserve requests. Otherwise a blank string of length <leadin> plus
 * length of <leadout> is returned.
 */
static const char *
sg_get_rsv_str(struct sg_request *srp, const char *leadin,
	       const char *leadout, int b_len, char *b)
{
	int k, i_len, o_len, len;
	struct sg_fd *sfp;
	struct sg_request **rapp;

	if (!b || b_len < 1)
		return b;
	if (!leadin)
		leadin = "";
	if (!leadout)
		leadout = "";
	i_len = strlen(leadin);
	o_len = strlen(leadout);
	if (!srp)
		goto blank;
	sfp = srp->parentfp;
	if (!sfp)
		goto blank;
	rapp = sfp->rsv_arr;
	for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
		if (srp == *rapp)
			break;
	}
	if (k >= SG_MAX_RSV_REQS)
		goto blank;
	scnprintf(b, b_len, "%srsv%d%s", leadin, k, leadout);
	return b;
blank:
	len = min_t(int, i_len + o_len, b_len - 1);
	for (k = 0; k < len; ++k)
		b[k] = ' ';
	b[len] = '\0';
	return b;
}

static inline const char *
sg_get_rsv_str_lck(struct sg_request *srp, const char *leadin,
		   const char *leadout, int b_len, char *b)
{
	unsigned long iflags;
	const char *cp;

	xa_lock_irqsave(&srp->parentfp->srp_arr, iflags);
	cp = sg_get_rsv_str(srp, leadin, leadout, b_len, b);
	xa_unlock_irqrestore(&srp->parentfp->srp_arr, iflags);
	return cp;
}

static void
sg_execute_cmd(struct sg_fd *sfp, struct sg_request *srp)
{
	bool at_head, sync;
	struct sg_device *sdp = sfp->parentdp;
	struct request *rqq = READ_ONCE(srp->rqq);

	sync = test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm);
	SG_LOG(3, sfp, "%s: pack_id=%d\n", __func__, srp->pack_id);
	if (test_bit(SG_FFD_NO_DURATION, sfp->ffd_bm))
		srp->start_ns = 0;
	else
		srp->start_ns = ktime_get_boottime_ns();/* assume always > 0 */
	srp->duration = 0;

	if (!test_bit(SG_FRQ_IS_V4I, srp->frq_bm) && srp->s_hdr3.interface_id == '\0')
		at_head = true;	/* backward compatibility for v1+v2 interfaces */
	else if (test_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm))
		/* cmd flags can override sfd setting */
		at_head = !!(srp->rq_flags & SG_FLAG_Q_AT_HEAD);
	else            /* this sfd is defaulting to head */
		at_head = !(srp->rq_flags & SG_FLAG_Q_AT_TAIL);

	kref_get(&sfp->f_ref); /* put usually in: sg_rq_end_io() */
	sg_rq_chg_state_force(srp, SG_RQ_INFLIGHT);
	/* >>>>>>> send cmd/req off to other levels <<<<<<<< */
	if (!sync) {
		atomic_inc(&sfp->submitted);
		set_bit(SG_FRQ_COUNT_ACTIVE, srp->frq_bm);
	}
	if (srp->rq_flags & SGV4_FLAG_HIPRI) {
		if (test_bit(QUEUE_FLAG_POLL, &rqq->q->queue_flags)) {
			set_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm);
			rqq->cmd_flags |= REQ_HIPRI;
			srp->cookie = request_to_qc_t(rqq->mq_hctx, rqq);
		} else {
			clear_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm);
			srp->rq_flags &= ~SGV4_FLAG_HIPRI;
		}
	}
	blk_execute_rq_nowait(sdp->disk, rqq, (int)at_head, sg_rq_end_io);
	set_bit(SG_FRQ_ISSUED, srp->frq_bm);
}

/*
 * All writes and submits converge on this function to launch the SCSI
 * command/request (via blk_execute_rq_nowait). Returns a pointer to a
 * sg_request object holding the request just issued or a negated errno
 * value twisted by ERR_PTR.
 * N.B. pack_id placed in sg_io_v4::request_extra field.
 */
static struct sg_request *
sg_common_write(struct sg_comm_wr_t *cwrp)
{
	int res = 0;
	int dlen = cwrp->dlen;
	int dir;
	int pack_id = SG_PACK_ID_WILDCARD;
	u32 rq_flags;
	enum sg_shr_var sh_var;
	struct sg_fd *fp = cwrp->sfp;
	struct sg_device *sdp = fp->parentdp;
	struct sg_request *srp;
	struct sg_io_hdr *hi_p;
	struct sg_io_v4 *h4p;

	if (likely(test_bit(SG_FRQ_IS_V4I, cwrp->frq_bm))) {
		h4p = cwrp->h4p;
		hi_p = NULL;
		dir = SG_DXFER_NONE;
		rq_flags = h4p->flags;
		pack_id = h4p->request_extra;
		if (unlikely(h4p->din_xfer_len && h4p->dout_xfer_len))
			return ERR_PTR(-EOPNOTSUPP);
		else if (h4p->din_xfer_len)
			dir = SG_DXFER_FROM_DEV;
		else if (h4p->dout_xfer_len)
			dir = SG_DXFER_TO_DEV;
	} else {			/* sg v3 interface so hi_p valid */
		h4p = NULL;
		hi_p = cwrp->h3p;
		dir = hi_p->dxfer_direction;
		rq_flags = hi_p->flags;
		pack_id = hi_p->pack_id;
	}
	if (unlikely(rq_flags & SGV4_FLAG_MULTIPLE_REQS))
		return ERR_PTR(-ERANGE);  /* only control object sets this */
	if (sg_fd_is_shared(fp)) {
		res = sg_share_chk_flags(fp, rq_flags, dlen, dir, &sh_var);
		if (unlikely(res < 0))
			return ERR_PTR(res);
	} else {
		sh_var = SG_SHR_NONE;
		if (unlikely(rq_flags & SGV4_FLAG_SHARE))
			return ERR_PTR(-ENOMSG);    /* no file share found */
	}
	if (unlikely(dlen >= SZ_256M))
		return ERR_PTR(-EINVAL);

	srp = sg_setup_req(cwrp, sh_var);
	if (IS_ERR(srp))
		return srp;
	srp->rq_flags = rq_flags;
	srp->pack_id = pack_id;

	if (likely(h4p)) {
		srp->s_hdr4.usr_ptr = h4p->usr_ptr;
		srp->s_hdr4.sbp = uptr64(h4p->response);
		srp->s_hdr4.max_sb_len = h4p->max_response_len;
		srp->s_hdr4.cmd_len = h4p->request_len;
		srp->s_hdr4.dir = dir;
		srp->s_hdr4.out_resid = 0;
		srp->s_hdr4.mrq_ind = 0;
		if (dir == SG_DXFER_TO_DEV) {
			srp->s_hdr4.wr_offset = cwrp->wr_offset;
			srp->s_hdr4.wr_len = dlen;
		}
	} else {	/* v3 interface active */
		memcpy(&srp->s_hdr3, hi_p, sizeof(srp->s_hdr3));
	}
	res = sg_start_req(srp, cwrp, dir);
	if (unlikely(res < 0))	/* probably out of space --> -ENOMEM */
		goto err_out;
	SG_LOG(4, fp, "%s: opcode=0x%02x, cdb_sz=%d, pack_id=%d\n", __func__,
	       srp->cmd_opcode, cwrp->cmd_len, pack_id);
	if (SG_IS_DETACHING(sdp)) {
		res = -ENODEV;
		goto err_out;
	}
	READ_ONCE(srp->rqq)->timeout = cwrp->timeout;
	sg_execute_cmd(fp, srp);
	return srp;
err_out:
	sg_deact_request(fp, srp);
	return ERR_PTR(res);
}

/*
 * ***********************************************************************
 * read(2) related functions follow. They are shown after write(2) related
 * functions. Apart from read(2) itself, ioctl(SG_IORECEIVE) and the second
 * half of the ioctl(SG_IO) share code with read(2).
 * ***********************************************************************
 */

/*
 * This function is called by wait_event_interruptible in sg_read() and
 * sg_ctl_ioreceive(). wait_event_interruptible will return if this one
 * returns true (or an event like a signal (e.g. control-C) occurs).
 */
static inline bool
sg_get_ready_srp(struct sg_fd *sfp, struct sg_request **srpp, int id,
		 bool is_tag)
{
	struct sg_request *srp;

	if (SG_IS_DETACHING(sfp->parentdp)) {
		*srpp = ERR_PTR(-ENODEV);
		return true;
	}
	srp = sg_find_srp_by_id(sfp, id, is_tag);
	*srpp = srp;
	return !!srp;
}

/*
 * Returns number of bytes copied to user space provided sense buffer or
 * negated errno value.
 */
static int
sg_copy_sense(struct sg_request *srp, bool v4_active)
{
	int sb_len_ret = 0;
	int scsi_stat;

	/* If need be, copy the sense buffer to the user space */
	scsi_stat = srp->rq_result & 0xfe;
	if (unlikely((scsi_stat & SAM_STAT_CHECK_CONDITION) ||
		     (driver_byte(srp->rq_result) & DRIVER_SENSE))) {
		int sb_len = min_t(int, SCSI_SENSE_BUFFERSIZE, srp->sense_len);
		int mx_sb_len;
		u8 *sbp = srp->sense_bp;
		void __user *up;

		srp->sense_bp = NULL;
		if (v4_active) {
			up = uptr64(srp->s_hdr4.sbp);
			mx_sb_len = srp->s_hdr4.max_sb_len;
		} else {
			up = (void __user *)srp->s_hdr3.sbp;
			mx_sb_len = srp->s_hdr3.mx_sb_len;
		}
		if (up && mx_sb_len > 0 && sbp) {
			sb_len = min_t(int, mx_sb_len, sb_len);
			/* Additional sense length field */
			sb_len_ret = 8 + (int)sbp[7];
			sb_len_ret = min_t(int, sb_len_ret, sb_len);
			if (copy_to_user(up, sbp, sb_len_ret))
				sb_len_ret = -EFAULT;
		}
		mempool_free(sbp, sg_sense_pool);
	}
	return sb_len_ret;
}

static int
sg_rec_state_v3v4(struct sg_fd *sfp, struct sg_request *srp, bool v4_active)
{
	int err = 0;
	u32 rq_res = srp->rq_result;
	enum sg_shr_var sh_var = srp->sh_var;
	enum sg_rq_state rs_st = SG_RQ_INACTIVE;
	struct sg_request *rs_srp;

	if (unlikely(!scsi_status_is_good(rq_res))) {
		int sb_len_wr = sg_copy_sense(srp, v4_active);

		if (unlikely(sb_len_wr < 0))
			return sb_len_wr;
	}
	if (!sg_result_is_good(rq_res))
		srp->rq_info |= SG_INFO_CHECK;
	if (unlikely(test_bit(SG_FRQ_ABORTING, srp->frq_bm)))
		srp->rq_info |= SG_INFO_ABORTED;

	if (sh_var == SG_SHR_WS_RQ && sg_fd_is_shared(sfp)) {
		__maybe_unused char b[32];

		rs_srp = srp->sh_srp;
		if (!rs_srp)
			return -EPROTO;
		rs_st = atomic_read(&rs_srp->rq_st);

		switch (rs_st) {
		case SG_RQ_SHR_SWAP:
			if (!(srp->rq_flags & SGV4_FLAG_KEEP_SHARE))
				goto set_inactive;
			SG_LOG(6, sfp, "%s: hold onto %s share\n",
			       __func__, sg_get_rsv_str(rs_srp, "", "",
							sizeof(b), b));
			break;
		case SG_RQ_SHR_IN_WS:
			if (!(srp->rq_flags & SGV4_FLAG_KEEP_SHARE))
				goto set_inactive;
			err = sg_rq_chg_state(rs_srp, rs_st, SG_RQ_SHR_SWAP);
			SG_LOG(6, sfp, "%s: hold onto %s share\n",
			       __func__, sg_get_rsv_str(rs_srp, "", "",
							sizeof(b), b));
			break;
		case SG_RQ_AWAIT_RCV:
			break;
		case SG_RQ_INACTIVE:
			/* remove request share mapping */
			rs_srp->sh_srp = NULL;
			break;
		default:
			err = -EPROTO;	/* Logic error */
			SG_LOG(1, sfp,
			       "%s: SHR_WS_RQ, bad read-side state: %s\n",
			       __func__, sg_rq_st_str(rs_st, true));
			break;	/* nothing to do */
		}
	}
	if (SG_IS_DETACHING(sfp->parentdp))
		srp->rq_info |= SG_INFO_DEVICE_DETACHING;
	return err;
set_inactive:
	/* make read-side request available for re-use */
	rs_srp->tag = SG_TAG_WILDCARD;
	rs_srp->sh_var = SG_SHR_NONE;
	sg_rq_chg_state_force(rs_srp, SG_RQ_INACTIVE);
	atomic_inc(&rs_srp->parentfp->inactives);
	rs_srp->frq_bm[0] &= (1 << SG_FRQ_RESERVED);
	rs_srp->in_resid = 0;
	rs_srp->rq_info = 0;
	rs_srp->sense_len = 0;
	rs_srp->sh_srp = NULL;
	return err;
}

static void
sg_complete_shr_rs(struct sg_fd *sfp, struct sg_request *srp, bool other_err,
		   enum sg_rq_state sr_st)
{
	int poll_type = POLL_OUT;
	struct sg_fd *ws_sfp = sg_fd_share_ptr(sfp);

	if (unlikely(!sg_result_is_good(srp->rq_result) || other_err)) {
		set_bit(SG_FFD_READ_SIDE_ERR, sfp->ffd_bm);
		sg_rq_chg_state_force(srp, SG_RQ_BUSY);
		poll_type = POLL_HUP;   /* "Hang-UP flag */
	} else if (sr_st != SG_RQ_SHR_SWAP) {
		sg_rq_chg_state_force(srp, SG_RQ_SHR_SWAP);
	}
	if (ws_sfp && !srp->sh_srp) {
		if (ws_sfp->async_qp &&
		    (!SG_IS_V4I(srp) || (srp->rq_flags & SGV4_FLAG_SIGNAL)))
			kill_fasync(&ws_sfp->async_qp, SIGPOLL, poll_type);
		if (ws_sfp->efd_ctxp && (srp->rq_flags & SGV4_FLAG_EVENTFD)) {
			u64 n = eventfd_signal(ws_sfp->efd_ctxp, 1);

			if (n != 1)
				pr_info("%s: srp=%pK eventfd prob\n",
					__func__, srp);
		}
	}
}

static void
sg_complete_v3v4(struct sg_fd *sfp, struct sg_request *srp, bool other_err)
{
	enum sg_rq_state sr_st = atomic_read(&srp->rq_st);

	/* advance state machine, send signal to write-side if appropriate */
	SG_LOG(4, sfp, "%s: %pK: sh_var=%s\n", __func__, srp,
	       sg_shr_str(srp->sh_var, true));
	switch (srp->sh_var) {
	case SG_SHR_RS_RQ:
		sg_complete_shr_rs(sfp, srp, other_err, sr_st);
		break;
	case SG_SHR_WS_RQ:	/* cleanup both on write-side completion */
		if (likely(sg_fd_is_shared(sfp))) {
			struct sg_request *rs_srp = srp->sh_srp;

			if (rs_srp) {
				rs_srp->sh_srp = NULL;
				rs_srp->sh_var = SG_SHR_RS_NOT_SRQ;
			} else {
				SG_LOG(2, sfp, "%s: write-side's paired read is missing\n",
				       __func__);
			}
		}
		srp->sh_var = SG_SHR_WS_NOT_SRQ;
		srp->sh_srp = NULL;
		srp->sgatp = &srp->sgat_h;
		if (sr_st != SG_RQ_BUSY)
			sg_rq_chg_state_force(srp, SG_RQ_BUSY);
		break;
	case SG_SHR_WS_NOT_SRQ:
	default:
		if (sr_st != SG_RQ_BUSY)
			sg_rq_chg_state_force(srp, SG_RQ_BUSY);
		break;
	}
}

static int
sg_receive_v4(struct sg_fd *sfp, struct sg_request *srp, void __user *p,
	      struct sg_io_v4 *h4p)
{
	int err;
	u32 rq_result = srp->rq_result;

	SG_LOG(3, sfp, "%s: p=%s, h4p=%s\n", __func__,
	       (p ? "given" : "NULL"), (h4p ? "given" : "NULL"));
	err = sg_rec_state_v3v4(sfp, srp, true);
	h4p->guard = 'Q';
	h4p->protocol = 0;
	h4p->subprotocol = 0;
	h4p->device_status = rq_result & 0xff;
	h4p->driver_status = driver_byte(rq_result);
	h4p->transport_status = host_byte(rq_result);
	h4p->response_len = srp->sense_len;
	h4p->info = srp->rq_info;
	h4p->flags = srp->rq_flags;
	h4p->duration = srp->duration;
	switch (srp->s_hdr4.dir) {
	case SG_DXFER_FROM_DEV:
		h4p->din_xfer_len = srp->sgatp->dlen;
		break;
	case SG_DXFER_TO_DEV:
		h4p->dout_xfer_len = srp->sgatp->dlen;
		break;
	default:
		break;
	}
	h4p->din_resid = srp->in_resid;
	h4p->dout_resid = srp->s_hdr4.out_resid;
	h4p->usr_ptr = srp->s_hdr4.usr_ptr;
	h4p->response = (uintptr_t)srp->s_hdr4.sbp;
	h4p->request_extra = srp->pack_id;
	if (test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm))
		h4p->generated_tag = srp->tag;
	if (p) {
		if (copy_to_user(p, h4p, SZ_SG_IO_V4))
			err = err ? err : -EFAULT;
	}
	sg_complete_v3v4(sfp, srp, err < 0);
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return unlikely(err < 0) ? err : 0;
}

/*
 * Invoked when user calls ioctl(SG_IORECEIVE, SGV4_FLAG_MULTIPLE_REQS).
 * Returns negative on error including -ENODATA if there are no mrqs submitted
 * nor waiting. Otherwise it returns the number of elements written to
 * rsp_arr, which may be 0 if mrqs submitted but none waiting
 */
static int
sg_mrq_iorec_complets(struct sg_fd *sfp, bool non_block, int max_mrqs,
		      struct sg_io_v4 *rsp_arr)
{
	int k;
	int res = 0;
	struct sg_request *srp;

	SG_LOG(3, sfp, "%s: max_mrqs=%d\n", __func__, max_mrqs);
	for (k = 0; k < max_mrqs; ++k) {
		if (!sg_mrq_get_ready_srp(sfp, &srp))
			break;
		if (IS_ERR(srp))
			return k ? k : PTR_ERR(srp);
		res = sg_receive_v4(sfp, srp, NULL, rsp_arr + k);
		if (unlikely(res))
			return res;
		rsp_arr[k].info |= SG_INFO_MRQ_FINI;
	}
	if (non_block)
		return k;

	for ( ; k < max_mrqs; ++k) {
		res = sg_wait_mrq_event(sfp, &srp);
		if (unlikely(res))
			return res;	/* signal --> -ERESTARTSYS */
		if (IS_ERR(srp))
			return k ? k : PTR_ERR(srp);
		res = sg_receive_v4(sfp, srp, NULL, rsp_arr + k);
		if (unlikely(res))
			return res;
		rsp_arr[k].info |= SG_INFO_MRQ_FINI;
	}
	return k;
}

/*
 * Invoked when user calls ioctl(SG_IORECEIVE, SGV4_FLAG_MULTIPLE_REQS).
 * Expected race as many concurrent calls with the same pack_id/tag can
 * occur. Only one should succeed per request (more may succeed but will get
 * different requests).
 */
static int
sg_mrq_ioreceive(struct sg_fd *sfp, struct sg_io_v4 *cop, void __user *p,
		 bool non_block)
{
	int res = 0;
	u32 len, n;
	struct sg_io_v4 *rsp_v4_arr;
	void __user *pp;

	SG_LOG(3, sfp, "%s: non_block=%d\n", __func__, !!non_block);
	n = cop->din_xfer_len;
	if (unlikely(n > SG_MAX_MULTI_REQ_SZ))
		return -E2BIG;
	if (unlikely(!cop->din_xferp || n < SZ_SG_IO_V4 || (n % SZ_SG_IO_V4)))
		return -ERANGE;
	n /= SZ_SG_IO_V4;
	len = n * SZ_SG_IO_V4;
	SG_LOG(3, sfp, "%s: %s, num_reqs=%u\n", __func__,
	       (non_block ? "IMMED" : "blocking"), n);
	rsp_v4_arr = kcalloc(n, SZ_SG_IO_V4, GFP_KERNEL);
	if (unlikely(!rsp_v4_arr))
		return -ENOMEM;

	sg_v4h_partial_zero(cop);
	cop->din_resid = n;
	res = sg_mrq_iorec_complets(sfp, non_block, n, rsp_v4_arr);
	if (unlikely(res < 0))
		goto fini;
	cop->din_resid -= res;
	cop->info = res;	/* number received */
	if (copy_to_user(p, cop, sizeof(*cop)))
		return -EFAULT;
	res = 0;
	pp = uptr64(cop->din_xferp);
	if (likely(pp)) {
		if (copy_to_user(pp, rsp_v4_arr, len))
			res = -EFAULT;
	} else {
		SG_LOG(1, sfp, "%s: cop->din_xferp==NULL ?_?\n", __func__);
	}
fini:
	kfree(rsp_v4_arr);
	return res;
}

static int
sg_wait_id_event(struct sg_fd *sfp, struct sg_request **srpp, int id,
		 bool is_tag)
{
	if (test_bit(SG_FFD_EXCL_WAITQ, sfp->ffd_bm))
		return __wait_event_interruptible_exclusive
				(sfp->cmpl_wait,
				 sg_get_ready_srp(sfp, srpp, id, is_tag));
	return __wait_event_interruptible
			(sfp->cmpl_wait,
			 sg_get_ready_srp(sfp, srpp, id, is_tag));
}

/*
 * Called when ioctl(SG_IORECEIVE) received. Expects a v4 interface object.
 * Checks if O_NONBLOCK file flag given, if not checks given 'flags' field
 * to see if SGV4_FLAG_IMMED is set. Either of these implies non blocking.
 * When non-blocking and there is no request waiting, yields EAGAIN;
 * otherwise it waits (i.e. it "blocks").
 */
static int
sg_ctl_ioreceive(struct sg_fd *sfp, void __user *p)
{
	bool non_block = SG_IS_O_NONBLOCK(sfp);
	bool use_tag = false;
	int res, id;
	int pack_id = SG_PACK_ID_WILDCARD;
	int tag = SG_TAG_WILDCARD;
	struct sg_io_v4 h4;
	struct sg_io_v4 *h4p = &h4;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp;

	res = sg_allow_if_err_recovery(sdp, non_block);
	if (unlikely(res))
		return res;
	/* Get first three 32 bit integers: guard, proto+subproto */
	if (copy_from_user(h4p, p, SZ_SG_IO_V4))
		return -EFAULT;
	/* for v4: protocol=0 --> SCSI;  subprotocol=0 --> SPC++ */
	if (unlikely(h4p->guard != 'Q' || h4p->protocol != 0 ||
		     h4p->subprotocol != 0))
		return -EPERM;
	if (h4p->flags & SGV4_FLAG_IMMED)
		non_block = true;	/* set by either this or O_NONBLOCK */
	SG_LOG(3, sfp, "%s: non_block(+IMMED)=%d\n", __func__, non_block);
	if (h4p->flags & SGV4_FLAG_MULTIPLE_REQS)
		return sg_mrq_ioreceive(sfp, h4p, p, non_block);
	/* read in part of v3 or v4 header for pack_id or tag based find */
	if (test_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm)) {
		use_tag = test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm);
		if (use_tag)
			tag = h4p->request_tag;	/* top 32 bits ignored */
		else
			pack_id = h4p->request_extra;
	}
	id = use_tag ? tag : pack_id;
try_again:
	srp = sg_find_srp_by_id(sfp, id, use_tag);
	if (!srp) {     /* nothing available so wait on packet or */
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (non_block)
			return -EAGAIN;
		res = sg_wait_id_event(sfp, &srp, id, use_tag);
		if (unlikely(res))
			return res;	/* signal --> -ERESTARTSYS */
		if (IS_ERR(srp))
			return PTR_ERR(srp);
	}	/* now srp should be valid */
	if (test_and_set_bit(SG_FRQ_RECEIVING, srp->frq_bm)) {
		cpu_relax();
		goto try_again;
	}
	return sg_receive_v4(sfp, srp, p, h4p);
}

/*
 * Called when ioctl(SG_IORECEIVE_V3) received. Expects a v3 interface.
 * Checks if O_NONBLOCK file flag given, if not checks given flags field
 * to see if SGV4_FLAG_IMMED is set. Either of these implies non blocking.
 * When non-blocking and there is no request waiting, yields EAGAIN;
 * otherwise it waits.
 */
static int
sg_ctl_ioreceive_v3(struct sg_fd *sfp, void __user *p)
{
	bool non_block = SG_IS_O_NONBLOCK(sfp);
	int res;
	int pack_id = SG_PACK_ID_WILDCARD;
	struct sg_io_hdr h3;
	struct sg_io_hdr *h3p = &h3;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp;

	res = sg_allow_if_err_recovery(sdp, non_block);
	if (unlikely(res))
		return res;
	/* Get first three 32 bit integers: guard, proto+subproto */
	if (copy_from_user(h3p, p, SZ_SG_IO_HDR))
		return -EFAULT;
	/* for v3: interface_id=='S' (in a 32 bit int) */
	if (unlikely(h3p->interface_id != 'S'))
		return -EPERM;
	if (h3p->flags & SGV4_FLAG_IMMED)
		non_block = true;	/* set by either this or O_NONBLOCK */
	SG_LOG(3, sfp, "%s: non_block(+IMMED)=%d\n", __func__, non_block);
	if (unlikely(h3p->flags & SGV4_FLAG_MULTIPLE_REQS))
		return -EINVAL;

	if (test_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm))
		pack_id = h3p->pack_id;
try_again:
	srp = sg_find_srp_by_id(sfp, pack_id, false);
	if (!srp) {     /* nothing available so wait on packet or */
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (non_block)
			return -EAGAIN;
		res = sg_wait_id_event(sfp, &srp, pack_id, false);
		if (unlikely(res))
			return res;	/* signal --> -ERESTARTSYS */
		if (IS_ERR(srp))
			return PTR_ERR(srp);
	}	/* now srp should be valid */
	if (test_and_set_bit(SG_FRQ_RECEIVING, srp->frq_bm)) {
		cpu_relax();
		goto try_again;
	}
	return sg_receive_v3(sfp, srp, p);
}

static int
sg_read_v1v2(void __user *buf, int count, struct sg_fd *sfp,
	     struct sg_request *srp)
{
	int res = 0;
	u32 rq_res = srp->rq_result;
	struct sg_header *h2p;
	struct sg_slice_hdr3 *sh3p;
	struct sg_header a_v2hdr;

	h2p = &a_v2hdr;
	memset(h2p, 0, SZ_SG_HEADER);
	sh3p = &srp->s_hdr3;
	h2p->reply_len = (int)sh3p->timeout;
	h2p->pack_len = h2p->reply_len; /* old, strange behaviour */
	h2p->pack_id = sh3p->pack_id;
	h2p->twelve_byte = (srp->cmd_opcode >= 0xc0 && sh3p->cmd_len == 12);
	h2p->target_status = status_byte(rq_res);
	h2p->host_status = host_byte(rq_res);
	h2p->driver_status = driver_byte(rq_res);
	if (unlikely(!scsi_status_is_good(rq_res) ||
		     (driver_byte(rq_res) & DRIVER_SENSE))) {
		if (likely(srp->sense_bp)) {
			u8 *sbp = srp->sense_bp;

			srp->sense_bp = NULL;
			memcpy(h2p->sense_buffer, sbp,
			       sizeof(h2p->sense_buffer));
			mempool_free(sbp, sg_sense_pool);
		}
	}
	switch (unlikely(host_byte(rq_res))) {
	/*
	 * This following setting of 'result' is for backward compatibility
	 * and is best ignored by the user who should use target, host and
	 * driver status.
	 */
	case DID_OK:
	case DID_PASSTHROUGH:
	case DID_SOFT_ERROR:
		h2p->result = 0;
		break;
	case DID_NO_CONNECT:
	case DID_BUS_BUSY:
	case DID_TIME_OUT:
		h2p->result = EBUSY;
		break;
	case DID_BAD_TARGET:
	case DID_ABORT:
	case DID_PARITY:
	case DID_RESET:
	case DID_BAD_INTR:
		h2p->result = EIO;
		break;
	case DID_ERROR:
		h2p->result = sg_result_is_good(rq_res) ? 0 : EIO;
		break;
	default:
		h2p->result = EIO;
		break;
	}

	/* Now copy the result back to the user buffer.  */
	if (count >= SZ_SG_HEADER) {
		if (copy_to_user(buf, h2p, SZ_SG_HEADER)) {
			res = -EFAULT;
			goto fini;
		}
		buf += SZ_SG_HEADER;
		if (count > h2p->reply_len)
			count = h2p->reply_len;
		if (count > SZ_SG_HEADER) {
			res = sg_read_append(srp, buf, count - SZ_SG_HEADER);
			if (unlikely(res))
				goto fini;
		}
	} else {
		res = (h2p->result == 0) ? 0 : -EIO;
	}
fini:
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return res;
}

/*
 * This is the read(2) system call entry point (see sg_fops) for this driver.
 * Accepts v1, v2 or v3 type headers (not v4). Returns count or negated
 * errno; if count is 0 then v3: returns -EINVAL; v1+v2: 0 when no other
 * error detected or -EIO.
 */
static ssize_t
sg_read(struct file *filp, char __user *p, size_t count, loff_t *ppos)
{
	bool could_be_v3;
	bool non_block = !!(filp->f_flags & O_NONBLOCK);
	int want_id = SG_PACK_ID_WILDCARD;
	int hlen, ret;
	struct sg_device *sdp = NULL;
	struct sg_fd *sfp;
	struct sg_request *srp = NULL;
	struct sg_header *h2p = NULL;
	struct sg_io_hdr a_sg_io_hdr;

	/*
	 * This could cause a response to be stranded. Close the associated
	 * file descriptor to free up any resources being held.
	 */
	ret = sg_check_file_access(filp, __func__);
	if (unlikely(ret))
		return ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	SG_LOG(3, sfp, "%s: read() count=%d\n", __func__, (int)count);
	ret = sg_allow_if_err_recovery(sdp, non_block);
	if (unlikely(ret))
		return ret;

	could_be_v3 = (count >= SZ_SG_IO_HDR);
	hlen = could_be_v3 ? SZ_SG_IO_HDR : SZ_SG_HEADER;
	h2p = (struct sg_header *)&a_sg_io_hdr;

	if (test_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm) && (int)count >= hlen) {
		/*
		 * Even though this is a user space read() system call, this
		 * code is cheating to fetch the pack_id.
		 * Only need first three 32 bit ints to determine interface.
		 */
		if (copy_from_user(h2p, p, 3 * sizeof(int)))
			return -EFAULT;
		if (h2p->reply_len < 0 && could_be_v3) {
			struct sg_io_hdr *v3_hdr = (struct sg_io_hdr *)h2p;

			if (likely(v3_hdr->interface_id == 'S')) {
				struct sg_io_hdr __user *h3_up;

				h3_up = (struct sg_io_hdr __user *)p;
				ret = get_user(want_id, &h3_up->pack_id);
				if (unlikely(ret))
					return ret;
				if (!non_block) {
					int flgs;

					ret = get_user(flgs, &h3_up->flags);
					if (unlikely(ret))
						return ret;
					if (flgs & SGV4_FLAG_IMMED)
						non_block = true;
				}
			} else if (v3_hdr->interface_id == 'Q') {
				pr_info_once("sg: %s: v4 interface%s here\n",
					     __func__, " disallowed");
				return -EPERM;
			} else {
				return -EPERM;
			}
		} else { /* for v1+v2 interfaces, this is the 3rd integer */
			want_id = h2p->pack_id;
		}
	}
try_again:
	srp = sg_find_srp_by_id(sfp, want_id, false);
	if (!srp) {	/* nothing available so wait on packet to arrive or */
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (non_block) /* O_NONBLOCK or v3::flags & SGV4_FLAG_IMMED */
			return -EAGAIN;
		ret = sg_wait_id_event(sfp, &srp, want_id, false);
		if (unlikely(ret))  /* -ERESTARTSYS as signal hit process */
			return ret;
		if (IS_ERR(srp))
			return PTR_ERR(srp);
		/* otherwise srp should be valid */
	}
	if (test_and_set_bit(SG_FRQ_RECEIVING, srp->frq_bm)) {
		cpu_relax();
		goto try_again;
	}
	if (srp->s_hdr3.interface_id == '\0') {
		ret = sg_read_v1v2(p, (int)count, sfp, srp);
	} else {
		if (in_compat_syscall()) {
			if (count < sizeof(struct compat_sg_io_hdr))
				return -EINVAL;
		} else if (count < SZ_SG_IO_HDR) {
			return -EINVAL;
		}
		ret = sg_receive_v3(sfp, srp, p);
	}
#if IS_ENABLED(SG_LOG_ACTIVE)
	if (unlikely(ret < 0))
		SG_LOG(1, sfp, "%s: negated errno: %d\n", __func__, ret);
#endif
	return unlikely(ret < 0) ? ret : (int)count;
}

/*
 * Completes a v3 request/command. Called from sg_read {v2 or v3},
 * ioctl(SG_IO) {for v3}, or from ioctl(SG_IORECEIVE) when its
 * completing a v3 request/command.
 */
static int
sg_receive_v3(struct sg_fd *sfp, struct sg_request *srp, void __user *p)
{
	int err, err2;
	int rq_res = srp->rq_result;
	struct sg_io_hdr hdr3;
	struct sg_io_hdr *hp = &hdr3;

	SG_LOG(3, sfp, "%s: sh_var: %s srp=0x%pK\n", __func__,
	       sg_shr_str(srp->sh_var, false), srp);
	err = sg_rec_state_v3v4(sfp, srp, false);
	memset(hp, 0, sizeof(*hp));
	memcpy(hp, &srp->s_hdr3, sizeof(srp->s_hdr3));
	hp->sb_len_wr = srp->sense_len;
	hp->info = srp->rq_info;
	hp->resid = srp->in_resid;
	hp->pack_id = srp->pack_id;
	hp->duration = srp->duration;
	hp->status = rq_res & 0xff;
	hp->masked_status = status_byte(rq_res);
	hp->msg_status = msg_byte(rq_res);
	hp->host_status = host_byte(rq_res);
	hp->driver_status = driver_byte(rq_res);
	err2 = put_sg_io_hdr(hp, p);
	err = err ? err : err2;
	sg_complete_v3v4(sfp, srp, err < 0);
	sg_finish_scsi_blk_rq(srp);
	sg_deact_request(sfp, srp);
	return err;
}

static int
max_sectors_bytes(struct request_queue *q)
{
	unsigned int max_sectors = queue_max_sectors(q);

	max_sectors = min_t(unsigned int, max_sectors, INT_MAX >> 9);
	return max_sectors << 9;
}

/*
 * Calculates sg_device::max_sgat_elems and sg_device::max_sgat_sz. It uses
 * the device's request queue. If q not available sets max_sgat_elems to 1
 * and max_sgat_sz to PAGE_SIZE. If potential max_sgat_sz is greater than
 * 2^30 scales down the implied max_segment_size so the product of the
 * max_segment_size and max_sgat_elems is less than or equal to 2^30 .
 */
static void
sg_calc_sgat_param(struct sg_device *sdp)
{
	int sz;
	u64 m;
	struct scsi_device *sdev = sdp->device;
	struct request_queue *q = sdev ? sdev->request_queue : NULL;

	clear_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm);
	if (!q) {
		sdp->max_sgat_elems = 1;
		sdp->max_sgat_sz = PAGE_SIZE;
		return;
	}
	sdp->max_sgat_elems = queue_max_segments(q);
	m = (u64)queue_max_segment_size(q) * queue_max_segments(q);
	if (m < PAGE_SIZE) {
		sdp->max_sgat_elems = 1;
		sdp->max_sgat_sz = PAGE_SIZE;
		return;
	}
	sz = (int)min_t(u64, m, 1 << 30);
	if (sz == (1 << 30))	/* round down so: sz = elems * elem_sz */
		sz = ((1 << 30) / sdp->max_sgat_elems) * sdp->max_sgat_elems;
	sdp->max_sgat_sz = sz;
}

/*
 * Only valid for shared file descriptors. Designed to be called after a
 * read-side request has successfully completed leaving valid data in a
 * reserve request buffer. The read-side is moved from SG_RQ_SHR_SWAP
 * to SG_RQ_INACTIVE state and returns 0. Acts on first reserve requests.
 * Otherwise -EINVAL is returned, unless write-side is in progress in
 * which case -EBUSY is returned.
 */
static int
sg_finish_rs_rq(struct sg_fd *sfp)
{
	int res = -EINVAL;
	int k;
	enum sg_rq_state sr_st;
	unsigned long iflags;
	struct sg_fd *rs_sfp;
	struct sg_request *rs_rsv_srp;
	struct sg_device *sdp = sfp->parentdp;

	rs_sfp = sg_fd_share_ptr(sfp);
	if (unlikely(!rs_sfp))
		goto fini;
	if (xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_RS_SHARE))
		rs_sfp = sfp;

	for (k = 0; k < SG_MAX_RSV_REQS; ++k) {
		res = -EINVAL;
		rs_rsv_srp = rs_sfp->rsv_arr[k];
		if (IS_ERR_OR_NULL(rs_rsv_srp))
			continue;
		xa_lock_irqsave(&rs_sfp->srp_arr, iflags);
		sr_st = atomic_read(&rs_rsv_srp->rq_st);
		switch (sr_st) {
		case SG_RQ_SHR_SWAP:
			res = sg_rq_chg_state_ulck(rs_rsv_srp, sr_st, SG_RQ_BUSY);
			if (!res)
				atomic_inc(&rs_sfp->inactives);
			rs_rsv_srp->tag = SG_TAG_WILDCARD;
			rs_rsv_srp->sh_var = SG_SHR_NONE;
			set_bit(SG_FRQ_RESERVED, rs_rsv_srp->frq_bm);
			rs_rsv_srp->in_resid = 0;
			rs_rsv_srp->rq_info = 0;
			rs_rsv_srp->sense_len = 0;
			rs_rsv_srp->sh_srp = NULL;
			sg_finish_scsi_blk_rq(rs_rsv_srp);
			sg_deact_request(rs_rsv_srp->parentfp, rs_rsv_srp);
			break;
		case SG_RQ_SHR_IN_WS:	/* too late, write-side rq active */
		case SG_RQ_BUSY:
			res = -EBUSY;
			break;
		default:
			res = -EINVAL;
			break;
		}
		xa_unlock_irqrestore(&rs_sfp->srp_arr, iflags);
		if (res == 0)
			return res;
	}
fini:
	if (unlikely(res))
		SG_LOG(1, sfp, "%s: err=%d\n", __func__, -res);
	return res;
}

static void
sg_unshare_rs_fd(struct sg_fd *rs_sfp, bool lck)
{
	int k;
	unsigned long iflags = 0;
	struct sg_device *sdp = rs_sfp->parentdp;
	struct sg_request **rapp = rs_sfp->rsv_arr;
	struct xarray *xadp = &sdp->sfp_arr;
	struct sg_request *r_srp;

	if (lck)
		xa_lock_irqsave_nested(xadp, iflags, 1);
	__clear_bit(SG_FFD_RESHARE, rs_sfp->ffd_bm);
	for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
		r_srp = *rapp;
		if (IS_ERR_OR_NULL(r_srp))
			continue;
		r_srp->sh_srp = NULL;
	}
	__xa_set_mark(xadp, rs_sfp->idx, SG_XA_FD_UNSHARED);
	__xa_clear_mark(xadp, rs_sfp->idx, SG_XA_FD_RS_SHARE);
	if (lck)
		xa_unlock_irqrestore(xadp, iflags);
	rcu_assign_pointer(rs_sfp->share_sfp, NULL);
	kref_put(&rs_sfp->f_ref, sg_remove_sfp);/* get: sg_find_sfp_by_fd() */
}

static void
sg_unshare_ws_fd(struct sg_fd *ws_sfp, bool lck)
{
	unsigned long iflags;
	struct sg_device *sdp = ws_sfp->parentdp;
	struct xarray *xadp = &sdp->sfp_arr;

	if (lck)
		xa_lock_irqsave_nested(xadp, iflags, 1);
	__xa_set_mark(xadp, ws_sfp->idx, SG_XA_FD_UNSHARED);
	/* SG_XA_FD_RS_SHARE mark should be already clear */
	if (lck)
		xa_unlock_irqrestore(xadp, iflags);
	rcu_assign_pointer(ws_sfp->share_sfp, NULL);
	kref_put(&ws_sfp->f_ref, sg_remove_sfp);/* get: sg_find_sfp_by_fd() */
}

/*
 * Clean up loose ends that occur when closing a file descriptor which is
 * part of a file share. There may be request shares in various states using
 * this file share so care is needed. Potential race when both sides of fd
 * share have their fd_s closed (i.e. sg_release()) at around the same time
 * is the reason for rechecking the FD_RS_SHARE or FD_UNSHARED marks.
 */
static void
sg_remove_sfp_share(struct sg_fd *sfp, bool is_rd_side)
		__must_hold(sfp->parentdp->open_rel_lock)
{
	__maybe_unused int res = 0;
	int k, retry_count;
	unsigned long iflags;
	enum sg_rq_state sr_st;
	struct sg_request **rapp;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_device *sh_sdp;
	struct sg_fd *sh_sfp;
	struct sg_request *rsv_srp = NULL;
	struct sg_request *ws_srp;
	struct xarray *xadp = &sdp->sfp_arr;
	struct xarray *xafp = &sfp->srp_arr;

	SG_LOG(3, sfp, "%s: sfp=%pK %s\n", __func__, sfp,
	       (is_rd_side ? "read-side" : "write-side"));
	xa_lock_irqsave(xadp, iflags);
	retry_count = 0;
try_again:
	if (is_rd_side && !xa_get_mark(xadp, sfp->idx, SG_XA_FD_RS_SHARE))
		goto fini;
	sh_sfp = sg_fd_share_ptr(sfp);
	if (unlikely(!sh_sfp))
		goto fini;
	sh_sdp = sh_sfp->parentdp;
	if (!xa_trylock(xafp)) {
		/*
		 * The other side of the share might be closing as well, avoid
		 * deadlock. Should clear relatively quickly.
		 */
		xa_unlock_irqrestore(xadp, iflags);
		if (++retry_count > SG_ADD_RQ_MAX_RETRIES) {
			SG_LOG(1, sfp, "%s: retry_count>>\n", __func__);
			return;
		}
		mutex_unlock(&sdp->open_rel_lock);
		cpu_relax();
		mutex_lock(&sdp->open_rel_lock);
		xa_lock_irqsave(xadp, iflags);
		goto try_again;
	}
	/* have acquired xafp lock */
	if (is_rd_side) {
		rapp = sfp->rsv_arr;
		for (k = 0; k < SG_MAX_RSV_REQS; ++k, ++rapp) {
			bool set_inactive = false;

			rsv_srp = *rapp;
			if (IS_ERR_OR_NULL(rsv_srp) ||
			    rsv_srp->sh_var != SG_SHR_RS_RQ)
				continue;
			sr_st = atomic_read(&rsv_srp->rq_st);
			switch (sr_st) {
			case SG_RQ_SHR_SWAP:
				set_inactive = true;
				break;
			case SG_RQ_SHR_IN_WS:
				ws_srp = rsv_srp->sh_srp;
				if (!IS_ERR_OR_NULL(ws_srp) &&
				    !test_bit(SG_FFD_RELEASE,
					      sh_sfp->ffd_bm)) {
					ws_srp->sh_var = SG_SHR_WS_NOT_SRQ;
				}
				rsv_srp->sh_srp = NULL;
				set_inactive = true;
				break;
			default:
				break;
			}
			rsv_srp->sh_var = SG_SHR_NONE;
			if (set_inactive) {
				res = sg_rq_chg_state_ulck(rsv_srp, sr_st, SG_RQ_INACTIVE);
				if (!res)
					atomic_inc(&sfp->inactives);
			}
		}
		if (!xa_get_mark(&sh_sdp->sfp_arr, sh_sfp->idx,
				 SG_XA_FD_FREE) && sg_fd_is_shared(sh_sfp))
			sg_unshare_ws_fd(sh_sfp, sdp != sh_sdp);
		sg_unshare_rs_fd(sfp, false);
	} else {			/* is write-side of share */
		if (!xa_get_mark(&sh_sdp->sfp_arr, sh_sfp->idx,
				 SG_XA_FD_FREE) && sg_fd_is_shared(sh_sfp))
			sg_unshare_rs_fd(sh_sfp, sdp != sh_sdp);
		sg_unshare_ws_fd(sfp, false);
	}
	xa_unlock(xafp);
fini:
	xa_unlock_irqrestore(xadp, iflags);
}

/*
 * Active when writing 1 to ioctl(SG_SET_GET_EXTENDED(CTL_FLAGS(UNSHARE))),
 * writing 0 has no effect. Undoes the configuration that has done by
 * ioctl(SG_SET_GET_EXTENDED(SHARE_FD)).
 */
static void
sg_do_unshare(struct sg_fd *sfp, bool unshare_val)
		__must_hold(sfp->f_mutex)
{
	bool retry, same_sdp_s;
	int retry_count = 0;
	unsigned long iflags;
	struct sg_request *rs_rsv_srp;
	struct sg_fd *rs_sfp;
	struct sg_fd *ws_sfp;
	struct sg_fd *o_sfp = sg_fd_share_ptr(sfp);
	struct sg_device *sdp = sfp->parentdp;
	struct xarray *xadp = &sdp->sfp_arr;

	if (unlikely(!o_sfp)) {
		SG_LOG(1, sfp, "%s: not shared ? ?\n", __func__);
		return;	/* no share to undo */
	}
	if (!unshare_val)
		return;		/* when unshare value is zero, it's a NOP */
	same_sdp_s = (o_sfp && sfp->parentdp == o_sfp->parentdp);
again:
	retry = false;
	if (xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_RS_SHARE)) {
		rs_sfp = sfp;
		ws_sfp = o_sfp;
		rs_rsv_srp = rs_sfp->rsv_arr[0];
		if (!IS_ERR_OR_NULL(rs_rsv_srp) &&
		    rs_rsv_srp->sh_var != SG_SHR_RS_RQ) {
			if (unlikely(!mutex_trylock(&ws_sfp->f_mutex))) {
				if (++retry_count > SG_ADD_RQ_MAX_RETRIES)
					SG_LOG(1, sfp,
					       "%s: cannot get write-side lock\n",
					       __func__);
				else
					retry = true;
				goto fini;
			}
			if (same_sdp_s) {
				xa_lock_irqsave(xadp, iflags);
				/* write-side is 'other' so do first */
				sg_unshare_ws_fd(ws_sfp, false);
				sg_unshare_rs_fd(rs_sfp, false);
				xa_unlock_irqrestore(xadp, iflags);
			} else {
				sg_unshare_ws_fd(ws_sfp, true);
				sg_unshare_rs_fd(rs_sfp, true);
			}
			mutex_unlock(&ws_sfp->f_mutex);
		}
	} else {			/* called on write-side fd */
		rs_sfp = o_sfp;
		ws_sfp = sfp;
		if (unlikely(!mutex_trylock(&rs_sfp->f_mutex))) {
			if (++retry_count > SG_ADD_RQ_MAX_RETRIES)
				SG_LOG(1, sfp, "%s: cannot get read side lock\n",
				       __func__);
			else
				retry = true;
			goto fini;
		}
		rs_rsv_srp = rs_sfp->rsv_arr[0];
		if (!IS_ERR_OR_NULL(rs_rsv_srp) &&
		    rs_rsv_srp->sh_var != SG_SHR_RS_RQ) {
			if (same_sdp_s) {
				xa_lock_irqsave(xadp, iflags);
				/* read-side is 'other' so do first */
				sg_unshare_rs_fd(rs_sfp, false);
				sg_unshare_ws_fd(ws_sfp, false);
				xa_unlock_irqrestore(xadp, iflags);
			} else {
				sg_unshare_rs_fd(rs_sfp, true);
				sg_unshare_ws_fd(ws_sfp, true);
			}
		}
		mutex_unlock(&rs_sfp->f_mutex);
	}
fini:
	if (unlikely(retry)) {
		cpu_relax();
		goto again;
	}
}

/*
 * Returns duration since srp->start_ns (using boot time as an epoch). Unit
 * is nanoseconds when time_in_ns==true; else it is in milliseconds.
 * For backward compatibility the duration is placed in a 32 bit unsigned
 * integer. This limits the maximum nanosecond duration that can be
 * represented (without wrapping) to about 4.3 seconds. If that is exceeded
 * return equivalent of 3.999.. secs as it is more eye catching than the real
 * number. Negative durations should not be possible but if they occur set
 * duration to an unlikely 2 nanosec. Stalls in a request setup will have
 * ts0==S64_MAX and will return 1 for an unlikely 1 nanosecond duration.
 */
static u32
sg_calc_rq_dur(const struct sg_request *srp, bool time_in_ns)
{
	ktime_t ts0 = ns_to_ktime(srp->start_ns);
	ktime_t now_ts;
	s64 diff;

	if (ts0 == 0)	/* only when SG_FFD_NO_DURATION is set */
		return 0;
	if (unlikely(ts0 == S64_MAX))	/* _prior_ to issuing req */
		return time_in_ns ? 1 : 999999999;
	now_ts = ktime_get_boottime();
	if (unlikely(ts0 > now_ts))
		return time_in_ns ? 2 : 999999998;
	if (time_in_ns)
		diff = ktime_to_ns(ktime_sub(now_ts, ts0));
	else	/* unlikely req duration will exceed 2**32 milliseconds */
		diff = ktime_ms_delta(now_ts, ts0);
	return (diff > (s64)U32_MAX) ? 3999999999U : (u32)diff;
}

static u32
sg_get_dur(struct sg_request *srp, const enum sg_rq_state *sr_stp,
	   bool time_in_ns, bool *is_durp)
{
	bool is_dur = false;
	u32 res = U32_MAX;

	switch (sr_stp ? *sr_stp : atomic_read(&srp->rq_st)) {
	case SG_RQ_INFLIGHT:
	case SG_RQ_BUSY:
		res = sg_calc_rq_dur(srp, time_in_ns);
		break;
	case SG_RQ_AWAIT_RCV:
	case SG_RQ_SHR_SWAP:
	case SG_RQ_SHR_IN_WS:
	case SG_RQ_INACTIVE:
		res = srp->duration;
		is_dur = true;	/* completion has occurred, timing finished */
		break;
	default:
		break;
	}
	if (is_durp)
		*is_durp = is_dur;
	return res;
}

static void
sg_fill_request_element(struct sg_fd *sfp, struct sg_request *srp,
			struct sg_req_info *rip)
{
	unsigned long iflags;

	xa_lock_irqsave(&sfp->srp_arr, iflags);
	rip->duration = sg_get_dur(srp, NULL, test_bit(SG_FFD_TIME_IN_NS,
						       sfp->ffd_bm), NULL);
	if (rip->duration == U32_MAX)
		rip->duration = 0;
	rip->orphan = test_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm);
	rip->sg_io_owned = test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm);
	rip->problem = !sg_result_is_good(srp->rq_result);
	rip->pack_id = test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm) ?
				srp->tag : srp->pack_id;
	rip->usr_ptr = SG_IS_V4I(srp) ? uptr64(srp->s_hdr4.usr_ptr)
				      : srp->s_hdr3.usr_ptr;
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
}

static inline bool
sg_rq_landed(struct sg_device *sdp, struct sg_request *srp)
{
	return atomic_read_acquire(&srp->rq_st) != SG_RQ_INFLIGHT || SG_IS_DETACHING(sdp);
}

/* This is a blocking wait then complete for a specific srp. */
static int
sg_wait_event_srp(struct sg_fd *sfp, void __user *p, struct sg_io_v4 *h4p,
		  struct sg_request *srp)
{
	int res;
	struct sg_device *sdp = sfp->parentdp;
	enum sg_rq_state sr_st;

	if (atomic_read(&srp->rq_st) != SG_RQ_INFLIGHT)
		goto skip_wait;		/* and skip _acquire() */
	if (srp->rq_flags & SGV4_FLAG_HIPRI) {
		/* call blk_poll(), spinning till found */
		res = sg_srp_q_blk_poll(srp, sdp->device->request_queue, -1);
		if (res != -ENODATA && unlikely(res < 0))
			return res;
		goto skip_wait;
	}
	SG_LOG(3, sfp, "%s: about to wait_event...()\n", __func__);
	/* N.B. The SG_FFD_EXCL_WAITQ flag is ignored here. */
	res = __wait_event_interruptible(sfp->cmpl_wait,
					 sg_rq_landed(sdp, srp));
	if (unlikely(res)) { /* -ERESTARTSYS because signal hit thread */
		set_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm);
		/* orphans harvested when sfp->keep_orphan is false */
		sg_rq_chg_state_force(srp, SG_RQ_INFLIGHT);
		SG_LOG(1, sfp, "%s:  wait_event_interruptible(): %s[%d]\n",
		       __func__, (res == -ERESTARTSYS ? "ERESTARTSYS" : ""),
		       res);
		return res;
	}
skip_wait:
	if (SG_IS_DETACHING(sdp)) {
		sg_rq_chg_state_force(srp, SG_RQ_INACTIVE);
		atomic_inc(&sfp->inactives);
		return -ENODEV;
	}
	sr_st = atomic_read(&srp->rq_st);
	if (unlikely(sr_st != SG_RQ_AWAIT_RCV))
		return -EPROTO;         /* Logic error */
	res = sg_rq_chg_state(srp, sr_st, SG_RQ_BUSY);
	if (unlikely(res)) {
#if IS_ENABLED(SG_LOG_ACTIVE)
		sg_rq_state_fail_msg(sfp, sr_st, SG_RQ_BUSY, __func__);
#endif
		return res;
	}
	if (SG_IS_V4I(srp))
		res = sg_receive_v4(sfp, srp, p, h4p);
	else
		res = sg_receive_v3(sfp, srp, p);
	return (res < 0) ? res : 0;
}

/*
 * Handles ioctl(SG_IO) for blocking (sync) usage of v3 or v4 interface.
 * Returns 0 on success else a negated errno.
 */
static int
sg_ctl_sg_io(struct sg_device *sdp, struct sg_fd *sfp, void __user *p)
{
	int res;
	struct sg_request *srp = NULL;
	u8 hu8arr[SZ_SG_IO_V4];
	struct sg_io_hdr *h3p = (struct sg_io_hdr *)hu8arr;
	struct sg_io_v4 *h4p = (struct sg_io_v4 *)hu8arr;

	SG_LOG(3, sfp, "%s:  SG_IO%s\n", __func__,
	       (SG_IS_O_NONBLOCK(sfp) ? " O_NONBLOCK ignored" : ""));
	res = sg_allow_if_err_recovery(sdp, false);
	if (unlikely(res))
		return res;
	if (unlikely(get_sg_io_hdr(h3p, p)))
		return -EFAULT;
	if (h3p->interface_id == 'Q') {
		/* copy in rest of sg_io_v4 object */
		int v3_len;

#ifdef CONFIG_COMPAT
		if (in_compat_syscall())
			v3_len = sizeof(struct compat_sg_io_hdr);
		else
			v3_len = SZ_SG_IO_HDR;
#else
		v3_len = SZ_SG_IO_HDR;
#endif
		if (copy_from_user(hu8arr + v3_len,
				   ((u8 __user *)p) + v3_len,
				   SZ_SG_IO_V4 - v3_len))
			return -EFAULT;
		res = sg_submit_v4(sfp, p, h4p, true, &srp);
	} else if (h3p->interface_id == 'S') {
		res = sg_submit_v3(sfp, h3p, true, &srp);
	} else {
		pr_info_once("sg: %s: v3 or v4 interface only here\n",
			     __func__);
		return -EPERM;
	}
	if (unlikely(res < 0))
		return res;
	if (!srp)	/* mrq case: already processed all responses */
		return res;
	res = sg_wait_event_srp(sfp, p, h4p, srp);
#if IS_ENABLED(SG_LOG_ACTIVE)
	if (unlikely(res))
		SG_LOG(1, sfp, "%s: %s=0x%pK  state: %s, share: %s\n",
		       __func__, "unexpected srp", srp,
		       sg_rq_st_str(atomic_read(&srp->rq_st), false),
		       sg_shr_str(srp->sh_var, false));
#endif
	return res;
}

static inline int
sg_num_waiting_maybe_acquire(struct sg_fd *sfp)
{
	int num = atomic_read(&sfp->waiting);

	if (num < 1)
		num = atomic_read_acquire(&sfp->waiting);
	return num;
}

/*
 * When use_tag is true then id is a tag, else it is a pack_id. Returns
 * valid srp if match, else returns NULL.
 */
static struct sg_request *
sg_match_request(struct sg_fd *sfp, bool use_tag, int id)
{
	unsigned long idx;
	struct sg_request *srp;

	if (sg_num_waiting_maybe_acquire(sfp) < 1)
		return NULL;
	if (id == SG_PACK_ID_WILDCARD) {
		xa_for_each_marked(&sfp->srp_arr, idx, srp, SG_XA_RQ_AWAIT)
			return srp;
	} else if (use_tag) {
		xa_for_each_marked(&sfp->srp_arr, idx, srp, SG_XA_RQ_AWAIT) {
			if (id == srp->tag)
				return srp;
		}
	} else {
		xa_for_each_marked(&sfp->srp_arr, idx, srp, SG_XA_RQ_AWAIT) {
			if (id == srp->pack_id)
				return srp;
		}
	}
	return NULL;
}

/*
 * Looks for first request following 'after_rp' (or the start if after_rp is
 * NULL) whose pack_id_of_mrq matches the given pack_id. If after_rp is
 * non-NULL and it is not found, then the search restarts from the beginning
 * of the list. If no match is found then NULL is returned.
 */
static struct sg_request *
sg_match_first_mrq_after(struct sg_fd *sfp, int pack_id,
			 struct sg_request *after_rp)
{
	bool found = false;
	bool look_for_after = after_rp ? true : false;
	int id;
	unsigned long idx;
	struct sg_request *srp;

	if (sg_num_waiting_maybe_acquire(sfp) < 1)
		return NULL;
once_more:
	xa_for_each_marked(&sfp->srp_arr, idx, srp, SG_XA_RQ_AWAIT) {
		if (look_for_after) {
			if (after_rp == srp)
				look_for_after = false;
			continue;
		}
		id = atomic_read(&srp->s_hdr4.pack_id_of_mrq);
		if (id == 0)	/* mrq_pack_ids cannot be zero */
			continue;
		if (pack_id == SG_PACK_ID_WILDCARD || pack_id == id) {
			found = true;
			break;
		}
	}
	if (look_for_after) {	/* after_rp may now be on free list */
		look_for_after = false;
		goto once_more;
	}
	return found ? srp : NULL;
}

static int
sg_abort_req(struct sg_fd *sfp, struct sg_request *srp)
		__must_hold(&sfp->srp_arr->xa_lock)
{
	int res = 0;
	enum sg_rq_state rq_st;
	struct request *rqq;

	if (test_and_set_bit(SG_FRQ_ABORTING, srp->frq_bm)) {
		SG_LOG(1, sfp, "%s: already aborting req pack_id/tag=%d/%d\n",
		       __func__, srp->pack_id, srp->tag);
		goto fini;	/* skip quietly if already aborted */
	}
	rq_st = atomic_read(&srp->rq_st);
	SG_LOG(3, sfp, "%s: req pack_id/tag=%d/%d, status=%s\n", __func__,
	       srp->pack_id, srp->tag, sg_rq_st_str(rq_st, false));
	switch (rq_st) {
	case SG_RQ_BUSY:
		clear_bit(SG_FRQ_ABORTING, srp->frq_bm);
		res = -EBUSY;	/* should not occur often */
		break;
	case SG_RQ_INACTIVE:	/* perhaps done already */
		clear_bit(SG_FRQ_ABORTING, srp->frq_bm);
		break;
	case SG_RQ_AWAIT_RCV:	/* user should still do completion */
	case SG_RQ_SHR_SWAP:
	case SG_RQ_SHR_IN_WS:
		clear_bit(SG_FRQ_ABORTING, srp->frq_bm);
		break;		/* nothing to do here, return 0 */
	case SG_RQ_INFLIGHT:	/* only attempt abort if inflight */
		srp->rq_result |= (DRIVER_SOFT << 24);
		rqq = READ_ONCE(srp->rqq);
		if (likely(rqq)) {
			SG_LOG(5, sfp, "%s: -->blk_abort_request srp=0x%pK\n",
			       __func__, srp);
			blk_abort_request(rqq);
		}
		break;
	default:
		clear_bit(SG_FRQ_ABORTING, srp->frq_bm);
		break;
	}
fini:
	return res;
}

/* Holding xa_lock_irq(&sfp->srp_arr) */
static int
sg_mrq_abort_inflight(struct sg_fd *sfp, int pack_id)
{
	bool got_ebusy = false;
	int res = 0;
	struct sg_request *srp;
	struct sg_request *prev_srp;

	for (prev_srp = NULL; true; prev_srp = srp) {
		srp = sg_match_first_mrq_after(sfp, pack_id, prev_srp);
		if (!srp)
			break;
		res = sg_abort_req(sfp, srp);
		if (res == -EBUSY)	/* check rest of active list */
			got_ebusy = true;
		else if (res)
			break;
	}
	if (res)
		return res;
	return got_ebusy ? -EBUSY : 0;
}

/*
 * Implements ioctl(SG_IOABORT) when SGV4_FLAG_MULTIPLE_REQS set. pack_id is
 * non-zero and is from the request_extra field. dev_scope is set when
 * SGV4_FLAG_DEV_SCOPE is given; in that case there is one level of recursion
 * if there is no match or clash with given sfp. Will abort the first
 * mrq that matches then exit. Can only do mrq abort if the mrq submission
 * used a non-zero ctl_obj.request_extra (pack_id).
 */
static int
sg_mrq_abort(struct sg_fd *sfp, int pack_id, bool dev_scope)
		__must_hold(sfp->f_mutex)
{
	int existing_id;
	int res = 0;
	unsigned long idx, iflags;
	struct sg_device *sdp;
	struct sg_fd *o_sfp;
	struct sg_fd *s_sfp;

	if (pack_id != SG_PACK_ID_WILDCARD)
		SG_LOG(3, sfp, "%s: pack_id=%d, dev_scope=%s\n", __func__,
		       pack_id, (dev_scope ? "true" : "false"));
	existing_id = atomic_read(&sfp->mrq_id_abort);
	if (existing_id == 0) {
		if (dev_scope)
			goto check_whole_dev;
		SG_LOG(1, sfp, "%s: sfp->mrq_id_abort is 0, nothing to do\n",
		       __func__);
		return -EADDRNOTAVAIL;
	}
	if (pack_id == SG_PACK_ID_WILDCARD) {
		pack_id = existing_id;
		SG_LOG(3, sfp, "%s: wildcard becomes pack_id=%d\n", __func__,
		       pack_id);
	} else if (pack_id != existing_id) {
		if (dev_scope)
			goto check_whole_dev;
		SG_LOG(1, sfp, "%s: want id=%d, got sfp->mrq_id_abort=%d\n",
		       __func__, pack_id, existing_id);
		return -EADDRINUSE;
	}
	if (test_and_set_bit(SG_FFD_MRQ_ABORT, sfp->ffd_bm))
		SG_LOG(2, sfp, "%s: repeated SG_IOABORT on mrq_id=%d\n",
		       __func__, pack_id);

	/* now look for inflight requests matching that mrq pack_id */
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	res = sg_mrq_abort_inflight(sfp, pack_id);
	if (res == -EBUSY) {
		res = sg_mrq_abort_inflight(sfp, pack_id);
		if (res)
			goto fini;
	}
	s_sfp = sg_fd_share_ptr(sfp);
	if (s_sfp) {	/* SGV4_FLAG_DO_ON_OTHER possible */
		xa_unlock_irqrestore(&sfp->srp_arr, iflags);
		sfp = s_sfp;	/* if share, switch to other fd */
		xa_lock_irqsave(&sfp->srp_arr, iflags);
		if (!sg_fd_is_shared(sfp))
			goto fini;
		/* tough luck if other fd used same mrq pack_id */
		res = sg_mrq_abort_inflight(sfp, pack_id);
		if (res == -EBUSY)
			res = sg_mrq_abort_inflight(sfp, pack_id);
	}
fini:
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
	return res;

check_whole_dev:
	res = -ENODATA;
	sdp = sfp->parentdp;
	xa_for_each(&sdp->sfp_arr, idx, o_sfp) {
		if (o_sfp == sfp)
			continue;       /* already checked */
		mutex_lock(&o_sfp->f_mutex);
		/* recurse, dev_scope==false is stopping condition */
		res = sg_mrq_abort(o_sfp, pack_id, false);
		mutex_unlock(&o_sfp->f_mutex);
		if (res == 0)
			break;
	}
	return res;
}

/*
 * Tries to abort an inflight request/command. First it checks the current fd
 * for a match on pack_id or tag. If there is a match, aborts that match.
 * Otherwise, if SGV4_FLAG_DEV_SCOPE is set, the rest of the file descriptors
 * belonging to the current device are similarly checked. If there is no match
 * then -ENODATA is returned.
 */
static int
sg_ctl_abort(struct sg_device *sdp, struct sg_fd *sfp, void __user *p)
		__must_hold(sfp->f_mutex)
{
	bool use_tag, dev_scope;
	int pack_id, id;
	int res = 0;
	unsigned long iflags, idx;
	struct sg_fd *o_sfp;
	struct sg_request *srp;
	struct sg_io_v4 io_v4;
	struct sg_io_v4 *h4p = &io_v4;

	if (copy_from_user(h4p, p, SZ_SG_IO_V4))
		return -EFAULT;
	if (h4p->guard != 'Q' || h4p->protocol != 0 || h4p->subprotocol != 0)
		return -EPERM;
	dev_scope = !!(h4p->flags & SGV4_FLAG_DEV_SCOPE);
	pack_id = h4p->request_extra;
	if (h4p->flags & SGV4_FLAG_MULTIPLE_REQS) {
		if (pack_id == 0)
			return -ENOSTR;
		res = sg_mrq_abort(sfp, pack_id, dev_scope);
		return res;
	}
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	use_tag = test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm);
	id = use_tag ? (int)h4p->request_tag : pack_id;

	srp = sg_match_request(sfp, use_tag, id);
	if (!srp) {	/* assume device (not just fd) scope */
		xa_unlock_irqrestore(&sfp->srp_arr, iflags);
		if (!dev_scope)
			return -ENODATA;
		xa_for_each(&sdp->sfp_arr, idx, o_sfp) {
			if (o_sfp == sfp)
				continue;	/* already checked */
			srp = sg_match_request(o_sfp, use_tag, id);
			if (srp) {
				sfp = o_sfp;
				xa_lock_irqsave(&sfp->srp_arr, iflags);
				break;
			}
		}
		if (!srp)
			return -ENODATA;
	}
	res = sg_abort_req(sfp, srp);
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
	return res;
}

/*
 * Check if search_for is a "char" device fd whose MAJOR is this driver.
 * If so filp->private_data must be the sfp we are looking for. Do further
 * checks (e.g. not already in a file share). If all is well set up cross
 * references and adjust xarray marks. Returns a sfp or negative errno
 * twisted by ERR_PTR().
 */
static struct sg_fd *
sg_find_sfp_by_fd(const struct file *search_for, struct sg_fd *from_sfp,
		  bool is_reshare)
		__must_hold(&from_sfp->f_mutex)
{
	int res = 0;
	unsigned long iflags;
	struct sg_fd *sfp;
	struct sg_device *from_sdp = from_sfp->parentdp;
	struct sg_device *sdp;

	SG_LOG(6, from_sfp, "%s: enter,  from_sfp=%pK search_for=%pK\n",
	       __func__, from_sfp, search_for);
	if (!(S_ISCHR(search_for->f_inode->i_mode) &&
	      MAJOR(search_for->f_inode->i_rdev) == SCSI_GENERIC_MAJOR))
		return ERR_PTR(-EBADF);
	sfp = search_for->private_data;
	if (!sfp)
		return ERR_PTR(-ENXIO);
	sdp = sfp->parentdp;
	if (!sdp)
		return ERR_PTR(-ENXIO);
	if (unlikely(!mutex_trylock(&sfp->f_mutex)))
		return ERR_PTR(-EPROBE_DEFER);	/* suggest re-invocation */
	if (unlikely(sg_fd_is_shared(sfp)))
		res = -EADDRNOTAVAIL;
	else if (unlikely(SG_HAVE_EXCLUDE(sdp)))
		res = -EPERM;
	if (res) {
		mutex_unlock(&sfp->f_mutex);
		return ERR_PTR(res);
	}

	xa_lock_irqsave(&from_sdp->sfp_arr, iflags);
	rcu_assign_pointer(from_sfp->share_sfp, sfp);
	__xa_clear_mark(&from_sdp->sfp_arr, from_sfp->idx, SG_XA_FD_UNSHARED);
	if (is_reshare)	/* reshare case: no kref_get() on read-side */
		__xa_set_mark(&from_sdp->sfp_arr, from_sfp->idx,
			      SG_XA_FD_RS_SHARE);
	else
		kref_get(&from_sfp->f_ref);  /* undone: sg_unshare_*_fd() */
	if (from_sdp != sdp) {
		xa_unlock_irqrestore(&from_sdp->sfp_arr, iflags);
		xa_lock_irqsave(&sdp->sfp_arr, iflags);
	}
	mutex_unlock(&sfp->f_mutex);
	rcu_assign_pointer(sfp->share_sfp, from_sfp);
	__xa_clear_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_UNSHARED);
	if (!is_reshare)
		__xa_set_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_RS_SHARE);
	kref_get(&sfp->f_ref);		/* undone: sg_unshare_*_fd() */
	xa_unlock_irqrestore(&sdp->sfp_arr, iflags);

	return sfp;
}

/*
 * After checking the proposed read-side/write-side relationship is unique and valid,
 * sets up pointers between read-side and write-side sg_fd objects. Returns 0 on
 * success or negated errno value. From ioctl(EXTENDED(SG_SEIM_SHARE_FD)).
 */
static int
sg_fd_share(struct sg_fd *ws_sfp, int m_fd)
		__must_hold(&ws_sfp->f_mutex)
{
	bool found = false;
	int res = 0;
	struct file *filp;
	struct sg_fd *rs_sfp;

	SG_LOG(3, ws_sfp, "%s:  SHARE: read-side fd: %d\n", __func__, m_fd);
	if (unlikely(!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO)))
		return -EACCES;
	if (unlikely(m_fd < 0))
		return -EBADF;

	if (unlikely(sg_fd_is_shared(ws_sfp)))
		return -EADDRINUSE;  /* don't allow chain of shares */
	/* Alternate approach: fcheck_files(current->files, m_fd) */
	filp = fget(m_fd);
	if (unlikely(!filp))
		return -ENOENT;
	if (unlikely(ws_sfp->filp == filp)) {/* share with self is confusing */
		res = -ELOOP;
		goto fini;
	}
	SG_LOG(6, ws_sfp, "%s: read-side fd okay, scan for filp=0x%pK\n",
	       __func__, filp);
	rs_sfp = sg_find_sfp_by_fd(filp, ws_sfp, false);
	if (!IS_ERR(rs_sfp))
		found = !!rs_sfp;
fini:
	/* paired with filp=fget(m_fd) above */
	fput(filp);
	if (unlikely(res))
		return res;
	return found ? 0 : -ENOTSOCK; /* ENOTSOCK for fd exists but not sg */
}

/*
 * After checking the proposed file share relationship is unique and
 * valid, sets up pointers between read-side and write-side sg_fd objects.
 * Allows previous write-side to be the same as the new new_ws_fd .
 */
static int
sg_fd_reshare(struct sg_fd *rs_sfp, int new_ws_fd)
		__must_hold(&rs_sfp->f_mutex)
{
	bool found = false;
	int res = 0;
	struct file *filp;
	struct sg_fd *ws_sfp = sg_fd_share_ptr(rs_sfp);

	SG_LOG(3, ws_sfp, "%s:  new_write_side_fd: %d\n", __func__, new_ws_fd);
	if (unlikely(!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO)))
		return -EACCES;
	if (unlikely(new_ws_fd < 0))
		return -EBADF;
	if (unlikely(!xa_get_mark(&rs_sfp->parentdp->sfp_arr, rs_sfp->idx,
				  SG_XA_FD_RS_SHARE)))
		res = -EINVAL;	/* invalid unless prev_sl==new_sl */

	/* Alternate approach: fcheck_files(current->files, m_fd) */
	filp = fget(new_ws_fd);
	if (unlikely(!filp))
		return -ENOENT;
	if (unlikely(rs_sfp->filp == filp)) {
		res = -ELOOP;	/* share with self is confusing */
		goto fini;
	}
	if (res == -EINVAL) {
		if (ws_sfp && ws_sfp->filp == filp) {
			found = true;
			res = 0;	/* prev_sl==new_sl is okay */
		}	/* else it is invalid and res is still -EINVAL */
		goto fini;
	}
	SG_LOG(6, ws_sfp, "%s: write-side fd ok, scan for filp=0x%pK\n", __func__,
	       filp);
	sg_unshare_ws_fd(ws_sfp, true);
	ws_sfp = sg_find_sfp_by_fd(filp, rs_sfp, true);
	if (!IS_ERR(ws_sfp))
		found = !!ws_sfp;
fini:
	/* fput() paired with filp=fget(new_ws_fd) above */
	fput(filp);
	if (unlikely(res))
		return res;
	if (found) {	/* can only reshare rsv_arr[0] */
		struct sg_request *rs_srp = rs_sfp->rsv_arr[0];

		if (!IS_ERR_OR_NULL(rs_srp))
			rs_srp->sh_srp = NULL;
		set_bit(SG_FFD_RESHARE, rs_sfp->ffd_bm);
	}
	return found ? 0 : -ENOTSOCK; /* ENOTSOCK for fd exists but not sg */
}

static int
sg_eventfd_new(struct sg_fd *rs_sfp, int eventfd)
		__must_hold(&rs_sfp->f_mutex)
{
	int ret = 0;

	if (rs_sfp->efd_ctxp)
		return -EBUSY;
	rs_sfp->efd_ctxp = eventfd_ctx_fdget(eventfd);
	if (IS_ERR(rs_sfp->efd_ctxp)) {
		ret = PTR_ERR(rs_sfp->efd_ctxp);
		rs_sfp->efd_ctxp = NULL;
		return ret;
	}
	return ret;
}

/*
 * First normalize want_rsv_sz to be >= sfp->sgat_elem_sz and
 * <= max_segment_size. Exit if that is the same as old size; otherwise
 * create a new sg_scatter_hold object and swap it with existing reserve
 * request's sg_scatter_hold object. Only modify first reserver request.
 */
static int
sg_set_reserved_sz(struct sg_fd *sfp, int want_rsv_sz)
		__must_hold(sfp->f_mutex)
{
	int new_sz, blen, res;
	unsigned long iflags;
	struct sg_scatter_hold n_schp, o_schp;
	struct sg_request *srp = sfp->rsv_arr[0];
	struct xarray *xafp = &sfp->srp_arr;

	if (unlikely(sg_fd_is_shared(sfp)))
		return -EBUSY;	/* this fd can't be either side of share */
	if (unlikely(!srp))
		return -EPROTO;
	if (unlikely(SG_RQ_ACTIVE(srp) || sfp->mmap_sz > 0))
		return -EBUSY;
	new_sz = min_t(int, want_rsv_sz, sfp->parentdp->max_sgat_sz);
	new_sz = max_t(int, new_sz, sfp->sgat_elem_sz);
	blen = srp->sgat_h.buflen;
	SG_LOG(3, sfp, "%s: was=%d, ask=%d, new=%d (sgat_elem_sz=%d)\n",
	       __func__, blen, want_rsv_sz, new_sz, sfp->sgat_elem_sz);
	if (blen == new_sz)
		return 0;
	res = sg_mk_sgat(&n_schp, sfp, new_sz);
	if (unlikely(res))
		return res;

	xa_lock_irqsave(xafp, iflags);
	/* (ugly) structured assignment swap */
	o_schp = srp->sgat_h;
	srp->sgat_h = n_schp;
	xa_unlock_irqrestore(xafp, iflags);
	sg_remove_sgat(sfp, &o_schp);
	return 0;
}

#ifdef CONFIG_COMPAT
struct compat_sg_req_info { /* used by SG_GET_REQUEST_TABLE ioctl() */
	char req_state;
	char orphan;
	char sg_io_owned;
	char problem;
	int pack_id;
	compat_uptr_t usr_ptr;
	unsigned int duration;
	int unused;
};

static int put_compat_request_table(struct compat_sg_req_info __user *o,
				    struct sg_req_info *rinfo)
{
	int i;
	for (i = 0; i < SG_MAX_QUEUE; i++) {
		if (copy_to_user(o + i, rinfo + i, offsetof(sg_req_info_t, usr_ptr)) ||
		    put_user((uintptr_t)rinfo[i].usr_ptr, &o[i].usr_ptr) ||
		    put_user(rinfo[i].duration, &o[i].duration) ||
		    put_user(rinfo[i].unused, &o[i].unused))
			return -EFAULT;
	}
	return 0;
}
#endif

static bool
sg_any_persistent_orphans(struct sg_fd *sfp)
{
	if (test_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm)) {
		unsigned long idx;
		struct sg_request *srp;
		struct xarray *xafp = &sfp->srp_arr;

		if (sg_num_waiting_maybe_acquire(sfp) < 1)
			return false;
		xa_for_each_marked(xafp, idx, srp, SG_XA_RQ_AWAIT) {
			if (test_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm))
				return true;
		}
	}
	return false;
}

/*
 * Will clear_first if size already over half of available buffer.
 *
 * N.B. This function is a useful debug aid to be called inline with its
 * output going to /sys/kernel/debug/scsi_generic/snapped for later
 * examination. Best to call it with no locks held and that implies that
 * the driver state may change while it is processing. Interpret the
 * result with this in mind.
 */
static void
sg_take_snap(struct sg_fd *sfp, bool clear_first)
{
	u32 hour, minute, second;
	u64 n;
	struct sg_device *sdp = sfp->parentdp;
	struct timespec64 ts64;
	char b[64];

	if (!sdp)
		return;
	ktime_get_real_ts64(&ts64);
	/* prefer local time but sys_tz.tz_minuteswest is always 0 */
	n = ts64.tv_sec;
	second = (u32)do_div(n, 60);
	minute = (u32)do_div(n, 60);
	hour = (u32)do_div(n, 24);	/* hour within a UTC day */
	snprintf(b, sizeof(b), "UTC time: %.2u:%.2u:%.2u:%.6u [tid=%d]",
		 hour, minute, second, (u32)ts64.tv_nsec / 1000,
		 (current ? current->pid : -1));
	mutex_lock(&snapped_mutex);
	if (!snapped_buf) {
		snapped_buf = kzalloc(SG_SNAP_BUFF_SZ,
				      GFP_KERNEL | __GFP_NOWARN);
		if (!snapped_buf)
			goto fini;
	} else if (clear_first) {
		memset(snapped_buf, 0, SG_SNAP_BUFF_SZ);
	}
#if IS_ENABLED(SG_PROC_OR_DEBUG_FS)
	if (true) {	/* for some declarations */
		int prevlen, bp_len;
		char *bp;

		prevlen = strlen(snapped_buf);
		if (prevlen > SG_SNAP_BUFF_SZ / 2)
			prevlen = 0;
		bp_len = SG_SNAP_BUFF_SZ - prevlen;
		bp = snapped_buf + prevlen;
		n = scnprintf(bp, bp_len, "%s\n", b);
		bp += n;
		bp_len -= n;
		if (bp_len < 2)
			goto fini;
		n = sg_proc_debug_sdev(sdp, bp, bp_len, NULL, false);
		if (n >= bp_len - 1) {
			if (bp[bp_len - 2] != '\n')
				bp[bp_len - 2] = '\n';
		}
	}
#endif
fini:
	mutex_unlock(&snapped_mutex);
}

/*
 * Processing of ioctl(SG_SET_GET_EXTENDED(SG_SEIM_CTL_FLAGS)) which is a set
 * of boolean flags. Access abbreviations: [rw], read-write; [ro], read-only;
 * [wo], write-only; [raw], read after write; [rbw], read before write.
 */
static int
sg_extended_bool_flags(struct sg_fd *sfp, struct sg_extended_info *seip)
{
	bool flg = false;
	int res = 0;
	const u32 c_flgs_wm = seip->ctl_flags_wr_mask;
	const u32 c_flgs_rm = seip->ctl_flags_rd_mask;
	const u32 c_flgs_val_in = seip->ctl_flags;
	u32 c_flgs_val_out = c_flgs_val_in;
	struct sg_device *sdp = sfp->parentdp;

	/* TIME_IN_NS boolean, [raw] time in nanoseconds (def: millisecs) */
	if (c_flgs_wm & SG_CTL_FLAGM_TIME_IN_NS)
		assign_bit(SG_FFD_TIME_IN_NS, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_TIME_IN_NS));
	if (c_flgs_rm & SG_CTL_FLAGM_TIME_IN_NS) {
		if (test_bit(SG_FFD_TIME_IN_NS, sfp->ffd_bm))
			c_flgs_val_out |= SG_CTL_FLAGM_TIME_IN_NS;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_TIME_IN_NS;
	}
	/* TAG_FOR_PACK_ID boolean, [raw] search by tag or pack_id (def) */
	if (c_flgs_wm & SG_CTL_FLAGM_TAG_FOR_PACK_ID)
		assign_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_TAG_FOR_PACK_ID));
	if (c_flgs_rm & SG_CTL_FLAGM_TAG_FOR_PACK_ID) {
		if (test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm))
			c_flgs_val_out |= SG_CTL_FLAGM_TAG_FOR_PACK_ID;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_TAG_FOR_PACK_ID;
	}
	/* ORPHANS boolean, [ro] does this fd have any orphan requests? */
	if (c_flgs_rm & SG_CTL_FLAGM_ORPHANS) {
		if (sg_any_persistent_orphans(sfp))
			c_flgs_val_out |= SG_CTL_FLAGM_ORPHANS;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_ORPHANS;
	}
	/* OTHER_OPENS boolean, [ro] any other sg open fds on this dev? */
	if (c_flgs_rm & SG_CTL_FLAGM_OTHER_OPENS) {
		if (atomic_read(&sdp->open_cnt) > 1)
			c_flgs_val_out |= SG_CTL_FLAGM_OTHER_OPENS;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_OTHER_OPENS;
	}
	/* Q_TAIL boolean, [raw] 1: queue at tail; 0: head (def: depends) */
	if (c_flgs_wm & SG_CTL_FLAGM_Q_TAIL)
		assign_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_Q_TAIL));
	if (c_flgs_rm & SG_CTL_FLAGM_Q_TAIL) {
		if (test_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm))
			c_flgs_val_out |= SG_CTL_FLAGM_Q_TAIL;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_Q_TAIL;
	}
	/*
	 * UNSHARE boolean: when reading yields zero. When writing true,
	 * unshares this fd from a previously established fd share. If
	 * a shared commands is inflight, waits a little while for it
	 * to finish.
	 */
	if (c_flgs_wm & SG_CTL_FLAGM_UNSHARE) {
		mutex_lock(&sfp->f_mutex);
		sg_do_unshare(sfp, !!(c_flgs_val_in & SG_CTL_FLAGM_UNSHARE));
		mutex_unlock(&sfp->f_mutex);
	}
	if (c_flgs_rm & SG_CTL_FLAGM_UNSHARE)
		c_flgs_val_out &= ~SG_CTL_FLAGM_UNSHARE;	/* clear bit */
	/* IS_SHARE boolean: [ro] true if fd may be read-side or write-side share */
	if (c_flgs_rm & SG_CTL_FLAGM_IS_SHARE) {
		if (sg_fd_is_shared(sfp))
			c_flgs_val_out |= SG_CTL_FLAGM_IS_SHARE;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_IS_SHARE;
	}
	/* IS_READ_SIDE boolean: [ro] true if this fd may be a read-side share */
	if (c_flgs_rm & SG_CTL_FLAGM_IS_READ_SIDE) {
		if (xa_get_mark(&sdp->sfp_arr, sfp->idx, SG_XA_FD_RS_SHARE))
			c_flgs_val_out |= SG_CTL_FLAGM_IS_READ_SIDE;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_IS_READ_SIDE;
	}
	/*
	 * READ_SIDE_FINI boolean, [rbw] should be called by write-side; when
	 * reading: read-side is finished, awaiting action by write-side;
	 * when written: 1 --> write-side doesn't want to continue
	 */
	if ((c_flgs_rm & SG_CTL_FLAGM_READ_SIDE_FINI) && sg_fd_is_shared(sfp)) {
		struct sg_fd *rs_sfp = sg_fd_share_ptr(sfp);

		if (rs_sfp && !IS_ERR_OR_NULL(rs_sfp->rsv_arr[0])) {
			struct sg_request *res_srp = rs_sfp->rsv_arr[0];

			if (atomic_read(&res_srp->rq_st) == SG_RQ_SHR_SWAP)
				c_flgs_val_out |= SG_CTL_FLAGM_READ_SIDE_FINI;
			else
				c_flgs_val_out &= ~SG_CTL_FLAGM_READ_SIDE_FINI;
		} else {
			c_flgs_val_out &= ~SG_CTL_FLAGM_READ_SIDE_FINI;
		}
	}
	if ((c_flgs_wm & SG_CTL_FLAGM_READ_SIDE_FINI) &&
	    (c_flgs_val_in & SG_CTL_FLAGM_READ_SIDE_FINI))
		res = sg_finish_rs_rq(sfp);
	/* READ_SIDE_ERR boolean, [ro] share: read-side finished with error */
	if (c_flgs_rm & SG_CTL_FLAGM_READ_SIDE_ERR) {
		struct sg_fd *rs_sfp = sg_fd_share_ptr(sfp);

		if (rs_sfp && test_bit(SG_FFD_READ_SIDE_ERR, rs_sfp->ffd_bm))
			c_flgs_val_out |= SG_CTL_FLAGM_READ_SIDE_ERR;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_READ_SIDE_ERR;
	}
	/* NO_DURATION boolean, [rbw] */
	if (c_flgs_rm & SG_CTL_FLAGM_NO_DURATION)
		flg = test_bit(SG_FFD_NO_DURATION, sfp->ffd_bm);
	if (c_flgs_wm & SG_CTL_FLAGM_NO_DURATION)
		assign_bit(SG_FFD_NO_DURATION, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_NO_DURATION));
	if (c_flgs_rm & SG_CTL_FLAGM_NO_DURATION) {
		if (flg)
			c_flgs_val_out |= SG_CTL_FLAGM_NO_DURATION;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_NO_DURATION;
	}
	/* MORE_ASYNC boolean, [rbw] */
	if (c_flgs_rm & SG_CTL_FLAGM_MORE_ASYNC)
		flg = test_bit(SG_FFD_MORE_ASYNC, sfp->ffd_bm);
	if (c_flgs_wm & SG_CTL_FLAGM_MORE_ASYNC)
		assign_bit(SG_FFD_MORE_ASYNC, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_MORE_ASYNC));
	if (c_flgs_rm & SG_CTL_FLAGM_MORE_ASYNC) {
		if (flg)
			c_flgs_val_out |= SG_CTL_FLAGM_MORE_ASYNC;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_MORE_ASYNC;
	}
	/* EXCL_WAITQ boolean, [rbw] */
	if (c_flgs_rm & SG_CTL_FLAGM_EXCL_WAITQ)
		flg = test_bit(SG_FFD_EXCL_WAITQ, sfp->ffd_bm);
	if (c_flgs_wm & SG_CTL_FLAGM_EXCL_WAITQ)
		assign_bit(SG_FFD_EXCL_WAITQ, sfp->ffd_bm,
			   !!(c_flgs_val_in & SG_CTL_FLAGM_EXCL_WAITQ));
	if (c_flgs_rm & SG_CTL_FLAGM_EXCL_WAITQ) {
		if (flg)
			c_flgs_val_out |= SG_CTL_FLAGM_EXCL_WAITQ;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_EXCL_WAITQ;
	}
	/* SNAP_DEV boolean, [rbw] */
	if (c_flgs_rm & SG_CTL_FLAGM_SNAP_DEV) {
		mutex_lock(&snapped_mutex);
		flg = (snapped_buf && strlen(snapped_buf) > 0);
		mutex_unlock(&snapped_mutex);
	}
	if (c_flgs_wm & SG_CTL_FLAGM_SNAP_DEV)
		sg_take_snap(sfp, !!(c_flgs_val_in & SG_CTL_FLAGM_SNAP_DEV));
	if (c_flgs_rm & SG_CTL_FLAGM_SNAP_DEV) {
		if (flg)
			c_flgs_val_out |= SG_CTL_FLAGM_SNAP_DEV;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_SNAP_DEV;
	}
	/* RM_EVENTFD boolean, [rbw] */
	if (c_flgs_rm & SG_CTL_FLAGM_RM_EVENTFD)
		flg = !!sfp->efd_ctxp;
	if ((c_flgs_wm & SG_CTL_FLAGM_RM_EVENTFD) && (c_flgs_val_in & SG_CTL_FLAGM_RM_EVENTFD)) {
		if (sfp->efd_ctxp && atomic_read(&sfp->submitted) < 1) {
			eventfd_ctx_put(sfp->efd_ctxp);
			sfp->efd_ctxp = NULL;
		}
	}
	if (c_flgs_rm & SG_CTL_FLAGM_RM_EVENTFD) {
		if (flg)
			c_flgs_val_out |= SG_CTL_FLAGM_RM_EVENTFD;
		else
			c_flgs_val_out &= ~SG_CTL_FLAGM_RM_EVENTFD;
	}

	if (c_flgs_val_in != c_flgs_val_out)
		seip->ctl_flags = c_flgs_val_out;
	return res;
}

static void
sg_extended_read_value(struct sg_fd *sfp, struct sg_extended_info *seip)
{
	u32 uv;
	unsigned long idx, idx2;
	struct sg_fd *a_sfp;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_request *srp;

	switch (seip->read_value) {
	case SG_SEIRV_INT_MASK:
		seip->read_value = SG_SEIM_ALL_BITS;
		break;
	case SG_SEIRV_BOOL_MASK:
		seip->read_value = SG_CTL_FLAGM_ALL_BITS;
		break;
	case SG_SEIRV_VERS_NUM:
		seip->read_value = sg_version_num;
		break;
	case SG_SEIRV_INACT_RQS:
		uv = 0;
		xa_for_each_marked(&sfp->srp_arr, idx, srp,
				   SG_XA_RQ_INACTIVE)
			++uv;
		seip->read_value = uv;
		break;
	case SG_SEIRV_DEV_INACT_RQS:
		uv = 0;
		xa_for_each(&sdp->sfp_arr, idx2, a_sfp) {
			xa_for_each_marked(&a_sfp->srp_arr, idx, srp,
					   SG_XA_RQ_INACTIVE)
				++uv;
		}
		seip->read_value = uv;
		break;
	case SG_SEIRV_SUBMITTED:  /* counts all non-blocking on active list */
		seip->read_value = (u32)atomic_read(&sfp->submitted);
		break;
	case SG_SEIRV_DEV_SUBMITTED: /* sum(submitted) on all fd's siblings */
		uv = 0;
		xa_for_each(&sdp->sfp_arr, idx2, a_sfp)
			uv += (u32)atomic_read(&a_sfp->submitted);
		seip->read_value = uv;
		break;
	case SG_SEIRV_MAX_RSV_REQS:
		seip->read_value = SG_MAX_RSV_REQS;
		break;
	case SG_SEIRV_DEV_TS_LOWER:	/* timestamp is 64 bits */
		seip->read_value = sfp->parentdp->create_ns & U32_MAX;
		break;
	case SG_SEIRV_DEV_TS_UPPER:
		seip->read_value = (sfp->parentdp->create_ns >> 32) & U32_MAX;
		break;
	default:
		SG_LOG(6, sfp, "%s: can't decode %d --> read_value\n",
		       __func__, seip->read_value);
		seip->read_value = 0;
		break;
	}
}

/* Called when processing ioctl(SG_SET_GET_EXTENDED) */
static int
sg_ctl_extended(struct sg_fd *sfp, void __user *p)
{
	int result = 0;
	int ret = 0;
	int n, j, s_wr_mask, s_rd_mask;
	u32 uv, or_masks;
	struct sg_device *sdp = sfp->parentdp;
	struct sg_extended_info *seip;
	struct sg_extended_info sei;

	seip = &sei;
	if (copy_from_user(seip, p, SZ_SG_EXTENDED_INFO))
		return -EFAULT;
	s_wr_mask = seip->sei_wr_mask;
	s_rd_mask = seip->sei_rd_mask;
	or_masks = s_wr_mask | s_rd_mask;
	if (unlikely(or_masks == 0)) {
		SG_LOG(2, sfp, "%s: both masks 0, do nothing\n", __func__);
		return 0;
	}
	SG_LOG(3, sfp, "%s: wr_mask=0x%x rd_mask=0x%x\n", __func__, s_wr_mask,
	       s_rd_mask);
	/* tot_fd_thresh (u32), [rbw] [limit for sum of active cmd dlen_s] */
	if (or_masks & SG_SEIM_TOT_FD_THRESH) {
		u32 hold = sfp->tot_fd_thresh;

		if (s_wr_mask & SG_SEIM_TOT_FD_THRESH) {
			uv = seip->tot_fd_thresh;
			if (uv > 0 && uv < PAGE_SIZE)
				uv = PAGE_SIZE;
			sfp->tot_fd_thresh = uv;
		}
		if (s_rd_mask & SG_SEIM_TOT_FD_THRESH)
			seip->tot_fd_thresh = hold;
	}
	/* check all boolean flags for either wr or rd mask set in or_mask */
	if (or_masks & SG_SEIM_CTL_FLAGS) {
		result = sg_extended_bool_flags(sfp, seip);
		if (ret == 0 && unlikely(result))
			ret = result;
	}
	/* yields minor_index (type: u32) [ro] */
	if (or_masks & SG_SEIM_MINOR_INDEX) {
		if (s_wr_mask & SG_SEIM_MINOR_INDEX) {
			SG_LOG(2, sfp, "%s: writing to minor_index ignored\n",
			       __func__);
		}
		if (s_rd_mask & SG_SEIM_MINOR_INDEX)
			seip->minor_index = sdp->index;
	}
	if ((s_rd_mask & SG_SEIM_READ_VAL) && (s_wr_mask & SG_SEIM_READ_VAL))
		sg_extended_read_value(sfp, seip);
	/* create share: write-side gives fd of read-side to share with [raw] */
	if (or_masks & SG_SEIM_SHARE_FD) {
		mutex_lock(&sfp->f_mutex);
		if (s_wr_mask & SG_SEIM_SHARE_FD) {
			result = sg_fd_share(sfp, (int)seip->share_fd);
			if (ret == 0 && unlikely(result))
				ret = result;
		}
		/* if share then yield device number of (other) read-side */
		if (s_rd_mask & SG_SEIM_SHARE_FD) {
			struct sg_fd *sh_sfp = sg_fd_share_ptr(sfp);

			seip->share_fd = sh_sfp ? sh_sfp->parentdp->index :
						  U32_MAX;
		}
		mutex_unlock(&sfp->f_mutex);
	}
	/* change_share: read-side is given shr_fd of new write-side [raw] */
	if (or_masks & SG_SEIM_CHG_SHARE_FD) {
		mutex_lock(&sfp->f_mutex);
		if (s_wr_mask & SG_SEIM_CHG_SHARE_FD) {
			result = sg_fd_reshare(sfp, (int)seip->share_fd);
			if (ret == 0 && unlikely(result))
				ret = result;
		}
		/* if share then yield device number of (other) write-side */
		if (s_rd_mask & SG_SEIM_CHG_SHARE_FD) {
			struct sg_fd *sh_sfp = sg_fd_share_ptr(sfp);

			seip->share_fd = sh_sfp ? sh_sfp->parentdp->index :
						  U32_MAX;
		}
		mutex_unlock(&sfp->f_mutex);
	}
	if (or_masks & SG_SEIM_EVENTFD) {
		mutex_lock(&sfp->f_mutex);
		if (s_wr_mask & SG_SEIM_EVENTFD) {
			result = sg_eventfd_new(sfp, (int)seip->share_fd);
			if (ret == 0 && unlikely(result))
				ret = result;
		}
		mutex_unlock(&sfp->f_mutex);
	}
	/* call blk_poll() on this fd's HIPRI requests [raw] */
	if (or_masks & SG_SEIM_BLK_POLL) {
		n = 0;
		if (s_wr_mask & SG_SEIM_BLK_POLL) {
			result = sg_sfp_blk_poll(sfp, seip->num);
			if (result < 0) {
				if (ret == 0)
					ret = result;
			} else {
				n = result;
			}
		}
		if (s_rd_mask & SG_SEIM_BLK_POLL)
			seip->num = n;		/* number completed by LLD */
	}
	/* override scatter gather element size [rbw] (def: SG_SCATTER_SZ) */
	if (or_masks & SG_SEIM_SGAT_ELEM_SZ) {
		n = sfp->sgat_elem_sz;
		if (s_wr_mask & SG_SEIM_SGAT_ELEM_SZ) {
			j = (int)seip->sgat_elem_sz;
			if (!is_power_of_2(j) || j < (int)PAGE_SIZE) {
				SG_LOG(1, sfp, "%s: %s not power of 2, %s\n",
				       __func__, "sgat element size",
				       "or less than PAGE_SIZE");
				ret = -EINVAL;
			} else {
				sfp->sgat_elem_sz = j;
			}
		}
		if (s_rd_mask & SG_SEIM_SGAT_ELEM_SZ)
			seip->sgat_elem_sz = n; /* prior value if rw */
	}
	/* reserved_sz [raw], since may be reduced by other limits */
	if (s_wr_mask & SG_SEIM_RESERVED_SIZE) {
		mutex_lock(&sfp->f_mutex);
		result = sg_set_reserved_sz(sfp, (int)seip->reserved_sz);
		if (ret == 0 && unlikely(result))
			ret = result;
		mutex_unlock(&sfp->f_mutex);
	}
	if (s_rd_mask & SG_SEIM_RESERVED_SIZE) {
		struct sg_request *r_srp = sfp->rsv_arr[0];

		seip->reserved_sz = (u32)min_t(int, r_srp->sgatp->buflen,
					       sdp->max_sgat_sz);
	}
	/* copy to user space if int or boolean read mask non-zero */
	if (s_rd_mask || seip->ctl_flags_rd_mask) {
		if (copy_to_user(p, seip, SZ_SG_EXTENDED_INFO))
			ret = ret ? ret : -EFAULT;
	}
	return ret;
}

/*
 * For backward compatibility, output SG_MAX_QUEUE sg_req_info objects. First
 * fetch from the active list then, if there is still room, from the free
 * list. Some of the trailing elements may be empty which is indicated by all
 * fields being zero. Any requests beyond SG_MAX_QUEUE are ignored.
 */
static int
sg_ctl_req_tbl(struct sg_fd *sfp, void __user *p)
{
	int k, val;
	int result = 0;
	unsigned long idx;
	struct sg_request *srp;
	struct sg_req_info *rinfop;

	SG_LOG(3, sfp, "%s:    SG_GET_REQUEST_TABLE\n", __func__);
	k = SG_MAX_QUEUE;
	rinfop = kcalloc(k, SZ_SG_REQ_INFO, GFP_KERNEL);
	if (unlikely(!rinfop))
		return -ENOMEM;
	val = 0;
	xa_for_each(&sfp->srp_arr, idx, srp) {
		if (unlikely(val >= SG_MAX_QUEUE))
			break;
		if (xa_get_mark(&sfp->srp_arr, idx, SG_XA_RQ_INACTIVE))
			continue;
		sg_fill_request_element(sfp, srp, rinfop + val);
		val++;
	}
	xa_for_each(&sfp->srp_arr, idx, srp) {
		if (unlikely(val >= SG_MAX_QUEUE))
			break;
		if (!xa_get_mark(&sfp->srp_arr, idx, SG_XA_RQ_INACTIVE))
			continue;
		sg_fill_request_element(sfp, srp, rinfop + val);
		val++;
	}
#ifdef CONFIG_COMPAT
	if (in_compat_syscall())
		result = put_compat_request_table(p, rinfop);
	else
		result = copy_to_user(p, rinfop,
				      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#else
	result = copy_to_user(p, rinfop,
			      SZ_SG_REQ_INFO * SG_MAX_QUEUE);
#endif
	kfree(rinfop);
	return result > 0 ? -EFAULT : result;	/* treat short copy as error */
}

static int
sg_ctl_scsi_id(struct scsi_device *sdev, struct sg_fd *sfp, void __user *p)
{
	struct sg_scsi_id ss_id;
	struct scsi_lun lun8b;

	SG_LOG(3, sfp, "%s:    SG_GET_SCSI_ID\n", __func__);
	ss_id.host_no = sdev->host->host_no;
	ss_id.channel = sdev->channel;
	ss_id.scsi_id = sdev->id;
	ss_id.lun = sdev->lun;
	ss_id.scsi_type = sdev->type;
	ss_id.h_cmd_per_lun = sdev->host->cmd_per_lun;
	ss_id.d_queue_depth = sdev->queue_depth;
	int_to_scsilun(sdev->lun, &lun8b);
	/* ss_id.scsi_lun is in an anonymous union with 'int unused[2]' */
	memcpy(ss_id.scsi_lun, lun8b.scsi_lun, 8);
	if (copy_to_user(p, &ss_id, sizeof(struct sg_scsi_id)))
		return -EFAULT;
	return 0;
}

static long
sg_ioctl_common(struct file *filp, struct sg_device *sdp, struct sg_fd *sfp,
		unsigned int cmd_in, void __user *p)
{
	bool read_only = O_RDWR != (filp->f_flags & O_ACCMODE);
	int val;
	int res = 0;
	int __user *ip = p;
	struct sg_request *srp;
	struct scsi_device *sdev;
	unsigned long idx;
	__maybe_unused const char *pmlp = ", pass to mid-level";

	SG_LOG(6, sfp, "%s: cmd=0x%x, O_NONBLOCK=%d%s\n", __func__, cmd_in,
	       !!(filp->f_flags & O_NONBLOCK),
	       (cmd_in == SG_GET_NUM_WAITING ? ", SG_GET_NUM_WAITING" : ""));
	sdev = sdp->device;

	switch (cmd_in) {
	case SG_GET_NUM_WAITING:
		/* Want as fast as possible, with a useful result */
		if (test_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm))
			sg_sfp_blk_poll(sfp, 0);	/* LLD may have some ready */
		val = atomic_read(&sfp->waiting);
		if (val)
			return put_user(val, ip);
		return put_user(atomic_read_acquire(&sfp->waiting), ip);
	case SG_IO:
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return sg_ctl_sg_io(sdp, sfp, p);
	case SG_IOSUBMIT:
		SG_LOG(3, sfp, "%s:    SG_IOSUBMIT\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return sg_ctl_iosubmit(sfp, p);
	case SG_IOSUBMIT_V3:
		SG_LOG(3, sfp, "%s:    SG_IOSUBMIT_V3\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return sg_ctl_iosubmit_v3(sfp, p);
	case SG_IORECEIVE:
		SG_LOG(3, sfp, "%s:    SG_IORECEIVE\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return sg_ctl_ioreceive(sfp, p);
	case SG_IORECEIVE_V3:
		SG_LOG(3, sfp, "%s:    SG_IORECEIVE_V3\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return sg_ctl_ioreceive_v3(sfp, p);
	case SG_IOABORT:
		SG_LOG(3, sfp, "%s:    SG_IOABORT\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		if (unlikely(read_only))
			return -EPERM;
		if (!mutex_trylock(&sfp->f_mutex))
			return -EAGAIN;
		res = sg_ctl_abort(sdp, sfp, p);
		mutex_unlock(&sfp->f_mutex);
		return res;
	case SG_SET_GET_EXTENDED:
		SG_LOG(3, sfp, "%s:    SG_SET_GET_EXTENDED\n", __func__);
		return sg_ctl_extended(sfp, p);
	case SG_GET_SCSI_ID:
		return sg_ctl_scsi_id(sdev, sfp, p);
	case SG_SET_FORCE_PACK_ID:
		SG_LOG(3, sfp, "%s:    SG_SET_FORCE_PACK_ID\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		assign_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm, !!val);
		return 0;
	case SG_GET_PACK_ID:    /* or tag of oldest "read"-able, -1 if none */
		val = -1;
		if (test_bit(SG_FFD_PREFER_TAG, sfp->ffd_bm)) {
			xa_for_each_marked(&sfp->srp_arr, idx, srp,
					   SG_XA_RQ_AWAIT) {
				if (!test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm)) {
					val = srp->tag;
					break;
				}
			}
		} else {
			xa_for_each_marked(&sfp->srp_arr, idx, srp,
					   SG_XA_RQ_AWAIT) {
				if (!test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm)) {
					val = srp->pack_id;
					break;
				}
			}
		}
		SG_LOG(3, sfp, "%s:    SG_GET_PACK_ID=%d\n", __func__, val);
		return put_user(val, ip);
	case SG_GET_SG_TABLESIZE:
		SG_LOG(3, sfp, "%s:    SG_GET_SG_TABLESIZE=%d\n", __func__,
		       sdp->max_sgat_elems);
		return put_user(sdp->max_sgat_elems, ip);
	case SG_SET_RESERVED_SIZE:
		res = get_user(val, ip);
		if (likely(!res)) {
			if (likely(val >= 0 && val <= (1024 * 1024 * 1024))) {
				mutex_lock(&sfp->f_mutex);
				res = sg_set_reserved_sz(sfp, val);
				mutex_unlock(&sfp->f_mutex);
			} else {
				SG_LOG(3, sfp, "%s: invalid size\n", __func__);
				res = -EINVAL;
			}
		}
		return res;
	case SG_GET_RESERVED_SIZE:
		{
			struct sg_request *r_srp = sfp->rsv_arr[0];

			mutex_lock(&sfp->f_mutex);
			val = min_t(int, r_srp->sgatp->buflen,
				    sdp->max_sgat_sz);
			mutex_unlock(&sfp->f_mutex);
			res = put_user(val, ip);
		}
		SG_LOG(3, sfp, "%s:    SG_GET_RESERVED_SIZE=%d\n", __func__,
		       val);
		return res;
	case SG_SET_COMMAND_Q:	/* set by driver whenever v3 or v4 req seen */
		SG_LOG(3, sfp, "%s:    SG_SET_COMMAND_Q\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		assign_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm, !val);
		return 0;
	case SG_GET_COMMAND_Q:
		SG_LOG(3, sfp, "%s:    SG_GET_COMMAND_Q\n", __func__);
		return put_user(!test_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm), ip);
	case SG_SET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_SET_KEEP_ORPHAN\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		assign_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm, !!val);
		return 0;
	case SG_GET_KEEP_ORPHAN:
		SG_LOG(3, sfp, "%s:    SG_GET_KEEP_ORPHAN\n", __func__);
		return put_user(test_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm),
				ip);
	case SG_GET_VERSION_NUM:
		SG_LOG(3, sfp, "%s:    SG_GET_VERSION_NUM\n", __func__);
		return put_user(sg_version_num, ip);
	case SG_GET_REQUEST_TABLE:
		return sg_ctl_req_tbl(sfp, p);
	case SG_SCSI_RESET:
		SG_LOG(3, sfp, "%s:    SG_SCSI_RESET\n", __func__);
		break;
	case SG_SET_TIMEOUT:
		SG_LOG(3, sfp, "%s:    SG_SET_TIMEOUT\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		if (unlikely(val < 0))
			return -EIO;
		if (val >= mult_frac((s64)INT_MAX, USER_HZ, HZ))
			val = min_t(s64, mult_frac((s64)INT_MAX, USER_HZ, HZ),
				    INT_MAX);
		sfp->timeout_user = val;
		sfp->timeout = mult_frac(val, HZ, USER_HZ);
		return 0;
	case SG_GET_TIMEOUT:    /* N.B. User receives timeout as return value */
				/* strange ..., for backward compatibility */
		SG_LOG(3, sfp, "%s:    SG_GET_TIMEOUT\n", __func__);
		return sfp->timeout_user;
	case SG_SET_FORCE_LOW_DMA:
		/*
		 * N.B. This ioctl never worked properly, but failed to
		 * return an error value. So returning '0' to keep
		 * compatibility with legacy applications.
		 */
		SG_LOG(3, sfp, "%s:    SG_SET_FORCE_LOW_DMA\n", __func__);
		return 0;
	case SG_GET_LOW_DMA:
		SG_LOG(3, sfp, "%s:    SG_GET_LOW_DMA\n", __func__);
		return put_user(0, ip);
	case SG_NEXT_CMD_LEN:	/* active only in v2 interface */
		SG_LOG(3, sfp, "%s:    SG_NEXT_CMD_LEN\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		if (unlikely(val > SG_MAX_CDB_SIZE))
			return -ENOMEM;
		mutex_lock(&sfp->f_mutex);
		sfp->next_cmd_len = max_t(int, val, 0);
		mutex_unlock(&sfp->f_mutex);
		return 0;
	case SG_GET_ACCESS_COUNT:
		SG_LOG(3, sfp, "%s:    SG_GET_ACCESS_COUNT\n", __func__);
		/* faked - we don't have a real access count anymore */
		val = (sdev ? 1 : 0);
		return put_user(val, ip);
	case SG_EMULATED_HOST:
		SG_LOG(3, sfp, "%s:    SG_EMULATED_HOST\n", __func__);
		if (SG_IS_DETACHING(sdp))
			return -ENODEV;
		return put_user(sdev->host->hostt->emulated, ip);
	case SCSI_IOCTL_SEND_COMMAND:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_SEND_COMMAND\n", __func__);
		return sg_scsi_ioctl(sdev->request_queue, NULL, filp->f_mode,
				     p);
	case SG_SET_DEBUG:
		SG_LOG(3, sfp, "%s:    SG_SET_DEBUG\n", __func__);
		res = get_user(val, ip);
		if (unlikely(res))
			return res;
		assign_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm, !!val);
		if (val == 0)	/* user can force recalculation */
			sg_calc_sgat_param(sdp);
		return 0;
	case BLKSECTGET:
		SG_LOG(3, sfp, "%s:    BLKSECTGET\n", __func__);
		return put_user(max_sectors_bytes(sdev->request_queue), ip);
	case BLKTRACESETUP:
		SG_LOG(3, sfp, "%s:    BLKTRACESETUP\n", __func__);
		return blk_trace_setup(sdev->request_queue,
				       sdp->disk->disk_name,
				       MKDEV(SCSI_GENERIC_MAJOR, sdp->index),
				       NULL, p);
	case BLKTRACESTART:
		SG_LOG(3, sfp, "%s:    BLKTRACESTART\n", __func__);
		return blk_trace_startstop(sdev->request_queue, 1);
	case BLKTRACESTOP:
		SG_LOG(3, sfp, "%s:    BLKTRACESTOP\n", __func__);
		return blk_trace_startstop(sdev->request_queue, 0);
	case BLKTRACETEARDOWN:
		SG_LOG(3, sfp, "%s:    BLKTRACETEARDOWN\n", __func__);
		return blk_trace_remove(sdev->request_queue);
	case SCSI_IOCTL_GET_IDLUN:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_GET_IDLUN %s\n", __func__,
		       pmlp);
		break;
	case SCSI_IOCTL_GET_BUS_NUMBER:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_GET_BUS_NUMBER%s\n",
		       __func__, pmlp);
		break;
	case SCSI_IOCTL_PROBE_HOST:
		SG_LOG(3, sfp, "%s:    SCSI_IOCTL_PROBE_HOST%s",
		       __func__, pmlp);
		break;
	case SG_GET_TRANSFORM:
		SG_LOG(3, sfp, "%s:    SG_GET_TRANSFORM%s\n", __func__, pmlp);
		break;
	default:
		SG_LOG(3, sfp, "%s:    unrecognized ioctl [0x%x]%s\n",
		       __func__, cmd_in, pmlp);
		if (read_only)
			return -EPERM;	/* don't know, so take safer approach */
		break;
	}
	res = sg_allow_if_err_recovery(sdp, filp->f_flags & O_NDELAY);
	if (unlikely(res))
		return res;
	return -ENOIOCTLCMD;
}

static long
sg_ioctl(struct file *filp, unsigned int cmd_in, unsigned long arg)
{
	void __user *p = (void __user *)arg;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	int ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	if (unlikely(!sdp))
		return -ENXIO;

	ret = sg_ioctl_common(filp, sdp, sfp, cmd_in, p);
	if (ret != -ENOIOCTLCMD)
		return ret;

	return scsi_ioctl(sdp->device, cmd_in, p);
}

#if IS_ENABLED(CONFIG_COMPAT)
static long
sg_compat_ioctl(struct file *filp, unsigned int cmd_in, unsigned long arg)
{
	void __user *p = compat_ptr(arg);
	struct sg_device *sdp;
	struct sg_fd *sfp;
	int ret;

	sfp = filp->private_data;
	sdp = sfp->parentdp;
	if (!sdp)
		return -ENXIO;

	ret = sg_ioctl_common(filp, sdp, sfp, cmd_in, p);
	if (ret != -ENOIOCTLCMD)
		return ret;

	return scsi_compat_ioctl(sdp->device, cmd_in, p);
}
#endif

/*
 * If the sg_request object is not inflight, return -ENODATA. This function
 * returns 1 if the given object was in inflight state and is in await_rcv
 * state after blk_poll() returns 1 or more. If blk_poll() fails, then that
 * (negative) value is returned. Otherwise returns 0. Note that blk_poll()
 * may complete unrelated requests that share the same q and cookie.
 */
static int
sg_srp_q_blk_poll(struct sg_request *srp, struct request_queue *q, int loop_count)
{
	int k, n, num;

	num = (loop_count < 1) ? 1 : loop_count;
	for (k = 0; k < num; ++k) {
		if (atomic_read(&srp->rq_st) != SG_RQ_INFLIGHT)
			return -ENODATA;
		n = blk_poll(q, srp->cookie, loop_count < 0 /* spin if negative */);
		if (n > 0)
			return atomic_read(&srp->rq_st) == SG_RQ_AWAIT_RCV;
		if (n < 0)
			return n;
	}
	return 0;
}

/*
 * Check all requests on this sfp that are both inflight and HIPRI. That check involves calling
 * blk_poll(spin<-false) loop_count times. If loop_count is 0 then call blk_poll once.
 * If loop_count is negative then call blk_poll(spin <- true)) once for each request.
 * Returns number found (could be 0) or a negated errno value.
 */
static int
sg_sfp_blk_poll(struct sg_fd *sfp, int loop_count)
{
	int res = 0;
	int n;
	unsigned long idx, iflags;
	struct sg_request *srp;
	struct scsi_device *sdev = sfp->parentdp->device;
	struct request_queue *q = sdev ? sdev->request_queue : NULL;
	struct xarray *xafp = &sfp->srp_arr;

	if (!q)
		return -EINVAL;
	xa_lock_irqsave(xafp, iflags);
	xa_for_each(xafp, idx, srp) {
		if ((srp->rq_flags & SGV4_FLAG_HIPRI) &&
		    !test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm) &&
		    atomic_read(&srp->rq_st) == SG_RQ_INFLIGHT &&
		    test_bit(SG_FRQ_ISSUED, srp->frq_bm)) {
			xa_unlock_irqrestore(xafp, iflags);
			n = sg_srp_q_blk_poll(srp, q, loop_count);
			if (n == -ENODATA)
				n = 0;
			if (unlikely(n < 0))
				return n;
			xa_lock_irqsave(xafp, iflags);
			res += n;
		}
	}
	xa_unlock_irqrestore(xafp, iflags);
	return res;
}

/*
 * Implements the poll(2) system call for this driver. Returns various EPOLL*
 * flags OR-ed together.
 */
static __poll_t
sg_poll(struct file *filp, poll_table *wait)
{
	int num;
	__poll_t p_res = 0;
	struct sg_fd *sfp = filp->private_data;

	if (test_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm))
		sg_sfp_blk_poll(sfp, 0);	/* LLD may have some ready to push up */
	num = atomic_read(&sfp->waiting);
	if (num < 1) {
		poll_wait(filp, &sfp->cmpl_wait, wait);
		num = atomic_read(&sfp->waiting);
	}
	if (num > 0)
		p_res = EPOLLIN | EPOLLRDNORM;

	if (SG_IS_DETACHING(sfp->parentdp))
		p_res |= EPOLLHUP;
	else if (likely(!test_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm)))
		p_res |= EPOLLOUT | EPOLLWRNORM;
	else if (atomic_read(&sfp->submitted) == 0)
		p_res |= EPOLLOUT | EPOLLWRNORM;
	SG_LOG(3, sfp, "%s: p_res=0x%x\n", __func__, (__force u32)p_res);
	return p_res;
}

static int
sg_fasync(int fd, struct file *filp, int mode)
{
	struct sg_fd *sfp = filp->private_data;

	SG_LOG(3, sfp, "%s: mode(%s)\n", __func__, (mode ? "add" : "remove"));
	return fasync_helper(fd, filp, mode, &sfp->async_qp);
}

static void
sg_vma_open(struct vm_area_struct *vma)
{
	struct sg_fd *sfp = vma->vm_private_data;

	if (unlikely(!sfp)) {
		pr_warn("%s: sfp null\n", __func__);
		return;
	}
	kref_get(&sfp->f_ref);	/* put in: sg_vma_close() */
}

static void
sg_vma_close(struct vm_area_struct *vma)
{
	struct sg_fd *sfp = vma->vm_private_data;

	if (unlikely(!sfp)) {
		pr_warn("%s: sfp null\n", __func__);
		return;
	}
	sfp->mmap_sz = 0;
	kref_put(&sfp->f_ref, sg_remove_sfp); /* get in: sg_vma_open() */
}

/* Note: the error return: VM_FAULT_SIGBUS causes a "bus error" */
static vm_fault_t
sg_vma_fault(struct vm_fault *vmf)
{
	int k, n, length;
	int res = VM_FAULT_SIGBUS;
	unsigned long offset;
	struct vm_area_struct *vma = vmf->vma;
	struct page *page;
	struct sg_scatter_hold *rsv_schp;
	struct sg_request *srp;
	struct sg_device *sdp;
	struct sg_fd *sfp;
	const char *nbp = "==NULL, bad";

	if (unlikely(!vma)) {
		pr_warn("%s: vma%s\n", __func__, nbp);
		goto out_err;
	}
	sfp = vma->vm_private_data;
	if (unlikely(!sfp)) {
		pr_warn("%s: sfp%s\n", __func__, nbp);
		goto out_err;
	}
	sdp = sfp->parentdp;
	if (sdp && SG_IS_DETACHING(sdp)) {
		SG_LOG(1, sfp, "%s: device detaching\n", __func__);
		goto out_err;
	}
	srp = sfp->rsv_arr[0];
	if (IS_ERR_OR_NULL(srp)) {
		SG_LOG(1, sfp, "%s: srp%s\n", __func__, nbp);
		goto out_err;
	}
	mutex_lock(&sfp->f_mutex);
	rsv_schp = srp->sgatp;
	offset = vmf->pgoff << PAGE_SHIFT;
	if (unlikely(offset >= (unsigned int)rsv_schp->buflen)) {
		SG_LOG(1, sfp, "%s: offset[%lu] >= rsv.buflen\n", __func__,
		       offset);
		goto out_err_unlock;
	}
	SG_LOG(5, sfp, "%s: vm_start=0x%lx, off=%lu\n", __func__,
	       vma->vm_start, offset);
	length = 1 << (PAGE_SHIFT + rsv_schp->page_order);
	k = (int)offset / length;
	n = ((int)offset % length) >> PAGE_SHIFT;
	page = nth_page(rsv_schp->pages[k], n);
	get_page(page);
	vmf->page = page;
	res = 0;
out_err_unlock:
	mutex_unlock(&sfp->f_mutex);
out_err:
	return res;
}

static const struct vm_operations_struct sg_mmap_vm_ops = {
	.fault = sg_vma_fault,
	.open = sg_vma_open,
	.close = sg_vma_close,
};

/*
 * Entry point for mmap(2) system call. For mmap(2) to work, request's
 * scatter gather list needs to be order 0 which it is unlikely to be
 * by default. mmap(2) cannot be called more than once per fd.
 */
static int
sg_mmap(struct file *filp, struct vm_area_struct *vma)
{
	int res = 0;
	unsigned long req_sz;
	struct sg_fd *sfp;
	struct sg_request *srp;

	if (unlikely(!filp || !vma))
		return -ENXIO;
	sfp = filp->private_data;
	if (unlikely(!sfp)) {
		pr_warn("sg: %s: sfp is NULL\n", __func__);
		return -ENXIO;
	}
	if (unlikely(!mutex_trylock(&sfp->f_mutex)))
		return -EBUSY;
	req_sz = vma->vm_end - vma->vm_start;
	SG_LOG(3, sfp, "%s: vm_start=%pK, len=%d\n", __func__,
	       (void *)vma->vm_start, (int)req_sz);
	if (unlikely(vma->vm_pgoff || req_sz < SG_DEF_SECTOR_SZ)) {
		res = -EINVAL; /* only an offset of 0 accepted */
		goto fini;
	}
	/* Check reserve request is inactive and has large enough buffer */
	srp = sfp->rsv_arr[0];
	if (SG_RQ_ACTIVE(srp)) {
		res = -EBUSY;
		goto fini;
	}
	if (unlikely(req_sz > SG_WRITE_COUNT_LIMIT)) {	/* sanity check */
		res = -ENOMEM;
		goto fini;
	}
	if (sfp->mmap_sz > 0) {
		SG_LOG(1, sfp, "%s: multiple invocations on this fd\n",
		       __func__);
		res = -EADDRINUSE;
		goto fini;
	}
	if (srp->sgat_h.page_order > 0 ||
	    req_sz > (unsigned long)srp->sgat_h.buflen) {
		sg_remove_srp(srp);
		set_bit(SG_FRQ_FOR_MMAP, srp->frq_bm);
		res = sg_mk_sgat(srp->sgatp, sfp, req_sz);
		if (res) {
			SG_LOG(1, sfp, "%s: sg_mk_sgat failed, wanted=%lu\n",
			       __func__, req_sz);
			goto fini;
		}
	}
	sfp->mmap_sz = req_sz;
	vma->vm_flags |= VM_IO | VM_DONTEXPAND | VM_DONTDUMP;
	vma->vm_private_data = sfp;
	vma->vm_ops = &sg_mmap_vm_ops;
	sg_vma_open(vma);
fini:
	mutex_unlock(&sfp->f_mutex);
	return res;
}

/*
 * This user context function is called from sg_rq_end_io() when an orphaned
 * request needs to be cleaned up (e.g. when control C is typed while an
 * ioctl(SG_IO) is active).
 */
static void
sg_uc_rq_end_io_orphaned(struct work_struct *work)
{
	struct sg_request *srp = container_of(work, struct sg_request,
					      ew_orph.work);
	struct sg_fd *sfp;

	sfp = srp->parentfp;
	if (unlikely(!sfp)) {
		WARN_ONCE(1, "%s: sfp unexpectedly NULL\n", __func__);
		return;
	}
	SG_LOG(3, sfp, "%s: srp=0x%pK\n", __func__, srp);
	if (test_bit(SG_FRQ_DEACT_ORPHAN, srp->frq_bm)) {
		sg_finish_scsi_blk_rq(srp);	/* clean up orphan case */
		sg_deact_request(sfp, srp);
	}
	kref_put(&sfp->f_ref, sg_remove_sfp); /* get in: sg_execute_cmd() */
}

/*
 * This "bottom half" (soft interrupt) handler is called by the mid-level
 * when a request has completed or failed. This callback is registered in a
 * blk_execute_rq_nowait() call in the sg_common_write(). For ioctl(SG_IO)
 * (sync) usage, sg_ctl_sg_io() waits to be woken up by this callback.
 */
static void
sg_rq_end_io(struct request *rqq, blk_status_t status)
{
	enum sg_rq_state rqq_state = SG_RQ_AWAIT_RCV;
	int a_resid, slen;
	u32 rq_result;
	unsigned long iflags;
	struct sg_request *srp = rqq->end_io_data;
	struct scsi_request *scsi_rp = scsi_req(rqq);
	struct sg_device *sdp;
	struct sg_fd *sfp;

	sfp = srp->parentfp;
	sdp = sfp->parentdp;

	rq_result = scsi_rp->result;
	srp->rq_result = rq_result;
	slen = min_t(int, scsi_rp->sense_len, SCSI_SENSE_BUFFERSIZE);
	a_resid = scsi_rp->resid_len;

	if (unlikely(a_resid)) {
		if (SG_IS_V4I(srp)) {
			if (rq_data_dir(rqq) == READ)
				srp->in_resid = a_resid;
			else
				srp->s_hdr4.out_resid = a_resid;
		} else {
			srp->in_resid = a_resid;
		}
	}
	if (unlikely(test_bit(SG_FRQ_ABORTING, srp->frq_bm)) && sg_result_is_good(rq_result))
		srp->rq_result |= (DRIVER_HARD << 24);

	SG_LOG(6, sfp, "%s: pack/tag_id=%d/%d, cmd=0x%x, res=0x%x\n", __func__,
	       srp->pack_id, srp->tag, srp->cmd_opcode, srp->rq_result);
	if (srp->start_ns > 0)	/* zero only when SG_FFD_NO_DURATION is set */
		srp->duration = sg_calc_rq_dur(srp, test_bit(SG_FFD_TIME_IN_NS,
							     sfp->ffd_bm));
	if (unlikely(!sg_result_is_good(rq_result) && slen > 0 &&
		     test_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm))) {
		if ((rq_result & 0xfe) == SAM_STAT_CHECK_CONDITION ||
		    (rq_result & 0xfe) == SAM_STAT_COMMAND_TERMINATED)
			__scsi_print_sense(sdp->device, __func__, scsi_rp->sense, slen);
	}
	if (unlikely(slen > 0)) {
		if (likely(scsi_rp->sense && !srp->sense_bp)) {
			srp->sense_bp =
				mempool_alloc(sg_sense_pool,
					      GFP_ATOMIC   /* <-- leave */);
			if (likely(srp->sense_bp)) {
				memcpy(srp->sense_bp, scsi_rp->sense, slen);
				if (slen < SCSI_SENSE_BUFFERSIZE)
					memset(srp->sense_bp + slen, 0,
					       SCSI_SENSE_BUFFERSIZE - slen);
			} else {
				slen = 0;
				pr_warn("%s: sense but can't alloc buffer\n",
					__func__);
			}
		} else if (unlikely(srp->sense_bp)) {
			slen = 0;
			pr_warn("%s: non-NULL srp->sense_bp ? ?\n", __func__);
		} else {
			slen = 0;
			pr_warn("%s: sense_len>0 but sense==NULL\n", __func__);
		}
	}
	srp->sense_len = slen;
	if (unlikely(test_bit(SG_FRQ_IS_ORPHAN, srp->frq_bm))) {
		if (test_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm)) {
			__clear_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm);
		} else {
			rqq_state = SG_RQ_BUSY;
			__set_bit(SG_FRQ_DEACT_ORPHAN, srp->frq_bm);
		}
	}
	xa_lock_irqsave(&sfp->srp_arr, iflags);
	__set_bit(SG_FRQ_ISSUED, srp->frq_bm);
	sg_rq_chg_state_force_ulck(srp, rqq_state);	/* normally --> SG_RQ_AWAIT_RCV */
	WRITE_ONCE(srp->rqq, NULL);
	if (test_bit(SG_FRQ_COUNT_ACTIVE, srp->frq_bm)) {
		int num = atomic_inc_return(&sfp->waiting);

		if (num < 2) {
			WRITE_ONCE(sfp->low_await_idx, srp->rq_idx);
		} else {
			int l_await_idx = READ_ONCE(sfp->low_await_idx);

			if (l_await_idx < 0 || srp->rq_idx < l_await_idx ||
			    !xa_get_mark(&sfp->srp_arr, l_await_idx, SG_XA_RQ_AWAIT))
				WRITE_ONCE(sfp->low_await_idx, srp->rq_idx);
		}
	}
	xa_unlock_irqrestore(&sfp->srp_arr, iflags);
	/*
	 * Free the mid-level resources apart from the bio (if any). The bio's
	 * blk_rq_unmap_user() can be called later from user context.
	 */
	scsi_req_free_cmd(scsi_rp);
	blk_put_request(rqq);

	if (unlikely(rqq_state != SG_RQ_AWAIT_RCV)) {
		/* clean up orphaned request that aren't being kept */
		INIT_WORK(&srp->ew_orph.work, sg_uc_rq_end_io_orphaned);
		schedule_work(&srp->ew_orph.work);
		/* kref_put(f_ref) done in sg_uc_rq_end_io_orphaned() */
		return;
	}
	if (!(srp->rq_flags & SGV4_FLAG_HIPRI))
		wake_up_interruptible(&sfp->cmpl_wait);
	if (sfp->async_qp && (!SG_IS_V4I(srp) ||
			      (srp->rq_flags & SGV4_FLAG_SIGNAL)))
		kill_fasync(&sfp->async_qp, SIGPOLL, POLL_IN);
	if (sfp->efd_ctxp && (srp->rq_flags & SGV4_FLAG_EVENTFD)) {
		u64 n = eventfd_signal(sfp->efd_ctxp, 1);

		if (n != 1)
			pr_info("%s: srp=%pK eventfd_signal problem\n",
				__func__, srp);
	}
	kref_put(&sfp->f_ref, sg_remove_sfp);	/* get in: sg_execute_cmd() */
}

static const struct file_operations sg_fops = {
	.owner = THIS_MODULE,
	.read = sg_read,
	.write = sg_write,
	.poll = sg_poll,
	.unlocked_ioctl = sg_ioctl,
#if IS_ENABLED(CONFIG_COMPAT)
	.compat_ioctl = sg_compat_ioctl,
#endif
	.open = sg_open,
	.mmap = sg_mmap,
	.release = sg_release,
	.fasync = sg_fasync,
	.llseek = no_llseek,
};

static struct class *sg_sysfs_class;

static bool sg_sysfs_valid;

/* Returns valid pointer to sg_device or negated errno twisted by ERR_PTR */
static struct sg_device *
sg_add_device_helper(struct gendisk *disk, struct scsi_device *scsidp)
{
	struct sg_device *sdp;
	int error;
	u32 k;
	unsigned long iflags;

	sdp = kzalloc(sizeof(*sdp), GFP_KERNEL);
	if (unlikely(!sdp))
		return ERR_PTR(-ENOMEM);

	idr_preload(GFP_KERNEL);
	write_lock_irqsave(&sg_index_lock, iflags);

	error = idr_alloc(&sg_index_idr, sdp, 0, SG_MAX_DEVS, GFP_NOWAIT);
	if (unlikely(error < 0)) {
		if (error == -ENOSPC) {
			sdev_printk(KERN_WARNING, scsidp,
				    "Unable to attach sg device type=%d, minor number exceeds %d\n",
				    scsidp->type, SG_MAX_DEVS - 1);
			error = -ENODEV;
		} else {
			sdev_printk(KERN_WARNING, scsidp,
				"%s: idr allocation sg_device failure: %d\n",
				    __func__, error);
		}
		goto out_unlock;
	}
	k = error;

	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, scsidp,
			 "%s: dev=%d, sdp=0x%pK ++\n", __func__, k, sdp));
	sprintf(disk->disk_name, "sg%d", k);
	disk->first_minor = k;
	sdp->disk = disk;
	sdp->device = scsidp;
	mutex_init(&sdp->open_rel_lock);
	xa_init_flags(&sdp->sfp_arr, XA_FLAGS_ALLOC | XA_FLAGS_LOCK_IRQ);
	init_waitqueue_head(&sdp->open_wait);
	clear_bit(SG_FDEV_DETACHING, sdp->fdev_bm);
	atomic_set(&sdp->open_cnt, 0);
	sdp->index = k;
	/* set d_ref to 1; corresponding put in: sg_remove_device() */
	kref_init(&sdp->d_ref);
	error = 0;

out_unlock:
	write_unlock_irqrestore(&sg_index_lock, iflags);
	idr_preload_end();

	if (unlikely(error)) {
		kfree(sdp);
		return ERR_PTR(error);
	}
	return sdp;
}

static int
sg_add_device(struct device *cl_dev, struct class_interface *cl_intf)
{
	struct scsi_device *scsidp = to_scsi_device(cl_dev->parent);
	struct gendisk *disk;
	struct sg_device *sdp = NULL;
	struct cdev *cdev = NULL;
	int error;
	unsigned long iflags;

	disk = alloc_disk(1);
	if (unlikely(!disk)) {
		pr_warn("%s: alloc_disk failed\n", __func__);
		return -ENOMEM;
	}
	disk->major = SCSI_GENERIC_MAJOR;

	error = -ENOMEM;
	cdev = cdev_alloc();
	if (unlikely(!cdev)) {
		pr_warn("%s: cdev_alloc failed\n", __func__);
		goto out;
	}
	cdev->owner = THIS_MODULE;
	cdev->ops = &sg_fops;

	sdp = sg_add_device_helper(disk, scsidp);
	if (IS_ERR(sdp)) {
		error = PTR_ERR(sdp);
		goto out;
	}

	error = cdev_add(cdev, MKDEV(SCSI_GENERIC_MAJOR, sdp->index), 1);
	if (unlikely(error))
		goto cdev_add_err;

	sdp->cdev = cdev;
	if (likely(sg_sysfs_valid)) {
		struct device *sg_class_member;

		sg_class_member = device_create(sg_sysfs_class, cl_dev->parent,
						MKDEV(SCSI_GENERIC_MAJOR,
						      sdp->index),
						sdp, "%s", disk->disk_name);
		if (IS_ERR(sg_class_member)) {
			pr_err("%s: device_create failed\n", __func__);
			error = PTR_ERR(sg_class_member);
			goto cdev_add_err;
		}
		error = sysfs_create_link(&scsidp->sdev_gendev.kobj,
					  &sg_class_member->kobj, "generic");
		if (unlikely(error))
			pr_err("%s: unable to make symlink 'generic' back "
			       "to sg%d\n", __func__, sdp->index);
	} else
		pr_warn("%s: sg_sys Invalid\n", __func__);

	sdp->create_ns = ktime_get_boottime_ns();
	sg_calc_sgat_param(sdp);
	sdev_printk(KERN_NOTICE, scsidp, "Attached scsi generic sg%d "
		    "type %d\n", sdp->index, scsidp->type);

	dev_set_drvdata(cl_dev, sdp);
	return 0;

cdev_add_err:
	write_lock_irqsave(&sg_index_lock, iflags);
	idr_remove(&sg_index_idr, sdp->index);
	write_unlock_irqrestore(&sg_index_lock, iflags);
	kfree(sdp);

out:
	put_disk(disk);
	if (cdev)
		cdev_del(cdev);
	return error;
}

static void
sg_device_destroy(struct kref *kref)
{
	struct sg_device *sdp = container_of(kref, struct sg_device, d_ref);
	unsigned long iflags;

	SCSI_LOG_TIMEOUT(1, pr_info("[tid=%d] %s: sdp idx=%d, sdp=0x%pK --\n",
				    (current ? current->pid : -1), __func__,
				    sdp->index, sdp));
	/*
	 * CAUTION!  Note that the device can still be found via idr_find()
	 * even though the refcount is 0.  Therefore, do idr_remove() BEFORE
	 * any other cleanup.
	 */

	xa_destroy(&sdp->sfp_arr);
	write_lock_irqsave(&sg_index_lock, iflags);
	idr_remove(&sg_index_idr, sdp->index);
	write_unlock_irqrestore(&sg_index_lock, iflags);

	put_disk(sdp->disk);
	kfree(sdp);
}

static void
sg_remove_device(struct device *cl_dev, struct class_interface *cl_intf)
{
	struct scsi_device *scsidp = to_scsi_device(cl_dev->parent);
	struct sg_device *sdp = dev_get_drvdata(cl_dev);
	unsigned long idx;
	struct sg_fd *sfp;

	if (unlikely(!sdp))
		return;
	/* set this flag as soon as possible as it could be a surprise */
	if (test_and_set_bit(SG_FDEV_DETACHING, sdp->fdev_bm)) {
		pr_warn("%s: multiple entries: sg%u\n", __func__, sdp->index);
		return; /* only want to do following once per device */
	}
	SCSI_LOG_TIMEOUT(3, sdev_printk(KERN_INFO, sdp->device,
					"%s: sg%u 0x%pK\n", __func__,
					sdp->index, sdp));
	xa_for_each(&sdp->sfp_arr, idx, sfp) {
		wake_up_interruptible_all(&sfp->cmpl_wait);
		if (sfp->async_qp)
			kill_fasync(&sfp->async_qp, SIGPOLL, POLL_HUP);
	}
	wake_up_interruptible_all(&sdp->open_wait);

	sysfs_remove_link(&scsidp->sdev_gendev.kobj, "generic");
	device_destroy(sg_sysfs_class, MKDEV(SCSI_GENERIC_MAJOR, sdp->index));
	cdev_del(sdp->cdev);
	sdp->cdev = NULL;

	/* init to 1: kref_init() in sg_add_device_helper() */
	kref_put(&sdp->d_ref, sg_device_destroy);
}

static int __init
init_sg(void)
{
	int rc;

	/* check scatter_elem_sz module parameter, change if inappropriate */
	if (scatter_elem_sz < (int)PAGE_SIZE)
		scatter_elem_sz = PAGE_SIZE;
	else if (!is_power_of_2(scatter_elem_sz))
		scatter_elem_sz = roundup_pow_of_two(scatter_elem_sz);
	if (def_reserved_size >= 0)
		sg_big_buff = def_reserved_size;
	else
		def_reserved_size = sg_big_buff;

	rc = register_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0),
				    SG_MAX_DEVS, "sg");
	if (unlikely(rc))
		return rc;

	sg_sense_cache = kmem_cache_create_usercopy
				("sg_sense", SCSI_SENSE_BUFFERSIZE, 0,
				 SLAB_HWCACHE_ALIGN, 0,
				 SCSI_SENSE_BUFFERSIZE, NULL);
	if (unlikely(!sg_sense_cache)) {
		pr_err("sg: can't init sense cache\n");
		rc = -ENOMEM;
		goto err_out_unreg;
	}
	sg_sense_pool = mempool_create_slab_pool(SG_MEMPOOL_MIN_NR,
						 sg_sense_cache);
	if (unlikely(!sg_sense_pool)) {
		pr_err("sg: can't init sense pool\n");
		rc = -ENOMEM;
		goto err_out_cache;
	}

	pr_info("Registered %s[char major=0x%x], version: %s, date: %s\n",
		"sg device ", SCSI_GENERIC_MAJOR, SG_VERSION_STR,
		sg_version_date);
	sg_sysfs_class = class_create(THIS_MODULE, "scsi_generic");
	if (IS_ERR(sg_sysfs_class)) {
		rc = PTR_ERR(sg_sysfs_class);
		goto err_out_pool;
	}
	sg_sysfs_valid = true;
	rc = scsi_register_interface(&sg_interface);
	if (likely(rc == 0)) {
		sg_proc_init();
		sg_dfs_init();
		return 0;
	}
	class_destroy(sg_sysfs_class);

err_out_pool:
	mempool_destroy(sg_sense_pool);
err_out_cache:
	kmem_cache_destroy(sg_sense_cache);
err_out_unreg:
	unregister_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0), SG_MAX_DEVS);
	return rc;
}

static void __exit
exit_sg(void)
{
	sg_dfs_exit();
	if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
		remove_proc_subtree("scsi/sg", NULL);
	kfree(snapped_buf);
	scsi_unregister_interface(&sg_interface);
	mempool_destroy(sg_sense_pool);
	kmem_cache_destroy(sg_sense_cache);
	class_destroy(sg_sysfs_class);
	sg_sysfs_valid = false;
	unregister_chrdev_region(MKDEV(SCSI_GENERIC_MAJOR, 0),
				 SG_MAX_DEVS);
	idr_destroy(&sg_index_idr);
}

static struct bio *
sg_mk_kern_bio(int bvec_cnt)
{
	struct bio *biop;

	if (bvec_cnt > BIO_MAX_VECS)
		return NULL;
	biop = bio_alloc(GFP_ATOMIC, bvec_cnt);
	if (!biop)
		return NULL;
	biop->bi_end_io = bio_put;
	return biop;
}

/*
 * Setup to move data between kernel buffers managed by this driver and a SCSI device. Note that
 * there is no corresponding 'unmap' call as is required by blk_rq_map_user() . Uses a single
 * bio with an expanded appended bvec if necessary.
 */
static int
sg_rq_map_kern(struct sg_request *srp, struct request_queue *q, struct request *rqq, int rw_ind)
{
	struct sg_scatter_hold *schp = srp->sgatp;
	struct bio *bio;
	bool have_bio = false;
	int k, ln, nr_segs;
	int op_flags = 0;
	int num_sgat = schp->num_sgat;
	int dlen = schp->dlen;
	int pg_sz = 1 << (PAGE_SHIFT + schp->page_order);

	SG_LOG(4, srp->parentfp, "%s: dlen=%d, pg_sz=%d\n", __func__, dlen, pg_sz);
	if (num_sgat <= 0)
		return 0;
	nr_segs = num_sgat;
	k = 0;		/* N.B. following condition may increase k */
	if (rw_ind == WRITE) {
		op_flags = REQ_SYNC | REQ_IDLE;
		if (unlikely(srp->rq_flags & SGV4_FLAG_DOUT_OFFSET) && SG_IS_V4I(srp)) {
			struct sg_slice_hdr4 *slh4p = &srp->s_hdr4;

			u32 wr_len = slh4p->wr_len;
			u32 wr_off = slh4p->wr_offset;

			if (wr_off > 0) {  /* skip over wr_off, conditionally add partial page */
				for (ln = 0; k < num_sgat && wr_off > 0; ++k, wr_off -= ln)
					ln = min_t(int, wr_off, pg_sz);
				bio = sg_mk_kern_bio(num_sgat + 1 - k);
				if (!bio)
					return -ENOMEM;
				bio->bi_opf = req_op(rqq) | op_flags;
				have_bio = true;
				if (ln < pg_sz) {	/* k > 0 since num_sgat > 0 */
					int rlen = pg_sz - ln;
					struct page *pg = schp->pages[k - 1];

					if (bio_add_pc_page(q, bio, pg, rlen, ln) < rlen) {
						bio_put(bio);
						return -EINVAL;
					}
					wr_len -= pg_sz - ln;
				}
				dlen = wr_len;
				nr_segs = num_sgat - k;
				SG_LOG(5, srp->parentfp, "%s:   wr_off=%u wr_len=%u\n", __func__,
				       wr_off, wr_len);
			} else {
				if (wr_len < dlen)
					dlen = wr_len;	/* short write, offset 0 */
			}
		}
	}
	if (!have_bio) {
		bio = sg_mk_kern_bio(nr_segs);
		if (!bio)
			return -ENOMEM;
		bio->bi_opf = req_op(rqq) | op_flags;
	}
	for ( ; k < num_sgat && dlen > 0; ++k, dlen -= ln) {
		ln = min_t(int, dlen, pg_sz);
		if (bio_add_pc_page(q, bio, schp->pages[k], ln, 0) < ln) {
			bio_put(bio);
			return -EINVAL;
		}
	}
	/* used blk_rq_append_bio() before but this is simpler */
	blk_rq_bio_prep(rqq, bio, nr_segs);
	rqq->nr_phys_segments = (1 << schp->page_order) * num_sgat;
	return 0;
}

static int
sg_start_req(struct sg_request *srp, struct sg_comm_wr_t *cwrp, int dxfer_dir)
{
	bool no_dxfer, us_xfer;
	int res = 0;
	int dlen = cwrp->dlen;
	int r0w = READ;
	u32 rq_flags = srp->rq_flags;
	unsigned int iov_count = 0;
	void __user *up;
	struct request *rqq;
	struct scsi_request *scsi_rp;
	struct sg_fd *sfp = cwrp->sfp;
	struct sg_device *sdp;
	struct sg_scatter_hold *req_schp;
	struct request_queue *q;
	struct rq_map_data *md = (void *)srp; /* want any non-NULL value */
	u8 *long_cmdp = NULL;
	__maybe_unused const char *cp = "";
	struct rq_map_data map_data;

	sdp = sfp->parentdp;
	if (cwrp->cmd_len > BLK_MAX_CDB) {	/* for longer SCSI cdb_s */
		long_cmdp = kzalloc(cwrp->cmd_len, GFP_KERNEL);
		if (unlikely(!long_cmdp)) {
			res = -ENOMEM;
			goto err_pre_blk_get;
		}
		SG_LOG(5, sfp, "%s: long_cmdp=0x%pK ++\n", __func__, long_cmdp);
	}
	if (SG_IS_V4I(srp)) {
		struct sg_io_v4 *h4p = cwrp->h4p;

		if (dxfer_dir == SG_DXFER_TO_DEV) {
			r0w = WRITE;
			up = uptr64(h4p->dout_xferp);
			iov_count = h4p->dout_iovec_count;
		} else if (dxfer_dir == SG_DXFER_FROM_DEV) {
			up = uptr64(h4p->din_xferp);
			iov_count = h4p->din_iovec_count;
		} else {
			up = NULL;
		}
	} else {
		struct sg_slice_hdr3 *sh3p = &srp->s_hdr3;

		up = sh3p->dxferp;
		iov_count = sh3p->iovec_count;
		r0w = dxfer_dir == SG_DXFER_TO_DEV ? WRITE : READ;
	}
	SG_LOG(4, sfp, "%s: dlen=%d%s\n", __func__, dlen,
	       (dlen ? (r0w ? ", data-OUT" : ", data-IN") : ""));
	q = sdp->device->request_queue;

	/*
	 * For backward compatibility default to using blocking variant even
	 * when in non-blocking (async) mode. If the SG_CTL_FLAGM_MORE_ASYNC
	 * boolean set on this file descriptor, returns -EAGAIN if
	 * blk_get_request(BLK_MQ_REQ_NOWAIT) yields EAGAIN (aka EWOULDBLOCK).
	 */
	rqq = blk_get_request(q, (r0w ? REQ_OP_SCSI_OUT : REQ_OP_SCSI_IN),
			      (test_bit(SG_FFD_MORE_ASYNC, sfp->ffd_bm) ?  BLK_MQ_REQ_NOWAIT : 0));
	if (IS_ERR(rqq)) {
		res = PTR_ERR(rqq);
		goto err_pre_blk_get;
	}
	/* current sg_request protected by SG_RQ_BUSY state */
	scsi_rp = scsi_req(rqq);
	WRITE_ONCE(srp->rqq, rqq);

	if (rq_flags & SGV4_FLAG_YIELD_TAG)
		srp->tag = rqq->tag;
	if (cwrp->cmd_len > BLK_MAX_CDB) {
		scsi_rp->cmd = long_cmdp;	/* transfer ownership */
		/* this heap freed in scsi_req_free_cmd() */
		long_cmdp = NULL;
	}
	if (cwrp->u_cmdp)
		res = sg_fetch_cmnd(sfp, cwrp->u_cmdp, cwrp->cmd_len,
				    scsi_rp->cmd);
	else if (likely(cwrp->cmdp))
		memcpy(scsi_rp->cmd, cwrp->cmdp, cwrp->cmd_len);
	else
		res = -EPROTO;
	if (unlikely(res))
		goto fini;
	scsi_rp->cmd_len = cwrp->cmd_len;
	srp->cmd_opcode = scsi_rp->cmd[0];
	no_dxfer = dlen <= 0 || dxfer_dir == SG_DXFER_NONE;
	us_xfer = !(rq_flags & (SG_FLAG_NO_DXFER | SG_FLAG_MMAP_IO));
	__assign_bit(SG_FRQ_US_XFER, srp->frq_bm, !no_dxfer && us_xfer);
	rqq->end_io_data = srp;
	scsi_rp->retries = SG_DEFAULT_RETRIES;
	req_schp = srp->sgatp;

	if (no_dxfer) {
		SG_LOG(4, sfp, "%s: no data xfer [0x%pK]\n", __func__, srp);
		goto fini;	/* path of reqs with no din nor dout */
	} else if (unlikely(rq_flags & SG_FLAG_DIRECT_IO) && iov_count == 0 &&
		   blk_rq_aligned(q, (unsigned long)up, dlen)) {
		srp->rq_info |= SG_INFO_DIRECT_IO;
		md = NULL;
		if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
			cp = "direct_io, ";
	} else {	/* normal IO and failed conditions for dio path */
		md = &map_data;
	}

	if (likely(md)) {	/* normal, "indirect" IO */
		if (unlikely(rq_flags & SG_FLAG_MMAP_IO)) {
			/* mmap IO must use and fit in reserve request */
			bool reserve0;
			struct sg_request *r_srp = sfp->rsv_arr[0];

			reserve0 = (r_srp == srp);
			if (unlikely(!reserve0 || dlen > req_schp->buflen))
				res = reserve0 ? -ENOMEM : -EBUSY;
		} else if (req_schp->buflen == 0) {
			int up_sz = max_t(int, dlen, sfp->sgat_elem_sz);

			res = sg_mk_sgat(srp->sgatp, sfp, up_sz);
		}
		if (unlikely(res))
			goto fini;
		md->pages = req_schp->pages;
		md->page_order = req_schp->page_order;
		md->nr_entries = req_schp->num_sgat;
		md->offset = 0;
		md->null_mapped = !up;
		md->from_user = (dxfer_dir == SG_DXFER_TO_FROM_DEV);
	}

	if (unlikely(iov_count)) {
		struct iovec *iov = NULL;
		struct iov_iter i;

		res = import_iovec(r0w, up, iov_count, 0, &iov, &i);
		if (unlikely(res < 0))
			goto fini;

		iov_iter_truncate(&i, dlen);
		if (unlikely(!iov_iter_count(&i))) {
			kfree(iov);
			res = -EINVAL;
			goto fini;
		}

		if (us_xfer)
			res = blk_rq_map_user_iov(q, rqq, md, &i, GFP_ATOMIC);
		kfree(iov);
		if (IS_ENABLED(CONFIG_SCSI_PROC_FS))
			cp = "iov_count > 0";
	} else if (us_xfer) { /* setup for transfer data to/from user space */
		res = blk_rq_map_user(q, rqq, md, up, dlen, GFP_ATOMIC);
#if IS_ENABLED(SG_LOG_ACTIVE)
		if (unlikely(res))
			SG_LOG(1, sfp, "%s: blk_rq_map_user() res=%d\n",
			       __func__, res);
#endif
	} else {	/* transfer data to/from kernel buffers */
		res = sg_rq_map_kern(srp, q, rqq, r0w);
	}
fini:
	if (unlikely(res)) {		/* failure, free up resources */
		if (us_xfer && rqq->bio)
			blk_rq_unmap_user(rqq->bio);
		scsi_req_free_cmd(scsi_rp);
		WRITE_ONCE(srp->rqq, NULL);
		blk_put_request(rqq);
	} else {
		srp->bio = rqq->bio;
	}
err_pre_blk_get:
	SG_LOG((res ? 1 : 4), sfp, "%s: %s %s res=%d [0x%pK]\n", __func__,
	       sg_shr_str(srp->sh_var, false), cp, res, srp);
	kfree(long_cmdp);
	return res;
}

/*
 * Clean up mid-level and block layer resources of finished request. Sometimes
 * blk_rq_unmap_user() returns -4 (-EINTR) and this is why: "If we're in a
 * workqueue, the request is orphaned, so don't copy into a random user
 * address space, just free and return -EINTR so user space doesn't expect
 * any data." [block/bio.c]
 */
static void
sg_finish_scsi_blk_rq(struct sg_request *srp)
{
	int ret;
	struct sg_fd *sfp = srp->parentfp;
	struct request *rqq = READ_ONCE(srp->rqq);
	__maybe_unused char b[32];

	SG_LOG(4, sfp, "%s: srp=0x%pK%s\n", __func__, srp,
	       sg_get_rsv_str_lck(srp, " ", "", sizeof(b), b));
	if (test_and_clear_bit(SG_FRQ_COUNT_ACTIVE, srp->frq_bm)) {
		if (atomic_dec_and_test(&sfp->submitted))
			clear_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm);
		atomic_dec_return_release(&sfp->waiting);
	}

	/* Expect blk_put_request(rqq) already called in sg_rq_end_io() */
	if (rqq) {	/* blk_get_request() may have failed */
		WRITE_ONCE(srp->rqq, NULL);
		if (scsi_req(rqq))
			scsi_req_free_cmd(scsi_req(rqq));
		blk_put_request(rqq);
	}
	if (likely(srp->bio)) {
		bool us_xfer = test_bit(SG_FRQ_US_XFER, srp->frq_bm);
		struct bio *bio = srp->bio;

		srp->bio = NULL;
		if (us_xfer && bio) {
			ret = blk_rq_unmap_user(bio);
			if (unlikely(ret)) {	/* -EINTR (-4) can be ignored */
				SG_LOG(6, sfp,
				       "%s: blk_rq_unmap_user() --> %d\n",
				       __func__, ret);
			}
		}
	}
	/* In worst case, READ data returned to user space by this point */
}

static int
sg_mk_sgat(struct sg_scatter_hold *schp, struct sg_fd *sfp, int minlen)
{
	int j, k, rem_sz, align_sz, order, o_order;
	int mx_sgat_elems = sfp->parentdp->max_sgat_elems;
	unsigned int elem_sz = sfp->sgat_elem_sz;
	const size_t ptr_sz = sizeof(struct page *);
	gfp_t mask_ap = GFP_ATOMIC | __GFP_COMP | __GFP_NOWARN | __GFP_ZERO;
	gfp_t mask_kz = GFP_ATOMIC | __GFP_NOWARN;
	struct page **pgp;

	if (unlikely(minlen <= 0)) {
		if (minlen < 0)
			return -EFAULT;
		++minlen;	/* don't remember why */
	}
	/* round request up to next highest SG_DEF_SECTOR_SZ byte boundary */
	align_sz = ALIGN(minlen, SG_DEF_SECTOR_SZ);

	schp->pages = kcalloc(mx_sgat_elems, ptr_sz, mask_kz);
	SG_LOG(4, sfp, "%s: minlen=%d [sz=%zu, 0x%pK ++]\n", __func__, minlen,
	       mx_sgat_elems * ptr_sz, schp->pages);
	if (unlikely(!schp->pages))
		return -ENOMEM;

	/* elem_sz must be power of 2 and >= PAGE_SIZE */
	o_order = get_order(elem_sz);
	order = o_order;

again:
	if (elem_sz * mx_sgat_elems < align_sz) {	/* misfit ? */
		SG_LOG(1, sfp, "%s: align_sz=%d too big\n", __func__,
		       align_sz);
		goto b4_alloc_pages;
	}
	rem_sz = align_sz;
	for (pgp = schp->pages; rem_sz > 0; ++pgp, rem_sz -= elem_sz) {
		*pgp = alloc_pages(mask_ap, order);
		if (unlikely(!*pgp))
			goto err_out;
		SG_LOG(6, sfp, "%s: elem_sz=%d [0x%pK ++]\n", __func__,
		       elem_sz, *pgp);
	}
	k = pgp - schp->pages;
	SG_LOG(((order != o_order || rem_sz > 0) ? 2 : 5), sfp,
	       "%s: num_sgat=%d, order=%d,%d  rem_sz=%d\n", __func__, k,
	       o_order, order, rem_sz);
	schp->page_order = order;
	schp->num_sgat = k;
	schp->buflen = align_sz;
	if (sfp->tot_fd_thresh > 0)
		atomic_add(align_sz, &sfp->sum_fd_dlens);
	return 0;
err_out:
	k = pgp - schp->pages;
	for (j = 0; j < k; ++j)
		__free_pages(schp->pages[j], order);

	if (--order >= 0) {
		elem_sz >>= 1;
		goto again;
	}
b4_alloc_pages:
	kfree(schp->pages);
	schp->pages = NULL;
	return -ENOMEM;
}

static void
sg_remove_sgat(struct sg_fd *sfp, struct sg_scatter_hold *schp)
{
	int k;
	void *p;

	if (!schp->pages)
		return;
	for (k = 0; k < schp->num_sgat; ++k) {
		p = schp->pages[k];
		SG_LOG(6, sfp, "%s: pg[%d]=0x%pK --\n", __func__, k, p);
		if (unlikely(!p))
			continue;
		__free_pages(p, schp->page_order);
	}
	SG_LOG(5, sfp, "%s: pg_order=%u, free pgs=0x%pK --\n", __func__,
	       schp->page_order, schp->pages);
	kfree(schp->pages);
}

/* Remove the data (possibly a sgat list) held by srp, not srp itself */
static void
sg_remove_srp(struct sg_request *srp)
{
	struct sg_scatter_hold *schp;
	struct sg_fd *sfp;
	__maybe_unused char b[48];

	if (!srp)
		return;
	schp = &srp->sgat_h; /* care: remove own data */
	sfp = srp->parentfp;
	SG_LOG(4, sfp, "%s: num_sgat=%d%s\n", __func__, schp->num_sgat,
	       sg_get_rsv_str_lck(srp, " [", "]", sizeof(b), b));
	sg_remove_sgat(sfp, schp);

	if (sfp->tot_fd_thresh > 0) {
		/* this is a subtraction, error if it goes negative */
		if (atomic_add_negative(-schp->buflen, &sfp->sum_fd_dlens)) {
			SG_LOG(2, sfp, "%s: logic error: this dlen > %s\n",
			       __func__, "sum_fd_dlens");
			atomic_set(&sfp->sum_fd_dlens, 0);
		}
	}
	memset(schp, 0, sizeof(*schp));		/* zeros buflen and dlen */
}

/*
 * For sg v1 and v2 interface: with a command yielding a data-in buffer, after
 * it has arrived in kernel memory, this function copies it to the user space,
 * appended to given struct sg_header object.
 */
static int
sg_read_append(struct sg_request *srp, void __user *outp, int num_xfer)
{
	int k, num, res;
	struct page *pgp;
	struct sg_scatter_hold *schp = srp->sgatp;

	SG_LOG(4, srp->parentfp, "%s: num_xfer=%d\n", __func__, num_xfer);
	if (unlikely(!outp || num_xfer <= 0))
		return (num_xfer == 0 && outp) ? 0 : -EINVAL;

	num = 1 << (PAGE_SHIFT + schp->page_order);
	for (k = 0, res = 0; k < schp->num_sgat; ++k) {
		pgp = schp->pages[k];
		if (unlikely(!pgp)) {
			res = -ENXIO;
			break;
		}
		if (num > num_xfer) {
			if (copy_to_user(outp, page_address(pgp), num_xfer))
				res = -EFAULT;
			break;
		} else {
			if (copy_to_user(outp, page_address(pgp), num)) {
				res = -EFAULT;
				break;
			}
			num_xfer -= num;
			if (num_xfer <= 0)
				break;
			outp += num;
		}
	}
	return res;
}

/*
 * If there are many requests outstanding, the speed of this function is
 * important. 'id' is pack_id when is_tag=false, otherwise it is a tag. Both
 * SG_PACK_ID_WILDCARD and SG_TAG_WILDCARD are -1 and that case is typically
 * the fast path. This function is only used in the non-blocking cases.
 * Returns pointer to (first) matching sg_request or NULL. If found,
 * sg_request state is moved from SG_RQ_AWAIT_RCV to SG_RQ_BUSY.
 */
static struct sg_request *
sg_find_srp_by_id(struct sg_fd *sfp, int id, bool is_tag)
{
	__maybe_unused bool is_bad_st = false;
	__maybe_unused enum sg_rq_state bad_sr_st = SG_RQ_INACTIVE;
	bool search_for_1 = (id != SG_TAG_WILDCARD);
	bool second = false;
	enum sg_rq_state sr_st;
	int res;
	int l_await_idx = READ_ONCE(sfp->low_await_idx);
	unsigned long idx, s_idx;
	unsigned long end_idx = ULONG_MAX;
	struct sg_request *srp = NULL;
	struct xarray *xafp = &sfp->srp_arr;

	if (test_bit(SG_FFD_HIPRI_SEEN, sfp->ffd_bm))
		sg_sfp_blk_poll(sfp, 0);	/* LLD may have some ready to push up */
	if (sg_num_waiting_maybe_acquire(sfp) < 1)
		return NULL;

	s_idx = (l_await_idx < 0) ? 0 : l_await_idx;
	idx = s_idx;
	if (unlikely(search_for_1)) {
second_time:
		for (srp = xa_find(xafp, &idx, end_idx, SG_XA_RQ_AWAIT);
		     srp;
		     srp = xa_find_after(xafp, &idx, end_idx, SG_XA_RQ_AWAIT)) {
			if (test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm))
				continue;
			if (unlikely(is_tag)) {
				if (srp->tag != id)
					continue;
			} else {
				if (srp->pack_id != id)
					continue;
			}
			sr_st = atomic_read(&srp->rq_st);
			switch (sr_st) {
			case SG_RQ_AWAIT_RCV:
				res = sg_rq_chg_state(srp, sr_st, SG_RQ_BUSY);
				if (likely(res == 0))
					goto good;
				/* else another caller got it, move on */
				if (IS_ENABLED(CONFIG_SCSI_PROC_FS)) {
					is_bad_st = true;
					bad_sr_st = atomic_read(&srp->rq_st);
				}
				break;
			case SG_RQ_SHR_IN_WS:
				goto good;
			case SG_RQ_INFLIGHT:
				break;
			default:
				if (IS_ENABLED(CONFIG_SCSI_PROC_FS)) {
					is_bad_st = true;
					bad_sr_st = sr_st;
				}
				break;
			}
			break;
		}
		/* If not found so far, need to wrap around and search [0 ... s_idx) */
		if (!srp && !second && s_idx > 0) {
			end_idx = s_idx - 1;
			s_idx = 0;
			idx = s_idx;
			second = true;
			goto second_time;
		}
	} else {
		/*
		 * Searching for _any_ request is the more likely usage. Start searching with the
		 * last xarray index that was used. In the case of a large-ish IO depth, it is
		 * likely that the second (relative) position will be the request we want, if it
		 * is ready. If there is no queuing and the "last used" has been re-used then the
		 * first (relative) position will be the request we want.
		 */
second_time2:
		for (srp = xa_find(xafp, &idx, end_idx, SG_XA_RQ_AWAIT);
		     srp;
		     srp = xa_find_after(xafp, &idx, end_idx, SG_XA_RQ_AWAIT)) {
			if (test_bit(SG_FRQ_SYNC_INVOC, srp->frq_bm))
				continue;
			res = sg_rq_chg_state(srp, SG_RQ_AWAIT_RCV, SG_RQ_BUSY);
			if (likely(res == 0)) {
				WRITE_ONCE(sfp->low_await_idx, idx + 1);
				goto good;
			}
#if IS_ENABLED(SG_LOG_ACTIVE)
			sg_rq_state_fail_msg(sfp, SG_RQ_AWAIT_RCV, SG_RQ_BUSY, __func__);
#endif
		}
		if (!srp && !second && s_idx > 0) {
			end_idx = s_idx - 1;
			s_idx = 0;
			idx = s_idx;
			second = true;
			goto second_time2;
		}
	}
	/* here if one of above loops does _not_ find a match */
	if (IS_ENABLED(CONFIG_SCSI_PROC_FS)) {
		if (search_for_1) {
			__maybe_unused const char *cptp = is_tag ? "tag=" :
								   "pack_id=";

			if (unlikely(is_bad_st))
				SG_LOG(1, sfp, "%s: %s%d wrong state: %s\n",
				       __func__, cptp, id,
				       sg_rq_st_str(bad_sr_st, true));
			else
				SG_LOG(6, sfp, "%s: %s%d not awaiting read\n",
				       __func__, cptp, id);
		}
	}
	return NULL;
good:
	SG_LOG(5, sfp, "%s: %s%d found [srp=0x%pK]\n", __func__,
	       (is_tag ? "tag=" : "pack_id="), id, srp);
	return srp;
}

/*
 * Returns true if a request is ready and its srp is written to *srpp . If
 * nothing can be found (because nothing is currently submitted) then true
 * is returned and ERR_PTR(-ENODATA) --> *srpp . If nothing is found but
 * sfp has requests submitted, returns false and NULL --> *srpp .
 */
static bool
sg_mrq_get_ready_srp(struct sg_fd *sfp, struct sg_request **srpp)
{
	bool second = false;
	int res;
	int l_await_idx = READ_ONCE(sfp->low_await_idx);
	unsigned long idx, s_idx, end_idx;
	struct sg_request *srp;
	struct xarray *xafp = &sfp->srp_arr;

	if (SG_IS_DETACHING(sfp->parentdp)) {
		*srpp = ERR_PTR(-ENODEV);
		return true;
	}
	if (atomic_read(&sfp->submitted) < 1) {
		*srpp = ERR_PTR(-ENODATA);
		return true;
	}
	if (sg_num_waiting_maybe_acquire(sfp) < 1)
		goto fini;

	s_idx = (l_await_idx < 0) ? 0 : l_await_idx;
	idx = s_idx;
	end_idx = ULONG_MAX;

second_time:
	for (srp = xa_find(xafp, &idx, end_idx, SG_XA_RQ_AWAIT);
	     srp;
	     srp = xa_find_after(xafp, &idx, end_idx, SG_XA_RQ_AWAIT)) {
		res = sg_rq_chg_state(srp, SG_RQ_AWAIT_RCV, SG_RQ_BUSY);
		if (likely(res == 0)) {
			*srpp = srp;
			WRITE_ONCE(sfp->low_await_idx, idx + 1);
			return true;
		}
#if IS_ENABLED(SG_LOG_ACTIVE)
		sg_rq_state_fail_msg(sfp, SG_RQ_AWAIT_RCV, SG_RQ_BUSY, __func__);
#endif
	}
	/* If not found so far, need to wrap around and search [0 ... end_idx) */
	if (!srp && !second && s_idx > 0) {
		end_idx = s_idx - 1;
		s_idx = 0;
		idx = s_idx;
		second = true;
		goto second_time;
	}
fini:
	*srpp = NULL;
	return false;
}

/*
 * Makes a new sg_request object. If 'first' is set then use GFP_KERNEL which
 * may take time but has improved chance of success, otherwise use GFP_ATOMIC.
 * Note that basic initialization is done but srp is not added to either sfp
 * list. On error returns twisted negated errno value (not NULL).
 * N.B. Initializes new srp state to SG_RQ_BUSY.
 */
static struct sg_request *
sg_mk_only_srp(struct sg_fd *sfp, bool first)
{
	struct sg_request *srp;
	gfp_t gfp = __GFP_NOWARN;

	if (first)      /* prepared to wait if none already outstanding */
		srp = kzalloc(sizeof(*srp), gfp | GFP_KERNEL);
	else
		srp = kzalloc(sizeof(*srp), gfp | GFP_ATOMIC);
	if (likely(srp)) {
		atomic_set(&srp->rq_st, SG_RQ_BUSY);
		srp->sh_var = SG_SHR_NONE;
		srp->parentfp = sfp;
		srp->tag = SG_TAG_WILDCARD;
		srp->sgatp = &srp->sgat_h; /* only write-side share changes sgatp */
		return srp;
	} else {
		return ERR_PTR(-ENOMEM);
	}
}

static struct sg_request *
sg_mk_srp_sgat(struct sg_fd *sfp, bool first, int db_len)
{
	int res;
	struct sg_request *n_srp = sg_mk_only_srp(sfp, first);

	if (IS_ERR(n_srp))
		return n_srp;
	if (db_len > 0) {
		res = sg_mk_sgat(n_srp->sgatp, sfp, db_len);
		if (unlikely(res)) {
			kfree(n_srp);
			return ERR_PTR(res);
		}
	}
	return n_srp;
}

/*
 * Irrespective of the given reserve request size, the minimum size requested
 * will be PAGE_SIZE (often 4096 bytes). Returns a pointer to reserve object or
 * a negated errno value twisted by ERR_PTR() macro. The actual number of bytes
 * allocated (maybe less than buflen) is in srp->sgatp->buflen . Note that this
 * function is only called in contexts where locking is not required.
 */
static struct sg_request *
sg_build_reserve(struct sg_fd *sfp, int buflen)
{
	bool go_out = false;
	int res, idx;
	struct sg_request *srp;
	struct sg_request **rapp;

	SG_LOG(3, sfp, "%s: buflen=%d\n", __func__, buflen);
	idx = sg_get_idx_new_lck(sfp);
	if (idx < 0) {
		SG_LOG(1, sfp, "%s: sg_get_idx_new_lck() failed\n", __func__);
		return ERR_PTR(-EFBIG);
	}
	rapp = sfp->rsv_arr + idx;
	srp = sg_mk_only_srp(sfp, xa_empty(&sfp->srp_arr));
	if (IS_ERR(srp)) {
		*rapp = NULL;
		return srp;
	}
	do {
		if (buflen < (int)PAGE_SIZE) {
			buflen = PAGE_SIZE;
			go_out = true;
		}
		res = sg_mk_sgat(srp->sgatp, sfp, buflen);
		if (likely(res == 0)) {
			*rapp = srp;
			SG_LOG(4, sfp,
			       "%s: rsv%d: final buflen=%d, srp=0x%pK ++\n",
			       __func__, idx, buflen, srp);
			return srp;
		}
		if (go_out) {
			*rapp = NULL;
			return ERR_PTR(res);
		}
		/* failed so remove, halve buflen, try again */
		sg_remove_srp(srp);
		buflen >>= 1;   /* divide by 2 */
	} while (true);
}

static struct sg_request *
sg_setup_req_ws_helper(struct sg_comm_wr_t *cwrp)
{
	int res;
	struct sg_request *r_srp;
	enum sg_rq_state rs_sr_st;
	struct sg_fd *fp = cwrp->sfp;
	struct sg_fd *rs_sfp = sg_fd_share_ptr(fp);

	if (unlikely(!rs_sfp))
		return ERR_PTR(-EPROTO);
	/*
	 * There may be contention with another potential write-side trying to pair with this
	 * read-side. The loser will receive an EADDRINUSE errno. The winner advances read-side's
	 * rq_state:	SG_RQ_SHR_SWAP --> SG_RQ_SHR_IN_WS
	 */
	if (cwrp->rsv_idx >= 0)
		r_srp = rs_sfp->rsv_arr[cwrp->rsv_idx];
	else
		r_srp = sg_get_probable_read_side(rs_sfp);
	if (unlikely(!r_srp))
		return ERR_PTR(-ENOSTR);

	rs_sr_st = atomic_read(&r_srp->rq_st);
	switch (rs_sr_st) {
	case SG_RQ_SHR_SWAP:
		break;
	case SG_RQ_AWAIT_RCV:
	case SG_RQ_INFLIGHT:
	case SG_RQ_BUSY:
		return ERR_PTR(-EBUSY);	/* too early for write-side req */
	case SG_RQ_INACTIVE:
		SG_LOG(1, fp, "%s: write-side finds read-side inactive\n",
		       __func__);
		return ERR_PTR(-EADDRNOTAVAIL);
	case SG_RQ_SHR_IN_WS:
		SG_LOG(1, fp, "%s: write-side find read-side shr_in_ws\n",
		       __func__);
		return ERR_PTR(-EADDRINUSE);
	}
	res = sg_rq_chg_state(r_srp, rs_sr_st, SG_RQ_SHR_IN_WS);
	if (unlikely(res))
		return ERR_PTR(-EADDRINUSE);
	return r_srp;
}

/*
 * Setup an active request (soon to carry a SCSI command) to the current file
 * descriptor by creating a new one or re-using a request marked inactive.
 * If successful returns a valid pointer to a sg_request object which is in
 * the SG_RQ_BUSY state. On failure returns a negated errno value twisted by
 * ERR_PTR() macro. Note that once a file share is established, the read-side
 * side's reserve request can only be used in a request share.
 */
static struct sg_request *
sg_setup_req(struct sg_comm_wr_t *cwrp, enum sg_shr_var sh_var)
{
	bool allow_rsv = true;		/* see note above */
	bool mk_new_srp = true;
	bool new_rsv_srp = false;
	bool no_reqs = false;
	bool ws_rq = false;
	bool some_inactive = false;
	bool try_harder = false;
	bool second = false;
	bool is_rsv;
	int ra_idx = 0;
	int l_used_idx;
	int dlen = cwrp->dlen;
	u32 sum_dlen;
	unsigned long idx, s_idx, end_idx, iflags;
	enum sg_rq_state sr_st;
	struct sg_fd *fp = cwrp->sfp;
	struct sg_request *r_srp; /* returned value won't be NULL */
	struct sg_request *rs_rsv_srp = NULL;
	struct xarray *xafp = &fp->srp_arr;
	__maybe_unused const char *cp = "";
	__maybe_unused char b[64];

	switch (sh_var) {
	case SG_SHR_RS_RQ:
		cp = "rs_rq";
		ra_idx = (test_bit(SG_FFD_RESHARE, fp->ffd_bm)) ? 0 : sg_get_idx_available(fp);
		if (ra_idx < 0) {
			new_rsv_srp = true;
			goto good_fini;
		}
		r_srp = fp->rsv_arr[ra_idx];
		sr_st = atomic_read(&r_srp->rq_st);
		if (sr_st == SG_RQ_INACTIVE) {
			int res = sg_rq_chg_state(r_srp, sr_st, SG_RQ_BUSY);

			if (unlikely(res)) {
				r_srp = NULL;
			} else {
				r_srp->sh_srp = NULL;
				mk_new_srp = false;
			}
		} else {
			SG_LOG(1, fp, "%s: no reserve request available\n", __func__);
			r_srp = ERR_PTR(-EFBIG);
		}
		if (IS_ERR(r_srp))
			goto err_out;
		if (mk_new_srp)
			new_rsv_srp = true;
		goto good_fini;
	case SG_SHR_WS_RQ:
		cp = "rs_rq";
		rs_rsv_srp = sg_setup_req_ws_helper(cwrp);
		if (IS_ERR(rs_rsv_srp)) {
			r_srp = rs_rsv_srp;
			goto err_out;
		}
		/* write-side dlen may be <= read-side's dlen */
		if (unlikely(dlen + cwrp->wr_offset >
			     rs_rsv_srp->sgatp->dlen)) {
			SG_LOG(1, fp, "%s: bad, write-side dlen [%d] > read-side's\n",
			       __func__, dlen);
			r_srp = ERR_PTR(-E2BIG);
			goto err_out;
		}
		ws_rq = true;
		dlen = 0;	/* any srp for write-side will do, pick smallest */
		break;
	case SG_SHR_RS_NOT_SRQ:
		allow_rsv = false;
		break;
	default:
		break;
	}

start_again:
	if (xa_empty(xafp)) {
		no_reqs = true;
		mk_new_srp = true;
	} else if (atomic_read(&fp->inactives) <= 0) {
		mk_new_srp = true;
	} else if (likely(!try_harder) && dlen < SG_DEF_SECTOR_SZ) {
		struct sg_request *low_srp = NULL;

		l_used_idx = READ_ONCE(fp->low_used_idx);
		s_idx = (l_used_idx < 0) ? 0 : l_used_idx;
		if (l_used_idx >= 0 && xa_get_mark(xafp, s_idx, SG_XA_RQ_INACTIVE)) {
			r_srp = xa_load(xafp, s_idx);
			if (r_srp && (allow_rsv || !test_bit(SG_FRQ_RESERVED, r_srp->frq_bm))) {
				if (r_srp->sgat_h.buflen <= SG_DEF_SECTOR_SZ) {
					if (sg_rq_chg_state(r_srp, SG_RQ_INACTIVE,
							    SG_RQ_BUSY) == 0) {
						mk_new_srp = false;
						atomic_dec(&fp->inactives);
						goto have_existing;
					}
				}
			}
		}
		xa_for_each_marked(xafp, idx, r_srp, SG_XA_RQ_INACTIVE) {
			if (allow_rsv || !test_bit(SG_FRQ_RESERVED, r_srp->frq_bm)) {
				if (r_srp->sgat_h.buflen <= SG_DEF_SECTOR_SZ) {
					if (sg_rq_chg_state(r_srp, SG_RQ_INACTIVE, SG_RQ_BUSY))
						continue;
					atomic_dec(&fp->inactives);
					mk_new_srp = false;
					break;
				} else if (!low_srp) {
					low_srp = r_srp;
				}
			}
		}
		if (mk_new_srp && low_srp) {	/* no candidate yet */
			/* take non-NULL low_srp, irrespective of r_srp->sgat_h.buflen size */
			r_srp = low_srp;
			if (sg_rq_chg_state(r_srp, SG_RQ_INACTIVE, SG_RQ_BUSY) == 0) {
				mk_new_srp = false;
				atomic_dec(&fp->inactives);
			}
		}
	} else {
		cp = "larger from srp_arr";
		l_used_idx = READ_ONCE(fp->low_used_idx);
		s_idx = (l_used_idx < 0) ? 0 : l_used_idx;
		idx = s_idx;
		end_idx = ULONG_MAX;

		if (allow_rsv) {
second_time:
			for (r_srp = xa_find(xafp, &idx, end_idx, SG_XA_RQ_INACTIVE);
			     r_srp;
			     r_srp = xa_find_after(xafp, &idx, end_idx, SG_XA_RQ_INACTIVE)) {
				if (r_srp->sgat_h.buflen >= dlen) {
					if (sg_rq_chg_state(r_srp, SG_RQ_INACTIVE, SG_RQ_BUSY))
						continue;
					atomic_dec(&fp->inactives);
					WRITE_ONCE(fp->low_used_idx, idx + 1);
					mk_new_srp = false;
					break;
				}
			}
			if (!r_srp && !second && s_idx > 0) {
				end_idx = s_idx - 1;
				s_idx = 0;
				idx = s_idx;
				second = true;
				goto second_time;
			}
		} else {
second_time_2:
			for (r_srp = xa_find(xafp, &idx, end_idx, SG_XA_RQ_INACTIVE);
			     r_srp;
			     r_srp = xa_find_after(xafp, &idx, end_idx, SG_XA_RQ_INACTIVE)) {
				if (r_srp->sgat_h.buflen >= dlen &&
				    !test_bit(SG_FRQ_RESERVED, r_srp->frq_bm)) {
					if (sg_rq_chg_state(r_srp, SG_RQ_INACTIVE, SG_RQ_BUSY))
						continue;
					atomic_dec(&fp->inactives);
					WRITE_ONCE(fp->low_used_idx, idx + 1);
					mk_new_srp = false;
					break;
				}
			}
			if (!r_srp && !second && s_idx > 0) {
				end_idx = s_idx - 1;
				s_idx = 0;
				idx = s_idx;
				second = true;
				goto second_time_2;
			}
		}
	}
have_existing:
	if (!mk_new_srp) {
		r_srp->in_resid = 0;
		r_srp->rq_info = 0;
		r_srp->sense_len = 0;
	}

good_fini:
	if (mk_new_srp) {	/* Need new sg_request object */
		bool disallow_cmd_q = test_bit(SG_FFD_NO_CMD_Q, fp->ffd_bm);
		int res;
		u32 n_idx;

		cp = "new";
		r_srp = NULL;
		if (disallow_cmd_q && atomic_read(&fp->submitted) > 0) {
			r_srp = ERR_PTR(-EDOM);
			SG_LOG(6, fp, "%s: trying 2nd req but cmd_q=false\n",
			       __func__);
			goto err_out;
		} else if (fp->tot_fd_thresh > 0) {
			sum_dlen = atomic_read(&fp->sum_fd_dlens) + dlen;
			if (unlikely(sum_dlen > (u32)fp->tot_fd_thresh)) {
				r_srp = ERR_PTR(-E2BIG);
				SG_LOG(2, fp, "%s: sum_of_dlen(%u) > %s\n",
				       __func__, sum_dlen, "tot_fd_thresh");
			}
		}
		if (!IS_ERR(r_srp) && new_rsv_srp) {
			ra_idx = sg_get_idx_new(fp);
			if (ra_idx < 0) {
				ra_idx = sg_get_idx_available(fp);
				if (ra_idx < 0) {
					SG_LOG(1, fp,
					       "%s: no read-side reqs available\n",
					       __func__);
					r_srp = ERR_PTR(-EFBIG);
				}
			}
		}
		if (IS_ERR(r_srp))	/* NULL is _not_ an ERR here */
			goto err_out;
		r_srp = sg_mk_srp_sgat(fp, no_reqs, dlen);
		if (IS_ERR(r_srp)) {
			if (!try_harder && dlen < SG_DEF_SECTOR_SZ &&
			    some_inactive) {
				try_harder = true;
				goto start_again;
			}
			goto err_out;
		}
		SG_LOG(4, fp, "%s: %smk_new_srp=0x%pK ++\n", __func__,
		       (new_rsv_srp ? "rsv " : ""), r_srp);
		if (new_rsv_srp) {
			fp->rsv_arr[ra_idx] = r_srp;
			set_bit(SG_FRQ_RESERVED, r_srp->frq_bm);
			r_srp->sh_srp = NULL;
		}
		xa_lock_irqsave(xafp, iflags);
		res = __xa_alloc(xafp, &n_idx, r_srp, xa_limit_32b, GFP_ATOMIC);
		xa_unlock_irqrestore(xafp, iflags);
		if (unlikely(res < 0)) {
			xa_unlock_irqrestore(xafp, iflags);
			sg_remove_srp(r_srp);
			kfree(r_srp);
			r_srp = ERR_PTR(-EPROTOTYPE);
			SG_LOG(1, fp, "%s: xa_alloc() failed, errno=%d\n",
			       __func__,  -res);
			goto err_out;
		}
		r_srp->rq_idx = n_idx;
		r_srp->parentfp = fp;
		xa_unlock_irqrestore(xafp, iflags);
	}
	/* keep SG_FRQ_RESERVED setting from prior/new r_srp; clear rest */
	is_rsv = test_bit(SG_FRQ_RESERVED, r_srp->frq_bm);
	WRITE_ONCE(r_srp->frq_bm[0], 0);
	if (is_rsv)
		set_bit(SG_FRQ_RESERVED, r_srp->frq_bm);
	/* r_srp inherits these 3 flags from cwrp->frq_bm */
	if (test_bit(SG_FRQ_IS_V4I, cwrp->frq_bm))
		set_bit(SG_FRQ_IS_V4I, r_srp->frq_bm);
	if (test_bit(SG_FRQ_SYNC_INVOC, cwrp->frq_bm))
		set_bit(SG_FRQ_SYNC_INVOC, r_srp->frq_bm);
	r_srp->sgatp->dlen = dlen;	/* must be <= r_srp->sgat_h.buflen */
	r_srp->sh_var = sh_var;
	r_srp->cmd_opcode = 0xff;  /* set invalid opcode (VS), 0x0 is TUR */
	/* If setup stalls (e.g. blk_get_request()) debug shows 'elap=1 ns' */
	if (test_bit(SG_FFD_TIME_IN_NS, fp->ffd_bm))
		r_srp->start_ns = S64_MAX;
	if (ws_rq && rs_rsv_srp) {
		/* write-side "shares" the read-side reserve request's data buffer */
		r_srp->sgatp = &rs_rsv_srp->sgat_h;
		rs_rsv_srp->sh_srp = r_srp;
		r_srp->sh_srp = rs_rsv_srp;
	} else if (sh_var == SG_SHR_RS_RQ && test_bit(SG_FFD_READ_SIDE_ERR, fp->ffd_bm)) {
		clear_bit(SG_FFD_READ_SIDE_ERR, fp->ffd_bm);
	}
err_out:
#if IS_ENABLED(SG_LOG_ACTIVE)
	if (IS_ERR(r_srp)) {
		int err = -PTR_ERR(r_srp);

		if (err == EBUSY)
			SG_LOG(4, fp, "%s: EBUSY (as ptr err)\n", __func__);
		else
			SG_LOG(1, fp, "%s: err=%d\n", __func__, err);
	} else {
		SG_LOG(4, fp, "%s: %s %sr_srp=0x%pK\n", __func__, cp,
		       sg_get_rsv_str_lck(r_srp, "[", "] ", sizeof(b), b),
		       r_srp);
	}
#endif
	return r_srp;
}

/*
 * Sets srp to SG_RQ_INACTIVE unless it was in SG_RQ_SHR_SWAP state. Also
 * change the asociated xarray entry flags to be consistent with
 * SG_RQ_INACTIVE. Since this function can be called from many contexts,
 * then assume no xa locks held.
 * The state machine should insure that two threads should never race here.
 */
static void
sg_deact_request(struct sg_fd *sfp, struct sg_request *srp)
{
	bool is_rsv;
	enum sg_rq_state sr_st;
	u8 *sbp;

	if (WARN_ON(!sfp || !srp))
		return;
	SG_LOG(3, sfp, "%s: srp=%pK\n", __func__, srp);
	sbp = srp->sense_bp;
	srp->sense_bp = NULL;
	sr_st = atomic_read(&srp->rq_st);
	if (sr_st != SG_RQ_SHR_SWAP) {
		/*
		 * Can be called from many contexts and it is hard to know
		 * whether xa locks held. So assume not.
		 */
		sg_rq_chg_state_force(srp, SG_RQ_INACTIVE);
		atomic_inc(&sfp->inactives);
		is_rsv = test_bit(SG_FRQ_RESERVED, srp->frq_bm);
		WRITE_ONCE(srp->frq_bm[0], 0);
		if (is_rsv)
			__set_bit(SG_FRQ_RESERVED, srp->frq_bm);
		srp->tag = SG_TAG_WILDCARD;
		srp->in_resid = 0;
		srp->rq_info = 0;
		srp->sense_len = 0;
	}
	/* maybe orphaned req, thus never read */
	if (sbp)
		mempool_free(sbp, sg_sense_pool);
}

/* Returns pointer to sg_fd object or negated errno twisted by ERR_PTR */
static struct sg_fd *
sg_add_sfp(struct sg_device *sdp, struct file *filp)
{
	bool reduced = false;
	int rbuf_len, res;
	u32 idx;
	long err;
	unsigned long iflags;
	struct sg_fd *sfp;
	struct sg_request *srp = NULL;
	struct xarray *xafp;
	struct xarray *xadp;

	sfp = kzalloc(sizeof(*sfp), GFP_ATOMIC | __GFP_NOWARN);
	if (unlikely(!sfp))
		return ERR_PTR(-ENOMEM);
	init_waitqueue_head(&sfp->cmpl_wait);
	xa_init_flags(&sfp->srp_arr, XA_FLAGS_ALLOC | XA_FLAGS_LOCK_IRQ);
	kref_init(&sfp->f_ref);		/* init to 1; put: sg_release() */
	mutex_init(&sfp->f_mutex);
	sfp->timeout = SG_DEFAULT_TIMEOUT;
	sfp->timeout_user = SG_DEFAULT_TIMEOUT_USER;
	sfp->filp = filp;
	/* other bits in sfp->ffd_bm[1] cleared by kzalloc() above */
	__assign_bit(SG_FFD_FORCE_PACKID, sfp->ffd_bm, SG_DEF_FORCE_PACK_ID);
	__assign_bit(SG_FFD_NO_CMD_Q, sfp->ffd_bm, !SG_DEF_COMMAND_Q);
	__assign_bit(SG_FFD_KEEP_ORPHAN, sfp->ffd_bm, SG_DEF_KEEP_ORPHAN);
	__assign_bit(SG_FFD_TIME_IN_NS, sfp->ffd_bm, SG_DEF_TIME_UNIT);
	__assign_bit(SG_FFD_Q_AT_TAIL, sfp->ffd_bm, SG_DEFAULT_Q_AT);
	sfp->tot_fd_thresh = SG_TOT_FD_THRESHOLD;
	atomic_set(&sfp->sum_fd_dlens, 0);
	atomic_set(&sfp->submitted, 0);
	atomic_set(&sfp->waiting, 0);
	atomic_set(&sfp->inactives, 0);
	/*
	 * SG_SCATTER_SZ initializes scatter_elem_sz but different value may
	 * be given as driver/module parameter (e.g. 'scatter_elem_sz=8192').
	 * Any user provided number will be changed to be PAGE_SIZE as a
	 * minimum, otherwise it will be rounded down (if required) to a
	 * power of 2. So it will always be a power of 2.
	 */
	sfp->sgat_elem_sz = scatter_elem_sz;
	sfp->parentdp = sdp;

	if (SG_IS_DETACHING(sdp)) {
		SG_LOG(1, sfp, "%s: sg%u detaching\n", __func__, sdp->index);
		kfree(sfp);
		return ERR_PTR(-ENODEV);
	}
	if (unlikely(sg_big_buff != def_reserved_size))
		sg_big_buff = def_reserved_size;

	rbuf_len = min_t(int, sg_big_buff, sdp->max_sgat_sz);
	if (rbuf_len > 0) {
		xafp = &sfp->srp_arr;
		srp = sg_build_reserve(sfp, rbuf_len);
		if (IS_ERR(srp)) {
			err = PTR_ERR(srp);
			SG_LOG(1, sfp, "%s: build reserve err=%ld\n", __func__,
			       -err);
			kfree(sfp);
			return ERR_PTR(err);
		}
		if (srp->sgatp->buflen < rbuf_len) {
			reduced = true;
			SG_LOG(2, sfp,
			       "%s: reserve reduced from %d to buflen=%d\n",
			       __func__, rbuf_len, srp->sgatp->buflen);
		}
		xa_lock_irqsave(xafp, iflags);
		res = __xa_alloc(xafp, &idx, srp, xa_limit_32b, GFP_ATOMIC);
		if (res < 0) {
			SG_LOG(1, sfp, "%s: xa_alloc(srp) bad, errno=%d\n",
			       __func__,  -res);
			xa_unlock_irqrestore(xafp, iflags);
			sg_remove_srp(srp);
			kfree(srp);
			kfree(sfp);
			return ERR_PTR(-EPROTOTYPE);
		}
		srp->rq_idx = idx;
		srp->parentfp = sfp;
		__set_bit(SG_FRQ_RESERVED, srp->frq_bm);
		sg_rq_chg_state_force_ulck(srp, SG_RQ_INACTIVE);
		atomic_inc(&sfp->inactives);
		xa_unlock_irqrestore(xafp, iflags);
	}
	if (!reduced) {
		SG_LOG(4, sfp, "%s: built reserve buflen=%d\n", __func__,
		       rbuf_len);
	}
	xadp = &sdp->sfp_arr;
	xa_lock_irqsave(xadp, iflags);
	res = __xa_alloc(xadp, &idx, sfp, xa_limit_32b, GFP_ATOMIC);
	if (unlikely(res < 0)) {
		xa_unlock_irqrestore(xadp, iflags);
		pr_warn("%s: xa_alloc(sdp) bad, o_count=%d, errno=%d\n",
			__func__, atomic_read(&sdp->open_cnt), -res);
		if (srp) {
			sg_remove_srp(srp);
			kfree(srp);
		}
		kfree(sfp);
		return ERR_PTR(res);
	}
	sfp->idx = idx;
	__xa_set_mark(xadp, idx, SG_XA_FD_UNSHARED);
	xa_unlock_irqrestore(xadp, iflags);
	kref_get(&sdp->d_ref);	/* put in: sg_uc_remove_sfp() */
	__module_get(THIS_MODULE);
	SG_LOG(3, sfp, "%s: success, sfp=0x%pK ++\n", __func__, sfp);
	return sfp;
}

/*
 * A successful call to sg_release() will result, at some later time, to this
 * "user context" function being invoked. All requests associated with this
 * file descriptor should be completed or cancelled when this function is
 * called (due to sfp->f_ref). Also the file descriptor itself has not been
 * accessible since it was list_del()-ed by the preceding sg_remove_sfp()
 * call. So no locking is required. sdp should never be NULL but to make
 * debugging more robust, this function will not blow up in that case.
 */
static void
sg_uc_remove_sfp(struct work_struct *work)
{
	__maybe_unused int o_count;
	int subm;
	unsigned long idx, iflags;
	struct sg_device *sdp;
	struct sg_fd *sfp = container_of(work, struct sg_fd, ew_fd.work);
	struct sg_fd *e_sfp;
	struct sg_request *srp;
	struct sg_request *e_srp;
	struct xarray *xafp = &sfp->srp_arr;
	struct xarray *xadp;

	if (unlikely(!sfp)) {
		pr_warn("sg: %s: sfp is NULL\n", __func__);
		return;
	}
	sdp = sfp->parentdp;

	/* Cleanup any responses which were never read(). */
	xa_for_each(xafp, idx, srp) {
		if (!xa_get_mark(xafp, srp->rq_idx, SG_XA_RQ_INACTIVE))
			sg_finish_scsi_blk_rq(srp);
		if (srp->sgatp->buflen > 0)
			sg_remove_srp(srp);
		if (unlikely(srp->sense_bp)) {
			mempool_free(srp->sense_bp, sg_sense_pool);
			srp->sense_bp = NULL;
		}
		xa_lock_irqsave(xafp, iflags);
		e_srp = __xa_erase(xafp, srp->rq_idx);
		xa_unlock_irqrestore(xafp, iflags);
		if (unlikely(srp != e_srp))
			SG_LOG(1, sfp, "%s: xa_erase() return unexpected\n",
			       __func__);
		SG_LOG(6, sfp, "%s: kfree: srp=%pK --\n", __func__, srp);
		kfree(srp);
	}
	subm = atomic_read(&sfp->submitted);
	if (subm != 0)
		SG_LOG(1, sfp, "%s: expected submitted=0 got %d\n",
		       __func__, subm);
	if (sfp->efd_ctxp)
		eventfd_ctx_put(sfp->efd_ctxp);
	xa_destroy(xafp);
	xadp = &sdp->sfp_arr;
	xa_lock_irqsave(xadp, iflags);
	e_sfp = __xa_erase(xadp, sfp->idx);
	xa_unlock_irqrestore(xadp, iflags);
	if (unlikely(sfp != e_sfp))
		SG_LOG(1, sfp, "%s: xa_erase() return unexpected\n",
		       __func__);
	o_count = atomic_dec_return(&sdp->open_cnt);
	SG_LOG(3, sfp, "%s: dev o_count after=%d: sfp=0x%pK --\n", __func__,
	       o_count, sfp);
	kfree(sfp);

	scsi_device_put(sdp->device);
	kref_put(&sdp->d_ref, sg_device_destroy);	/* get: sg_add_sfp() */
	module_put(THIS_MODULE);
}

static void
sg_remove_sfp(struct kref *kref)
{
	struct sg_fd *sfp = container_of(kref, struct sg_fd, f_ref);

	INIT_WORK(&sfp->ew_fd.work, sg_uc_remove_sfp);
	schedule_work(&sfp->ew_fd.work);
}

static struct sg_device *
sg_lookup_dev(int dev)
	__must_hold(&sg_index_lock)
{
	return idr_find(&sg_index_idr, dev);
}

/*
 * Returns valid pointer to a sg_device object on success or a negated
 * errno value on failure. Does not return NULL.
 */
static struct sg_device *
sg_get_dev(int min_dev)
{
	struct sg_device *sdp;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = sg_lookup_dev(min_dev);
	if (unlikely(!sdp))
		sdp = ERR_PTR(-ENXIO);
	else if (SG_IS_DETACHING(sdp)) {
		/* If detaching, then the refcount may already be 0, in
		 * which case it would be a bug to do kref_get().
		 */
		sdp = ERR_PTR(-ENODEV);
	} else
		kref_get(&sdp->d_ref);	/* put: sg_open() */
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return sdp;
}

#if IS_ENABLED(SG_PROC_OR_DEBUG_FS)
static const char *
sg_rq_st_str(enum sg_rq_state rq_st, bool long_str)
{
	switch (rq_st) {	/* request state */
	case SG_RQ_INACTIVE:
		return long_str ? "inactive" :  "ina";
	case SG_RQ_INFLIGHT:
		return long_str ? "inflight" : "act";
	case SG_RQ_AWAIT_RCV:
		return long_str ? "await_receive" : "rcv";
	case SG_RQ_BUSY:	/* state transitioning */
		return long_str ? "busy" : "bsy";
	case SG_RQ_SHR_SWAP:	/* read-side: awaiting write-side req start */
		return long_str ? "share swap" : "s_wp";
	case SG_RQ_SHR_IN_WS:	/* read-side: waiting for inflight write-side */
		return long_str ? "share write-side active" : "ws_a";
	default:
		return long_str ? "unknown" : "unk";
	}
}

static const char *
sg_shr_str(enum sg_shr_var sh_var, bool long_str)
{
	switch (sh_var) {	/* share variety of request */
	case SG_SHR_NONE:
		return long_str ? "none" :  "-";
	case SG_SHR_RS_RQ:
		return long_str ? "read-side request" :  "rs_rq";
	case SG_SHR_RS_NOT_SRQ:
		return long_str ? "read-side, not share request" :  "rs_nsh";
	case SG_SHR_WS_RQ:
		return long_str ? "write-side request" :  "ws_rq";
	case SG_SHR_WS_NOT_SRQ:
		return long_str ? "write-side, not share request" :  "ws_nsh";
	default:
		return long_str ? "unknown" : "unk";
	}
}

#elif IS_ENABLED(SG_LOG_ACTIVE)

static const char *
sg_rq_st_str(enum sg_rq_state rq_st, bool long_str)
{
	return "";
}

static const char *
sg_shr_str(enum sg_shr_var sh_var, bool long_str)
{
	return "";
}
#endif

#if IS_ENABLED(SG_PROC_OR_DEBUG_FS)

#define SG_SNAPSHOT_DEV_MAX 4

/*
 * For snapshot_devs array, -1 or two adjacent the same is terminator.
 * -1 in first element of first two elements the same implies all.
 */
static struct sg_dfs_context_t {
	struct dentry *dfs_rootdir;
	int snapshot_devs[SG_SNAPSHOT_DEV_MAX];
} sg_dfs_cxt;

struct sg_proc_deviter {
	loff_t index;
	size_t max;
	int fd_index;
};

static int
sg_idr_max_id(int id, void *p, void *data)
		__must_hold(&sg_index_lock)
{
	int *k = data;

	if (*k < id)
		*k = id;
	return 0;
}

static int
sg_last_dev(void)
{
	int k = -1;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	idr_for_each(&sg_index_idr, sg_idr_max_id, &k);
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return k + 1;		/* origin 1 */
}

static void *
dev_seq_start(struct seq_file *s, loff_t *pos)
{
	struct sg_proc_deviter *it = kzalloc(sizeof(*it), GFP_KERNEL);

	s->private = it;
	if (unlikely(!it))
		return NULL;

	it->index = *pos;
	it->max = sg_last_dev();
	if (it->index >= (int)it->max)
		return NULL;
	return it;
}

static void *
dev_seq_next(struct seq_file *s, void *v, loff_t *pos)
{
	struct sg_proc_deviter *it = s->private;

	*pos = ++it->index;
	return (it->index < (int)it->max) ? it : NULL;
}

static void
dev_seq_stop(struct seq_file *s, void *v)
{
	kfree(s->private);
}

#endif			/* SG_PROC_OR_DEBUG_FS */

#if IS_ENABLED(CONFIG_SCSI_PROC_FS)     /* around 100 lines */

static int
sg_proc_seq_show_int(struct seq_file *s, void *v)
{
	seq_printf(s, "%d\n", *((int *)s->private));
	return 0;
}

static int
sg_proc_single_open_adio(struct inode *inode, struct file *filp)
{
	return single_open(filp, sg_proc_seq_show_int, &sg_allow_dio);
}

/* Kept for backward compatibility. sg_allow_dio is now ignored. */
static ssize_t
sg_proc_write_adio(struct file *filp, const char __user *buffer,
		   size_t count, loff_t *off)
{
	int err;
	unsigned long num;

	if (unlikely(!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO)))
		return -EACCES;
	err = kstrtoul_from_user(buffer, count, 0, &num);
	if (unlikely(err))
		return err;
	sg_allow_dio = num ? 1 : 0;
	return count;
}

static int
sg_proc_single_open_dressz(struct inode *inode, struct file *filp)
{
	return single_open(filp, sg_proc_seq_show_int, &sg_big_buff);
}

static ssize_t
sg_proc_write_dressz(struct file *filp, const char __user *buffer,
		     size_t count, loff_t *off)
{
	int err;
	unsigned long k = ULONG_MAX;

	if (unlikely(!capable(CAP_SYS_ADMIN) || !capable(CAP_SYS_RAWIO)))
		return -EACCES;

	err = kstrtoul_from_user(buffer, count, 0, &k);
	if (unlikely(err))
		return err;
	if (likely(k <= 1048576)) {	/* limit "big buff" to 1 MB */
		sg_big_buff = k;
		return count;
	}
	return -EDOM;
}

static int
sg_proc_seq_show_version(struct seq_file *s, void *v)
{
	seq_printf(s, "%d\t%s [%s]\n", sg_version_num, SG_VERSION_STR,
		   sg_version_date);
	return 0;
}

static int
sg_proc_seq_show_devhdr(struct seq_file *s, void *v)
{
	seq_puts(s, "host\tchan\tid\tlun\ttype\topens\tqdepth\tbusy\tonline\n");
	return 0;
}

static int
sg_proc_seq_show_dev(struct seq_file *s, void *v)
{
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	struct scsi_device *scsidp;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	if (unlikely(!sdp || !sdp->device || SG_IS_DETACHING(sdp)))
		seq_puts(s, "-1\t-1\t-1\t-1\t-1\t-1\t-1\t-1\t-1\n");
	else {
		scsidp = sdp->device;
		seq_printf(s, "%d\t%d\t%d\t%llu\t%d\t%d\t%d\t%d\t%d\n",
			      scsidp->host->host_no, scsidp->channel,
			      scsidp->id, scsidp->lun, (int)scsidp->type,
			      1,
			      (int)scsidp->queue_depth,
			      (int)scsi_device_busy(scsidp),
			      (int)scsi_device_online(scsidp));
	}
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

static int
sg_proc_seq_show_devstrs(struct seq_file *s, void *v)
{
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	struct scsi_device *scsidp;
	unsigned long iflags;

	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	scsidp = sdp ? sdp->device : NULL;
	if (sdp && scsidp && !SG_IS_DETACHING(sdp))
		seq_printf(s, "%8.8s\t%16.16s\t%4.4s\n",
			   scsidp->vendor, scsidp->model, scsidp->rev);
	else
		seq_puts(s, "<no active device>\n");
	read_unlock_irqrestore(&sg_index_lock, iflags);
	return 0;
}

#endif		/* CONFIG_SCSI_PROC_FS (~100 lines back) */

#if IS_ENABLED(SG_PROC_OR_DEBUG_FS)

/* Writes debug info for one sg_request in obp buffer */
static int
sg_proc_debug_sreq(struct sg_request *srp, int to, bool t_in_ns, char *obp,
		   int len)
{
	bool is_v3v4, v4, is_dur;
	int n = 0;
	u32 dur;
	enum sg_rq_state rq_st;
	const char *cp;
	const char *tp = t_in_ns ? "ns" : "ms";
	char b[32];

	if (unlikely(len < 1))
		return 0;
	v4 = SG_IS_V4I(srp);
	is_v3v4 = v4 ? true : (srp->s_hdr3.interface_id != '\0');
	sg_get_rsv_str(srp, "     ", "", sizeof(b), b);
	if (strlen(b) > 5)
		cp = (is_v3v4 && (srp->rq_flags & SG_FLAG_MMAP_IO)) ?
					" mmap" : "";
	else
		cp = (srp->rq_info & SG_INFO_DIRECT_IO_MASK) ? " dio" : "";
	rq_st = atomic_read(&srp->rq_st);
	dur = sg_get_dur(srp, &rq_st, t_in_ns, &is_dur);
	n += scnprintf(obp + n, len - n, "%s%s>> %s:%d dlen=%d/%d id=%d", b,
		       cp, sg_rq_st_str(rq_st, false), srp->rq_idx, srp->sgatp->dlen,
		       srp->sgatp->buflen, (int)srp->pack_id);
	if (test_bit(SG_FFD_NO_DURATION, srp->parentfp->ffd_bm))
		;
	else if (is_dur)	/* cmd/req has completed, waiting for ... */
		n += scnprintf(obp + n, len - n, " dur=%u%s", dur, tp);
	else if (dur < U32_MAX) { /* in-flight or busy (so ongoing) */
		if ((srp->rq_flags & SGV4_FLAG_YIELD_TAG) &&
		    srp->tag != SG_TAG_WILDCARD)
			n += scnprintf(obp + n, len - n, " tag=0x%x",
				       srp->tag);
		n += scnprintf(obp + n, len - n, " t_o/elap=%us/%u%s",
			       to / 1000, dur, tp);
	}
	if (srp->sh_var != SG_SHR_NONE)
		n += scnprintf(obp + n, len - n, " shr=%s",
			       sg_shr_str(srp->sh_var, false));
	if (srp->sgatp->num_sgat > 1)
		n += scnprintf(obp + n, len - n, " sgat=%d", srp->sgatp->num_sgat);
	cp = (srp->rq_flags & SGV4_FLAG_HIPRI) ? "hipri " : "";
	n += scnprintf(obp + n, len - n, " %sop=0x%02x\n", cp, srp->cmd_opcode);
	return n;
}

/* Writes debug info for one sg fd (including its sg requests) in obp buffer */
static int
sg_proc_debug_fd(struct sg_fd *fp, char *obp, int len, unsigned long idx,
		 bool reduced)
{
	bool set_debug;
	bool t_in_ns = test_bit(SG_FFD_TIME_IN_NS, fp->ffd_bm);
	int n = 0;
	int to, k;
	unsigned long iflags;
	const char *cp;
	struct sg_request *srp = fp->rsv_arr[0];
	struct sg_device *sdp = fp->parentdp;

	if (sg_fd_is_shared(fp))
		cp = xa_get_mark(&sdp->sfp_arr, fp->idx, SG_XA_FD_RS_SHARE) ?
			" shr_rs" : " shr_rs";
	else
		cp = "";
	set_debug = test_bit(SG_FDEV_LOG_SENSE, sdp->fdev_bm);
	/* sgat=-1 means unavailable */
	to = (fp->timeout >= 0) ? jiffies_to_msecs(fp->timeout) : -999;
	if (to < 0)
		n += scnprintf(obp + n, len - n, "BAD timeout=%d",
			       fp->timeout);
	else if (to % 1000)
		n += scnprintf(obp + n, len - n, "timeout=%dms rs", to);
	else
		n += scnprintf(obp + n, len - n, "timeout=%ds rs", to / 1000);
	n += scnprintf(obp + n, len - n, "v_buflen=%d%s fd_idx=%lu\n  ",
		       (srp ? srp->sgatp->buflen : -1), cp, idx);
	if (test_bit(SG_FFD_NO_CMD_Q, fp->ffd_bm))
		n += scnprintf(obp + n, len - n, " no_cmd_q");
	if (test_bit(SG_FFD_FORCE_PACKID, fp->ffd_bm))
		n += scnprintf(obp + n, len - n, " force_packid");
	if (test_bit(SG_FFD_KEEP_ORPHAN, fp->ffd_bm))
		n += scnprintf(obp + n, len - n, " keep_orphan");
	if (test_bit(SG_FFD_EXCL_WAITQ, fp->ffd_bm))
		n += scnprintf(obp + n, len - n, " excl_waitq");
	if (test_bit(SG_FFD_SVB_ACTIVE, fp->ffd_bm))
		n += scnprintf(obp + n, len - n, " svb");
	n += scnprintf(obp + n, len - n, " fd_bm=0x%lx\n", fp->ffd_bm[0]);
	n += scnprintf(obp + n, len - n,
		       "   mmap_sz=%d low_used_idx=%d low_await_idx=%d sum_fd_dlens=%u\n",
		       fp->mmap_sz, READ_ONCE(fp->low_used_idx), READ_ONCE(fp->low_await_idx),
		       atomic_read(&fp->sum_fd_dlens));
	n += scnprintf(obp + n, len - n,
		       "   submitted=%d waiting=%d inactives=%d   open thr_id=%d\n",
		       atomic_read(&fp->submitted),
		       atomic_read(&fp->waiting), atomic_read(&fp->inactives), fp->tid);
	if (reduced)
		return n;
	k = 0;
	xa_lock_irqsave(&fp->srp_arr, iflags);
	xa_for_each(&fp->srp_arr, idx, srp) {
		if (srp->rq_idx != (unsigned long)idx)
			n += scnprintf(obp + n, len - n,
				       ">>> xa_index=%lu, rq_idx=%d, bad\n",
				       idx, srp->rq_idx);
		if (xa_get_mark(&fp->srp_arr, idx, SG_XA_RQ_INACTIVE))
			continue;
		if (set_debug)
			n += scnprintf(obp + n, len - n, "     rq_bm=0x%lx",
				       srp->frq_bm[0]);
		else if (test_bit(SG_FRQ_ABORTING, srp->frq_bm))
			n += scnprintf(obp + n, len - n,
				       "     abort>> ");
		n += sg_proc_debug_sreq(srp, fp->timeout, t_in_ns, obp + n,
					len - n);
		++k;
		if ((k % 8) == 0) {	/* don't hold up isr_s too long */
			xa_unlock_irqrestore(&fp->srp_arr, iflags);
			cpu_relax();
			xa_lock_irqsave(&fp->srp_arr, iflags);
		}
	}
	if (k == 0)
		n += scnprintf(obp + n, len - n, "     No requests active\n");
	k = 0;
	xa_for_each_marked(&fp->srp_arr, idx, srp, SG_XA_RQ_INACTIVE) {
		if (k == 0)
			n += scnprintf(obp + n, len - n, "   Inactives:\n");
		if (set_debug)
			n += scnprintf(obp + n, len - n, "     rq_bm=0x%lx",
				       srp->frq_bm[0]);
		n += sg_proc_debug_sreq(srp, fp->timeout, t_in_ns,
					obp + n, len - n);
		++k;
		if ((k % 8) == 0) {	/* don't hold up isr_s too long */
			xa_unlock_irqrestore(&fp->srp_arr, iflags);
			cpu_relax();
			xa_lock_irqsave(&fp->srp_arr, iflags);
		}
	}
	xa_unlock_irqrestore(&fp->srp_arr, iflags);
	return n;
}

/* Writes debug info for one sg device (including its sg fds) in obp buffer */
static int
sg_proc_debug_sdev(struct sg_device *sdp, char *obp, int len,
		   int *fd_counterp, bool reduced)
{
	int n = 0;
	int my_count = 0;
	unsigned long idx;
	struct scsi_device *ssdp = sdp->device;
	struct sg_fd *fp;
	char *disk_name;
	int *countp;

	countp = fd_counterp ? fd_counterp : &my_count;
	disk_name = (sdp->disk ? sdp->disk->disk_name : "?_?");
	n += scnprintf(obp + n, len - n, " >>> device=%s ", disk_name);
	n += scnprintf(obp + n, len - n, "%d:%d:%d:%llu ", ssdp->host->host_no,
		       ssdp->channel, ssdp->id, ssdp->lun);
	n += scnprintf(obp + n, len - n,
		       "  max_sgat_sz,elems=2^%d,%d excl=%d open_cnt=%d\n",
		       ilog2(sdp->max_sgat_sz), sdp->max_sgat_elems,
		       SG_HAVE_EXCLUDE(sdp), atomic_read(&sdp->open_cnt));
	xa_for_each(&sdp->sfp_arr, idx, fp) {
		++*countp;
		n += scnprintf(obp + n, len - n, "  FD(%d): ", *countp);
		n += sg_proc_debug_fd(fp, obp + n, len - n, idx, reduced);
	}
	return n;
}

static int
sg_proc_seq_show_debug(struct seq_file *s, void *v, bool reduced)
{
	bool found = false;
	bool trunc = false;
	const int bp_len = SG_PROC_DEBUG_SZ;
	int j, sd_n;
	int n = 0;
	int k = 0;
	unsigned long iflags;
	struct sg_proc_deviter *it = (struct sg_proc_deviter *)v;
	struct sg_device *sdp;
	int *fdi_p;
	const int *dev_arr = sg_dfs_cxt.snapshot_devs;
	char *bp;
	char *disk_name;
	char b1[128];

	b1[0] = '\0';
	if (it && it->index == 0)
		seq_printf(s, "max_active_device=%d  def_reserved_size=%d\n",
			   (int)it->max, def_reserved_size);
	fdi_p = it ? &it->fd_index : &k;
	bp = kzalloc(bp_len, __GFP_NOWARN | GFP_KERNEL);
	if (unlikely(!bp)) {
		seq_printf(s, "%s: Unable to allocate %d on heap, finish\n",
			   __func__, bp_len);
		return -ENOMEM;
	}
	read_lock_irqsave(&sg_index_lock, iflags);
	sdp = it ? sg_lookup_dev(it->index) : NULL;
	if (unlikely(!sdp))
		goto skip;
	sd_n = dev_arr[0];
	if (sd_n != -1 && sd_n != sdp->index && sd_n != dev_arr[1]) {
		for (j = 1; j < SG_SNAPSHOT_DEV_MAX; ) {
			sd_n = dev_arr[j];
			if (sd_n < 0)
				goto skip;
			++j;
			if (j >= SG_SNAPSHOT_DEV_MAX) {
				if (sd_n == sdp->index) {
					found = true;
					break;
				}
			} else if (sd_n == dev_arr[j]) {
				goto skip;
			} else if (sd_n == sdp->index) {
				found = true;
				break;
			}
		}
		if (!found)
			goto skip;
		found = false;
	}
	if (!xa_empty(&sdp->sfp_arr)) {
		found = true;
		disk_name = (sdp->disk ? sdp->disk->disk_name : "?_?");
		if (SG_IS_DETACHING(sdp)) {
			snprintf(b1, sizeof(b1), " >>> %s %s\n", disk_name,
				 "detaching pending close\n");
		} else if (sdp->device) {
			n = sg_proc_debug_sdev(sdp, bp, bp_len, fdi_p,
					       reduced);
			if (n >= bp_len - 1) {
				trunc = true;
				if (bp[bp_len - 2] != '\n')
					bp[bp_len - 2] = '\n';
			}
		} else {
			snprintf(b1, sizeof(b1), " >>> device=%s  %s\n",
				 disk_name, "sdp->device==NULL, skip");
		}
	}
skip:
	read_unlock_irqrestore(&sg_index_lock, iflags);
	if (found) {
		if (n > 0) {
			seq_puts(s, bp);
			if (seq_has_overflowed(s))
				goto s_ovfl;
			if (trunc)
				seq_printf(s, "   >> Output truncated %s\n",
					   "due to buffer size");
		} else if (b1[0]) {
			seq_puts(s, b1);
			if (unlikely(seq_has_overflowed(s)))
				goto s_ovfl;
		}
	}
s_ovfl:
	kfree(bp);
	return 0;
}

static int
sg_proc_seq_show_debug_full(struct seq_file *s, void *v)
{
	return sg_proc_seq_show_debug(s, v, false);
}

static int
sg_proc_seq_show_debug_summ(struct seq_file *s, void *v)
{
	return sg_proc_seq_show_debug(s, v, true);
}

#endif         /* SG_PROC_OR_DEBUG_FS */

#if IS_ENABLED(CONFIG_SCSI_PROC_FS)

static const struct proc_ops adio_proc_ops = {
	.proc_open      = sg_proc_single_open_adio,
	.proc_read      = seq_read,
	.proc_lseek     = seq_lseek,
	.proc_write     = sg_proc_write_adio,
	.proc_release   = single_release,
};

static const struct proc_ops dressz_proc_ops = {
	.proc_open      = sg_proc_single_open_dressz,
	.proc_read      = seq_read,
	.proc_lseek     = seq_lseek,
	.proc_write     = sg_proc_write_dressz,
	.proc_release   = single_release,
};

static const struct seq_operations dev_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_dev,
};

static const struct seq_operations devstrs_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_devstrs,
};

static const struct seq_operations debug_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_debug_full,
};

static const struct seq_operations debug_summ_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_debug_summ,
};

static int
sg_proc_init(void)
{
	struct proc_dir_entry *p;

	p = proc_mkdir("scsi/sg", NULL);
	if (unlikely(!p))
		return 1;

	proc_create("allow_dio", 0644, p, &adio_proc_ops);
	proc_create_seq("debug", 0444, p, &debug_seq_ops);
	proc_create_seq("debug_summary", 0444, p, &debug_summ_seq_ops);
	proc_create("def_reserved_size", 0644, p, &dressz_proc_ops);
	proc_create_single("device_hdr", 0444, p, sg_proc_seq_show_devhdr);
	proc_create_seq("devices", 0444, p, &dev_seq_ops);
	proc_create_seq("device_strs", 0444, p, &devstrs_seq_ops);
	proc_create_single("version", 0444, p, sg_proc_seq_show_version);
	return 0;
}

/* remove_proc_subtree("scsi/sg", NULL) in exit_sg() does cleanup */

#else

static int
sg_proc_init(void)
{
	return 0;
}

#endif			/* CONFIG_SCSI_PROC_FS */

#if IS_ENABLED(CONFIG_DEBUG_FS)

struct sg_dfs_attr {
	const char *name;
	umode_t mode;
	int (*show)(void *d, struct seq_file *m);
	ssize_t (*write)(void *d, const char __user *b, size_t s, loff_t *o);
	/* Set either .show or .seq_ops. */
	const struct seq_operations *seq_ops;
};

static int
sg_dfs_snapped_show(void *data, struct seq_file *m)
{
	mutex_lock(&snapped_mutex);
	if (snapped_buf && snapped_buf[0])
		seq_puts(m, snapped_buf);
	mutex_unlock(&snapped_mutex);
	return 0;
}

static ssize_t
sg_dfs_snapped_write(void *data, const char __user *buf, size_t count,
		     loff_t *ppos)
{
	/* Any write clears snapped buffer */
	mutex_lock(&snapped_mutex);
	kfree(snapped_buf);
	snapped_buf = NULL;
	mutex_unlock(&snapped_mutex);
	return count;
}

static int
sg_dfs_snapshot_devs_show(void *data, struct seq_file *m)
{
	bool last;
	int k, d;
	struct sg_dfs_context_t *ctxp = data;

	for (k = 0; k < SG_SNAPSHOT_DEV_MAX; ++k) {
		d = ctxp->snapshot_devs[k];
		last = (k + 1 == SG_SNAPSHOT_DEV_MAX);
		if (d < 0) {
			if (k == 0)
				seq_puts(m, "-1");
			break;
		}
		if (!last && d == ctxp->snapshot_devs[k + 1]) {
			if (k == 0)
				seq_puts(m, "-1");
			break;
		}
		if (k != 0)
			seq_puts(m, ",");
		seq_printf(m, "%d", d);
	}
	seq_puts(m, "\n");
	return 0;
}

static ssize_t
sg_dfs_snapshot_devs_write(void *data, const char __user *buf, size_t count,
			   loff_t *ppos)
{
	bool trailing_comma;
	int k, n;
	struct sg_dfs_context_t *cxtp = data;
	char lbuf[64] = { }, *cp, *c2p;

	if (count >= sizeof(lbuf)) {
		pr_err("%s: operation too long\n", __func__);
		return -EINVAL;
	}
	if (copy_from_user(lbuf, buf, count))
		return -EFAULT;
	for (k = 0, n = 0, cp = lbuf; k < SG_SNAPSHOT_DEV_MAX;
	     ++k, cp = c2p + 1) {
		c2p = strchr(cp, ',');
		if (c2p)
			*c2p = '\0';
		trailing_comma = !!c2p;
		/* sscanf is easier to use that this ... */
		if (kstrtoint(cp, 10, cxtp->snapshot_devs + k))
			break;
		++n;
		if (!trailing_comma)
			break;
	}
	if (n == 0) {
		return -EINVAL;
	} else if (k >= SG_SNAPSHOT_DEV_MAX && trailing_comma) {
		pr_err("%s: only %d elements in snapshot array\n", __func__,
		       SG_SNAPSHOT_DEV_MAX);
		return -EINVAL;
	}
	if (n < SG_SNAPSHOT_DEV_MAX)
		cxtp->snapshot_devs[n] = -1;
	return count;
}

static int
sg_dfs_show(struct seq_file *m, void *v)
{
	const struct sg_dfs_attr *attr = m->private;
	void *data = d_inode(m->file->f_path.dentry->d_parent)->i_private;

	return attr->show(data, m);
}

static ssize_t
sg_dfs_write(struct file *file, const char __user *buf, size_t count,
	     loff_t *ppos)
{
	struct seq_file *m = file->private_data;
	const struct sg_dfs_attr *attr = m->private;
	void *data = d_inode(file->f_path.dentry->d_parent)->i_private;

	/*
	 * Attributes that only implement .seq_ops are read-only and 'attr' is
	 * the same with 'data' in this case.
	 */
	if (unlikely(attr == data || !attr->write))
		return -EPERM;
	return attr->write(data, buf, count, ppos);
}

static int
sg_dfs_open(struct inode *inode, struct file *file)
{
	const struct sg_dfs_attr *attr = inode->i_private;
	void *data = d_inode(file->f_path.dentry->d_parent)->i_private;
	struct seq_file *m;
	int ret;

	if (attr->seq_ops) {
		ret = seq_open(file, attr->seq_ops);
		if (!ret) {
			m = file->private_data;
			m->private = data;
		}
		return ret;
	}
	if (WARN_ON_ONCE(!attr->show))
		return -EPERM;
	return single_open(file, sg_dfs_show, inode->i_private);
}

static int
sg_dfs_release(struct inode *inode, struct file *file)
{
	const struct sg_dfs_attr *attr = inode->i_private;

	if (attr->show)
		return single_release(inode, file);
	return seq_release(inode, file);
}

static const struct file_operations sg_dfs_fops = {
	.owner		= THIS_MODULE,
	.open		= sg_dfs_open,
	.read		= seq_read,
	.write		= sg_dfs_write,
	.llseek		= seq_lseek,
	.release	= sg_dfs_release,
};

static void sg_dfs_mk_files(struct dentry *parent, void *data,
			    const struct sg_dfs_attr *attr)
{
	if (IS_ERR_OR_NULL(parent))
		return;

	d_inode(parent)->i_private = data;
	for (; attr->name; ++attr)
		debugfs_create_file(attr->name, attr->mode, parent,
				    (void *)attr, &sg_dfs_fops);
}

static const struct seq_operations sg_snapshot_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_debug_full,
};

static const struct seq_operations sg_snapshot_summ_seq_ops = {
	.start = dev_seq_start,
	.next  = dev_seq_next,
	.stop  = dev_seq_stop,
	.show  = sg_proc_seq_show_debug_summ,
};

static const struct sg_dfs_attr sg_dfs_attrs[] = {
	{"snapped", 0600, sg_dfs_snapped_show, sg_dfs_snapped_write},
	{"snapshot", 0400, .seq_ops = &sg_snapshot_seq_ops},
	{"snapshot_devs", 0600, sg_dfs_snapshot_devs_show,
	 sg_dfs_snapshot_devs_write},
	{"snapshot_summary", 0400, .seq_ops = &sg_snapshot_summ_seq_ops},
	{ },
};

static void
sg_dfs_init(void)
{
	/* create and populate /sys/kernel/debug/scsi_generic directory */
	if (!sg_dfs_cxt.dfs_rootdir) {
		sg_dfs_cxt.dfs_rootdir = debugfs_create_dir("scsi_generic",
							    NULL);
		sg_dfs_mk_files(sg_dfs_cxt.dfs_rootdir, &sg_dfs_cxt,
				sg_dfs_attrs);
	}
	sg_dfs_cxt.snapshot_devs[0] = -1;	/* show all sg devices */
}

static void
sg_dfs_exit(void)
{
	debugfs_remove_recursive(sg_dfs_cxt.dfs_rootdir);
	sg_dfs_cxt.dfs_rootdir = NULL;
}

#else		/* not  defined: CONFIG_DEBUG_FS */

static void sg_dfs_init(void) {}
static void sg_dfs_exit(void) {}

#endif		/* CONFIG_DEBUG_FS */

module_param_named(scatter_elem_sz, scatter_elem_sz, int, 0644);
module_param_named(def_reserved_size, def_reserved_size, int, 0644);
module_param_named(allow_dio, sg_allow_dio, int, 0644);

MODULE_AUTHOR("Douglas Gilbert");
MODULE_DESCRIPTION("SCSI generic (sg) driver");
MODULE_LICENSE("GPL");
MODULE_VERSION(SG_VERSION_STR);
MODULE_ALIAS_CHARDEV_MAJOR(SCSI_GENERIC_MAJOR);

MODULE_PARM_DESC(scatter_elem_sz, "scatter gather element size (default: max(SG_SCATTER_SZ, PAGE_SIZE))");
MODULE_PARM_DESC(def_reserved_size, "size of buffer reserved for each fd");
MODULE_PARM_DESC(allow_dio, "allow direct I/O (default: 0 (disallow)); now ignored");
module_init(init_sg);
module_exit(exit_sg);
