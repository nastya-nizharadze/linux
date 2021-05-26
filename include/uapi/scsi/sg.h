/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
#ifndef _UAPI_SCSI_SG_H
#define _UAPI_SCSI_SG_H

/*
 * History:
 *  Started: Aug 9 by Lawrence Foard (entropy@world.std.com), to allow user
 *  process control of SCSI devices.
 *  Development Sponsored by Killy Corp. NY NY
 *
 * Original driver (sg.h):
 *   Copyright (C) 1992 Lawrence Foard
 *
 * Later extensions (versions 2, 3 and 4) to driver:
 *   Copyright (C) 1998 - 2021 Douglas Gilbert
 *
 * Version 4.0.12 (20210111)
 *  This version is for Linux 4 and 5 series kernels.
 *
 * Documentation
 * =============
 * A web site for the SG device driver can be found at:
 *   https://sg.danny.cz/sg  [alternatively check the MAINTAINERS file]
 * The documentation for the sg version 3 driver can be found at:
 *   https://sg.danny.cz/sg/p/sg_v3_ho.html
 * Also see: <kernel_source>/Documentation/scsi/scsi-generic.txt
 *
 * For utility and test programs see: https://sg.danny.cz/sg/sg3_utils.html
 */

#include <stddef.h>
#include <linux/types.h>
#include <linux/major.h>

/* bsg.h contains the sg v4 user space interface structure (sg_io_v4). */
#include <linux/bsg.h>

/*
 * Same structure as used by readv() call. It defines one scatter-gather
 * element. "Scatter-gather" is abbreviated to "sgat" in this driver to
 * avoid confusion with this driver's name.
 */
typedef struct sg_iovec	{
	void __user *iov_base;	/* Starting address (of a byte) */
	size_t iov_len;		/* Length in bytes */
} sg_iovec_t;


typedef struct sg_io_hdr {
	int interface_id;	/* [i] 'S' for SCSI generic (required) */
	int dxfer_direction;	/* [i] data transfer direction  */
	unsigned char cmd_len;	/* [i] SCSI command length */
	unsigned char mx_sb_len;/* [i] max length to write to sbp */
	unsigned short iovec_count;	/* [i] 0 implies no sgat list */
	unsigned int dxfer_len;	/* [i] byte count of data transfer */
	/* dxferp points to data transfer memory or scatter gather list */
	void __user *dxferp;	/* [i], [*io] */
	unsigned char __user *cmdp;/* [i], [*i] points to command to perform */
	void __user *sbp;	/* [i], [*o] points to sense_buffer memory */
	unsigned int timeout;	/* [i] MAX_UINT->no timeout (unit: millisec) */
	unsigned int flags;	/* [i] 0 -> default, see SG_FLAG... */
	int pack_id;		/* [i->o] unused internally (normally) */
	void __user *usr_ptr;	/* [i->o] unused internally */
	unsigned char status;	/* [o] scsi status */
	unsigned char masked_status;/* [o] shifted, masked scsi status */
	unsigned char msg_status;/* [o] messaging level data (optional) */
	unsigned char sb_len_wr; /* [o] byte count actually written to sbp */
	unsigned short host_status; /* [o] errors from host adapter */
	unsigned short driver_status;/* [o] errors from software driver */
	int resid;		/* [o] dxfer_len - actual_transferred */
	/* unit may be nanoseconds after SG_SET_GET_EXTENDED ioctl use */
	unsigned int duration;	/* [o] time taken by cmd (unit: millisec) */
	unsigned int info;	/* [o] auxiliary information */
} sg_io_hdr_t;

#define SG_INTERFACE_ID_ORIG 'S'

/* Use negative values to flag difference from original sg_header structure */
#define SG_DXFER_NONE (-1)	/* e.g. a SCSI Test Unit Ready command */
#define SG_DXFER_TO_DEV (-2)	/* data-out buffer e.g. SCSI WRITE command */
#define SG_DXFER_FROM_DEV (-3)	/* data-in buffer e.g. SCSI READ command */
/*
 * SG_DXFER_TO_FROM_DEV is treated like SG_DXFER_FROM_DEV with the additional
 * property than during indirect IO the user buffer is copied into the kernel
 * buffers _before_ the transfer from the device takes place. Useful if short
 * DMA transfers (less than requested) are not reported (e.g. resid always 0).
 */
#define SG_DXFER_TO_FROM_DEV (-4)
#define SG_DXFER_UNKNOWN (-5)	/* Unknown data direction, do not use */

/* following flag values can be OR-ed together in v3::flags or v4::flags */
#define SG_FLAG_DIRECT_IO 1	/* default is indirect IO */
/* SG_FLAG_UNUSED_LUN_INHIBIT is ignored in sg v4 driver */
#define SG_FLAG_UNUSED_LUN_INHIBIT 2  /* ignored, was LUN overwrite in cdb */
#define SG_FLAG_MMAP_IO 4	/* request memory mapped IO */
/* no transfers between kernel<-->user space; keep device<-->kernel xfers */
#define SG_FLAG_NO_DXFER 0x10000 /* See comment on previous line! */
/* defaults: for sg driver (v3_v4): Q_AT_HEAD; for block layer: Q_AT_TAIL */
#define SG_FLAG_Q_AT_TAIL 0x10
#define SG_FLAG_Q_AT_HEAD 0x20

/*
 * Flags used by ioctl(SG_IOSUBMIT) [abbrev: SG_IOS] and ioctl(SG_IORECEIVE)
 * [abbrev: SG_IOR] OR-ed into sg_io_v4::flags. The sync v4 interface uses
 * ioctl(SG_IO) and can take these new flags, as can the v3 interface.
 * These flags apply for SG_IOS unless otherwise noted. May be OR-ed together.
 */
#define SGV4_FLAG_DIRECT_IO SG_FLAG_DIRECT_IO
#define SGV4_FLAG_MMAP_IO SG_FLAG_MMAP_IO
#define SGV4_FLAG_Q_AT_TAIL SG_FLAG_Q_AT_TAIL
#define SGV4_FLAG_Q_AT_HEAD SG_FLAG_Q_AT_HEAD
#define SGV4_FLAG_IMMED 0x400 /* for polling with SG_IOR, ignored in SG_IOS */
#define SGV4_FLAG_HIPRI 0x800 /* request will use blk_poll to complete */

/* Output (potentially OR-ed together) in v3::info or v4::info field */
#define SG_INFO_OK_MASK 0x1
#define SG_INFO_OK 0x0		/* no sense, host nor driver "noise" */
#define SG_INFO_CHECK 0x1	/* something abnormal happened */

#define SG_INFO_DIRECT_IO_MASK 0x6
#define SG_INFO_INDIRECT_IO 0x0	/* data xfer via kernel buffers (or no xfer) */
#define SG_INFO_DIRECT_IO 0x2	/* direct IO requested and performed */
#define SG_INFO_MIXED_IO 0x4	/* not used, always 0 */
#define SG_INFO_DEVICE_DETACHING 0x8	/* completed successfully but ... */
#define SG_INFO_ABORTED 0x10	/* this command has been aborted */
#define SG_INFO_MRQ_FINI 0x20	/* marks multi-reqs that have finished */

/*
 * Pointer to object of this structure filled by ioctl(SG_GET_SCSI_ID). Last
 * field changed in v4 driver, was 'int unused[2]' so remains the same size.
 */
typedef struct sg_scsi_id {
	int host_no;	/* as in "scsi<n>" where 'n' is one of 0, 1, 2 etc */
	int channel;
	int scsi_id;	/* scsi id of target device */
	int lun;	/* lower 32 bits of internal 64 bit integer */
	int scsi_type;	/* TYPE_... defined in scsi/scsi.h */
	short h_cmd_per_lun;/* host (adapter) maximum commands per lun */
	short d_queue_depth;/* device (or adapter) maximum queue length */
	union {
		int unused[2];  /* as per version 3 driver */
		__u8 scsi_lun[8];  /* full 8 byte SCSI LUN [in v4 driver] */
	};
} sg_scsi_id_t;

/* For backward compatibility v4 driver yields at most SG_MAX_QUEUE of these */
typedef struct sg_req_info {	/* used by SG_GET_REQUEST_TABLE ioctl() */
	char req_state;	/* See 'enum sg_rq_state' definition in v4 driver */
	char orphan;	/* 0 -> normal request, 1 -> from interrupted SG_IO */
	/* sg_io_owned set imples synchronous, clear implies asynchronous */
	char sg_io_owned;/* 0 -> complete with read(), 1 -> owned by SG_IO */
	char problem;	/* 0 -> no problem detected, 1 -> error to report */
	int pack_id;	/* pack_id, in v4 driver may be tag instead */
	void __user *usr_ptr;	/* user provided pointer in v3+v4 interface */
	unsigned int duration;
	int unused;
} sg_req_info_t;

/*
 * IOCTLs: Those ioctls that are relevant to the SG 3.x drivers follow.
 * [Those that only apply to the SG 2.x drivers are at the end of the file.]
 * (_GET_s yield result via 'int *' 3rd argument unless otherwise indicated)
 */

#define SG_EMULATED_HOST 0x2203	/* true for emulated host adapter (ATAPI) */

/*
 * Used to configure SCSI command transformation layer for ATAPI devices.
 * Only supported by the ide-scsi driver. 20181014 No longer supported, this
 * driver passes them to the mid-level which returns a EINVAL (22) errno.
 *
 * Original note: N.B. 3rd arg is not pointer but value: 3rd arg = 0 to
 * disable transform, 1 to enable it
 */
#define SG_SET_TRANSFORM 0x2204
#define SG_GET_TRANSFORM 0x2205

#define SG_SET_RESERVED_SIZE 0x2275  /* request new reserved buffer size */
#define SG_GET_RESERVED_SIZE 0x2272  /* actual size of reserved buffer */

/*
 * Historically the scsi/sg driver has used 0x22 as it ioctl base number.
 * Add a define for that value and use it for several new ioctls added in
 * version 4.0.01 sg driver and later.
 */
#define SG_IOCTL_MAGIC_NUM 0x22

/* The following ioctl has a 'sg_scsi_id_t *' object as its 3rd argument. */
#define SG_GET_SCSI_ID 0x2276   /* Yields fd's bus, chan, dev, lun + type */
/* SCSI id information can also be obtained from SCSI_IOCTL_GET_IDLUN */

/* Override host setting and always DMA using low memory ( <16MB on i386) */
#define SG_SET_FORCE_LOW_DMA 0x2279  /* 0-> use adapter setting, 1-> force */
#define SG_GET_LOW_DMA 0x227a	/* 0-> use all ram for dma; 1-> low dma ram */

/*
 * When SG_SET_FORCE_PACK_ID set to 1, pack_id (or tag) is input to read() or
 * ioctl(SG_IO_RECEIVE). These functions wait until matching packet (request/
 * command) is finished but they will return with EAGAIN quickly if the file
 * descriptor was opened O_NONBLOCK or (in v4) if SGV4_FLAG_IMMED is given.
 * The tag is used when SG_CTL_FLAGM_TAG_FOR_PACK_ID is set on the parent
 * file descriptor (default: use pack_id). If pack_id or tag is -1 then read
 * oldest waiting and this is the same action as when FORCE_PACK_ID is
 * clear on the parent file descriptor. In the v4 interface the pack_id is
 * placed the in sg_io_v4::request_extra field .
 */
#define SG_SET_FORCE_PACK_ID 0x227b	/* pack_id or in v4 can be tag */
#define SG_GET_PACK_ID 0x227c  /* Yields oldest readable pack_id/tag, or -1 */

#define SG_GET_NUM_WAITING 0x227d /* Number of commands awaiting read() */

/* Yields max scatter gather tablesize allowed by current host adapter */
#define SG_GET_SG_TABLESIZE 0x227F  /* 0 implies can't do scatter gather */

/*
 * Integer form of version number: [x]xyyzz where [x] empty when x=0 .
 * String form of version number: "[x]x.[y]y.zz"
 */
#define SG_GET_VERSION_NUM 0x2282 /* Example: version "2.1.34" yields 20134 */

/* Returns -EBUSY if occupied. 3rd argument pointer to int (see next) */
#define SG_SCSI_RESET 0x2284
/*
 * Associated values that can be given to SG_SCSI_RESET follow.
 * SG_SCSI_RESET_NO_ESCALATE may be OR-ed to the _DEVICE, _TARGET, _BUS
 * or _HOST reset value so only that action is attempted.
 */
#define		SG_SCSI_RESET_NOTHING	0
#define		SG_SCSI_RESET_DEVICE	1
#define		SG_SCSI_RESET_BUS	2
#define		SG_SCSI_RESET_HOST	3
#define		SG_SCSI_RESET_TARGET	4
#define		SG_SCSI_RESET_NO_ESCALATE	0x100

/* synchronous SCSI command ioctl, (for version 3 and 4 interface) */
#define SG_IO 0x2285	/* similar effect as write() followed by read() */

#define SG_GET_REQUEST_TABLE 0x2286	/* yields table of active requests */

/* How to treat EINTR during SG_IO ioctl(), only in sg v3 and v4 driver */
#define SG_SET_KEEP_ORPHAN 0x2287 /* 1 -> hold for read(), 0 -> drop (def) */
#define SG_GET_KEEP_ORPHAN 0x2288

/*
 * Yields scsi midlevel's access_count for this SCSI device. 20181014 No
 * longer available, always yields 1.
 */
#define SG_GET_ACCESS_COUNT 0x2289


/*
 * Default size (in bytes) a single scatter-gather list element can have.
 * The value used by the driver is 'max(SG_SCATTER_SZ, PAGE_SIZE)'. This
 * value should be a power of 2 (and may be rounded up internally). In the
 * v4 driver this can be changed by ioctl(SG_SET_GET_EXTENDED{SGAT_ELEM_SZ}).
 */
#define SG_SCATTER_SZ (8 * 4096)

/* sg driver users' code should handle retries (e.g. from Unit Attentions) */
#define SG_DEFAULT_RETRIES 0

/* Defaults, commented if they differ from original sg driver */
#define SG_DEF_FORCE_PACK_ID 0
#define SG_DEF_KEEP_ORPHAN 0
#define SG_DEF_RESERVED_SIZE SG_SCATTER_SZ /* load time option */

/*
 * Maximum outstanding requests (i.e write()s without corresponding read()s)
 * yields EDOM from write() if exceeded. This limit only applies prior to
 * version 3.9 . It is still used as a maximum number of sg_req_info objects
 * that are returned from the SG_GET_REQUEST_TABLE ioctl.
 */
#define SG_MAX_QUEUE 16

#define SG_BIG_BUFF SG_DEF_RESERVED_SIZE    /* for backward compatibility */

/*
 * Alternate style type names, "..._t" variants (as found in the
 * 'typedef struct * {};' definitions above) are preferred to these:
 */
typedef struct sg_io_hdr Sg_io_hdr;
typedef struct sg_io_vec Sg_io_vec;
typedef struct sg_scsi_id Sg_scsi_id;
typedef struct sg_req_info Sg_req_info;


/* vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv */
/*   The v1+v2 SG interface based on the 'sg_header' structure follows.   */
/* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ */

#define SG_MAX_SENSE 16	/* this only applies to the sg_header interface */

struct sg_header {
	int pack_len;	/* [o] reply_len (ie useless), ignored as input */
	int reply_len;	/* [i] max length of expected reply (inc. sg_header) */
	int pack_id;	/* [io] id number of packet (use ints >= 0) */
	int result;	/* [o] 0==ok, else (+ve) Unix errno (best ignored) */
	unsigned int twelve_byte:1;
	    /* [i] Force 12 byte command length for group 6 & 7 commands  */
	unsigned int target_status:5;	/* [o] scsi status from target */
	unsigned int host_status:8;	/* [o] host status (see "DID" codes) */
	unsigned int driver_status:8;	/* [o] driver status+suggestion */
	unsigned int other_flags:10;	/* unused */
	unsigned char sense_buffer[SG_MAX_SENSE];
	/*
	 * [o] Output in 3 cases:
	 *	when target_status is CHECK_CONDITION or
	 *	when target_status is COMMAND_TERMINATED or
	 *	when (driver_status & DRIVER_SENSE) is true.
	 */
};

/*
 * IOCTLs: The following are not required (or ignored) when the v3 or v4
 * interface is used as those structures contain a timeout field. These
 * ioctls are kept for backward compatibility with v1+v2 interfaces.
 */

#define SG_SET_TIMEOUT 0x2201  /* unit: (user space) jiffies */
#define SG_GET_TIMEOUT 0x2202  /* yield timeout as _return_ value */

/*
 * Get/set command queuing state per fd (default is SG_DEF_COMMAND_Q.
 * Each time a sg_io_hdr_t object is seen on this file descriptor, this
 * command queuing flag is set on (overriding the previous setting).
 * This setting defaults to 0 (i.e. no queuing) but gets set the first
 * time that fd sees a v3 or v4 interface request.
 */
#define SG_GET_COMMAND_Q 0x2270   /* Yields 0 (queuing off) or 1 (on) */
#define SG_SET_COMMAND_Q 0x2271   /* Change queuing state with 0 or 1 */

/*
 * Turn on/off error sense trace (1 and 0 respectively, default is off).
 * Try using: "# cat /proc/scsi/sg/debug" instead in the v3 driver
 */
#define SG_SET_DEBUG 0x227e    /* 0 -> turn off debug */

/*
 * override SCSI command length with given number on the next write() on
 * this file descriptor (v1 and v2 interface only)
 */
#define SG_NEXT_CMD_LEN 0x2283

/*
 * New ioctls to replace async (non-blocking) write()/read() interface.
 * Present in version 4 and later of the sg driver [>20190427]. The
 * SG_IOSUBMIT and SG_IORECEIVE ioctls accept the sg_v4 interface based on
 * struct sg_io_v4 found in <include/uapi/linux/bsg.h>. These objects are
 * passed by a pointer in the third argument of the ioctl.
 *
 * Data may be transferred both from the user space to the driver by these
 * ioctls. Hence the _IOWR macro is used here to generate the ioctl number
 * rather than _IOW or _IOR.
 */
/* Submits a v4 interface object to driver, optionally receive tag back */
#define SG_IOSUBMIT _IOWR(SG_IOCTL_MAGIC_NUM, 0x41, struct sg_io_v4)

/* Gives some v4 identifying info to driver, receives associated response */
#define SG_IORECEIVE _IOWR(SG_IOCTL_MAGIC_NUM, 0x42, struct sg_io_v4)

/* Submits a v3 interface object to driver */
#define SG_IOSUBMIT_V3 _IOWR(SG_IOCTL_MAGIC_NUM, 0x45, struct sg_io_hdr)

/* Gives some v3 identifying info to driver, receives associated response */
#define SG_IORECEIVE_V3 _IOWR(SG_IOCTL_MAGIC_NUM, 0x46, struct sg_io_hdr)

/* Provides identifying info about a prior submission (e.g. a tag) */
#define SG_IOABORT _IOW(SG_IOCTL_MAGIC_NUM, 0x43, struct sg_io_v4)

/* command queuing is always on when the v3 or v4 interface is used */
#define SG_DEF_COMMAND_Q 0

#define SG_DEF_UNDERRUN_FLAG 0

/* If the timeout value in the v3_v4 interfaces is 0, this value is used */
#define SG_DEFAULT_TIMEOUT	(60*HZ)	/* HZ == 'jiffies in 1 second' */

#endif		/* end of _UAPI_SCSI_SG_H guard */
