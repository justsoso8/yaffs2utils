/*
 * yaffs2utils: Utilities to make/extract a YAFFS2/YAFFS1 image.
 * Copyright (C) 2010-2011 Luen-Yung Lin <penguin.lin@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as 
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include "configs.h"

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <getopt.h>
#include <limits.h>
#include <libgen.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/mman.h>
#ifdef _HAVE_LUTIMES
#include <sys/time.h>
#else
#include <utime.h>
#endif
#ifdef _HAVE_OSX_SYSLIMITS
#include <sys/syslimits.h>
#endif

#include "yaffs_packedtags1.h"
#include "yaffs_packedtags2.h"
#include "yaffs_trace.h"

#include "yaffs2utils_io.h"
#include "yaffs2utils_ecc.h"
#include "yaffs2utils_list.h"
#include "yaffs2utils_endian.h"
#include "yaffs2utils_progress.h"

#include "yaffs2utils_version.h"

/*-------------------------------------------------------------------------*/

typedef struct unyaffs2_file_var {
	loff_t file_size;
} unyaffs2_file_var_t;

typedef struct unyaffs2_symlink_var {
	char *alias;
} unyaffs2_symlink_var_t;

typedef struct unyaffs2_hardlink_var {
	struct unyaffs2_obj *equiv_obj;
} unyaffs2_hardlink_var_t;

typedef struct unyaffs2_dev_var {
	unsigned rdev;
} unyaffs2_dev_var_t;

typedef union unyaffs2_file_variant {
	struct unyaffs2_file_var file;
	struct unyaffs2_symlink_var symlink;
	struct unyaffs2_hardlink_var hardlink;
	struct unyaffs2_dev_var dev;
} unyaffs2_file_variant;

typedef struct unyaffs2_obj {
	unsigned char valid:1;
	unsigned char extracted:1;	/* 1 when extracted. */

	unsigned obj_id;
	unsigned parent_id;
	struct unyaffs2_obj *parent_obj;

	off_t hdr_off;			/* header offset in the image */

	char name[NAME_MAX + 1];

	enum yaffs_obj_type type;	/* file type */
	union unyaffs2_file_variant variant;

	unsigned mode;			/* file mode */

	unsigned uid;			/* owner uid */
	unsigned gid;			/* owner gid */

	unsigned atime;
	unsigned mtime;
	unsigned ctime;

	struct list_head hashlist;      /* hash table */
	struct list_head hardlink;	/* hardlink list */

	struct list_head children;	/* if it is the directory */
	struct list_head siblings;	/* neighbors of fs tree */
} unyaffs2_obj_t;

typedef struct unyaffs2_fstree {
	unsigned objs;
	struct unyaffs2_obj *root;
} unyaffs2_fstree_t;

typedef struct unyaffs2_specfile {
	char *path;			/* file path */
	struct list_head list;		/* specified files list */
	struct unyaffs2_obj *obj;	/* object */
} unyaffs2_specfile_t;

#ifdef _HAVE_MMAP
typedef struct unyaffs2_mmap {
	unsigned char *addr;
	size_t size;
} unyaffs2_mmap_t;
#endif

/*-------------------------------------------------------------------------*/

#define UNYAFFS2_OBJTABLE_SIZE	YAFFS_NOBJECT_BUCKETS

#define UNYAFFS2_FLAGS_NONROOT	0x01
#define UNYAFFS2_FLAGS_YAFFS1	0x02
#define UNYAFFS2_FLAGS_ENDIAN	0x04
#define UNYAFFS2_FLAGS_VERBOSE	0x08

#define UNYAFFS2_ISYAFFS1	(unyaffs2_flags & UNYAFFS2_FLAGS_YAFFS1)
#define UNYAFFS2_ISENDIAN	(unyaffs2_flags & UNYAFFS2_FLAGS_ENDIAN)
#define UNYAFFS2_ISVERBOSE	(unyaffs2_flags & UNYAFFS2_FLAGS_VERBOSE)

#define UNYAFFS2_PRINT(s, args...)	fprintf(stdout, s, ##args)

#define UNYAFFS2_ERROR(s, args...)	fprintf(stderr, s, ##args)

#define UNYAFFS2_WARN(s, args...)	UNYAFFS2_ERROR(s, ##args)

#define UNYAFFS2_HELP(s, args...) 	UNYAFFS2_ERROR(s, ##args)

#ifdef _UNYAFFS2_DEBUG
#define UNYAFFS2_DEBUG(s, args...)	UNYAFFS2_ERROR(s, ##args)
#else
#define UNYAFFS2_DEBUG(s, args...)
#endif

#define UNYAFFS2_VERBOSE(s, args...) \
		({if (UNYAFFS2_ISVERBOSE) \
			UNYAFFS2_PRINT(s, ##args);})

#define UNYAFFS2_PROGRESS_INIT() \
		({ if (!UNYAFFS2_ISVERBOSE) \
			progress_init();})

#define UNYAFFS2_PROGRESS_BAR(objs, all) \
		({ if (!UNYAFFS2_ISVERBOSE) \
			progress_bar(objs, all);})

/*-------------------------------------------------------------------------*/

static unsigned unyaffs2_chunksize = 0;
static unsigned unyaffs2_sparesize = 0;

static unsigned unyaffs2_flags = 0;

static unsigned unyaffs2_image_objs = 0;

static unsigned unyaffs2_bufsize = 0;
static unsigned char *unyaffs2_databuf = NULL;

static int unyaffs2_image_fd = -1;

static char unyaffs2_curfile[PATH_MAX + PATH_MAX] = {0};
static char unyaffs2_linkfile[PATH_MAX + PATH_MAX] = {0};

static LIST_HEAD(unyaffs2_hardlink_list);	/* hardlink */
static LIST_HEAD(unyaffs2_specfile_list);	/* specfied files */

static nand_ecclayout_t *unyaffs2_oobinfo = NULL;

static struct unyaffs2_fstree unyaffs2_objtree = {0};
static struct list_head unyaffs2_objtable[UNYAFFS2_OBJTABLE_SIZE];

#ifdef _HAVE_MMAP
static struct unyaffs2_mmap unyaffs2_mmapinfo = {0};
#endif

/*-------------------------------------------------------------------------*/

static struct unyaffs2_obj *
unyaffs2_obj_alloc (void)
{
	struct unyaffs2_obj *obj;

	obj = calloc(sizeof(struct unyaffs2_obj), sizeof(unsigned char));
	if (obj == NULL)
		return NULL;

	obj->parent_obj = obj;

	INIT_LIST_HEAD(&obj->hardlink);
	INIT_LIST_HEAD(&obj->children);
	INIT_LIST_HEAD(&obj->siblings);
	INIT_LIST_HEAD(&obj->hashlist);

	return obj;
}

static void
unyaffs2_obj_free (struct unyaffs2_obj *obj)
{
	if (obj->type == YAFFS_OBJECT_TYPE_SYMLINK &&
	    obj->variant.symlink.alias != NULL)
		free(obj->variant.symlink.alias);

	list_del(&obj->hardlink);
	list_del(&obj->children);
	list_del(&obj->siblings);
	list_del(&obj->hashlist);

	free(obj);
}

/*-------------------------------------------------------------------------*/

/*
 * hash table to look up objects
 */

static inline unsigned
unyaffs2_objtable_hash (unsigned hash)
{
	return hash % UNYAFFS2_OBJTABLE_SIZE;
}

static inline void
unyaffs2_objtable_insert (struct unyaffs2_obj *obj)
{
	unsigned n = unyaffs2_objtable_hash(obj->obj_id);
	list_add_tail(&obj->hashlist, &unyaffs2_objtable[n]);
}

static inline struct unyaffs2_obj *
unyaffs2_objtable_lookup (unsigned obj_id)
{
	unsigned n = unyaffs2_objtable_hash(obj_id);
	struct list_head *p;
	struct unyaffs2_obj *obj;

	list_for_each(p, &unyaffs2_objtable[n]) {
		obj = list_entry(p, unyaffs2_obj_t, hashlist);
		if (obj->obj_id == obj_id)
			return obj;
	}

	return NULL;
}

static inline void
unyaffs2_objtable_init (void)
{
	unsigned n;

	for (n = 0; n < UNYAFFS2_OBJTABLE_SIZE; n++)
		INIT_LIST_HEAD(&unyaffs2_objtable[n]);
}

static inline void
unyaffs2_objtable_exit (void)
{
	unsigned i;
	struct list_head *p, *n;
	struct unyaffs2_obj *obj;

	for (i = 0; i < UNYAFFS2_OBJTABLE_SIZE; i++) {
		list_for_each_safe(p, n, &unyaffs2_objtable[i]) {
			obj = list_entry(p, unyaffs2_obj_t, hashlist);
			unyaffs2_obj_free(obj);
		}
	}
}

/*-------------------------------------------------------------------------*/

/*
 * fs tree for objects extraction.
 */

static void
unyaffs2_objtree_cleanup (struct unyaffs2_obj *obj)
{
	struct list_head *p, *n;
	struct unyaffs2_obj *child;

	if (obj == NULL)
		return;

	list_for_each_safe(p, n, &obj->children) {
		child = list_entry(p, unyaffs2_obj_t, siblings);
		unyaffs2_objtree_cleanup(child);
	}

	unyaffs2_obj_free(obj);
}

static struct unyaffs2_fstree *
unyaffs2_objtree_init (struct unyaffs2_fstree *fst)
{
	struct unyaffs2_fstree *f = fst;

	if (f == NULL) {
		f = malloc(sizeof(struct unyaffs2_fstree));
		if (f == NULL)
			return NULL;
	}

	/* initialize */
	memset(f, 0, sizeof(struct unyaffs2_fstree));

	return f;
}

static void
unyaffs2_objtree_exit (struct unyaffs2_fstree *fst)
{
	return unyaffs2_objtree_cleanup(fst->root);
}

/*-------------------------------------------------------------------------*/

/*
 * specfied files
 */

static struct unyaffs2_specfile *
unyaffs2_specfile_lookup (const char *path) 
{
	struct unyaffs2_specfile *spec;
	struct list_head *p;
	size_t len;

	list_for_each(p, &unyaffs2_specfile_list) {
		spec = list_entry(p, unyaffs2_specfile_t, list);
		if (!strncmp(path, spec->path, strlen(spec->path))) {
			len = strlen(spec->path);
			if (path[len] == '\0' || path[len] == '/')
				return spec;
		}
	}

	return NULL;
}

static int
unyaffs2_specfile_insert (const char *path)
{
	char *s, *e;
	size_t len;
	struct unyaffs2_specfile *spec;

	/* skipping leading '/' */
	s = (char *)path;
	while (s[0] != '\0' && s[0] == '/')
		s++;

	/* skipping following '/' */
	e = (char *)path + strlen(path) - 1;
	while (e > s && e[0] == '/')
		e--;

	if (e <= s)
		return -1;

	spec = calloc(sizeof(struct unyaffs2_specfile), sizeof(unsigned char));
	if (spec) {
		len = e - s + 1;
		spec->path = calloc(len + 1, sizeof(unsigned char));
		if (spec->path == NULL) {
			free(spec);
			return -1;
		}
		memcpy(spec->path, s, len);
		spec->path[len] = '\0';

		list_add_tail(&spec->list, &unyaffs2_specfile_list);
	}

	return (spec == NULL);
}

static void
unyaffs2_specfile_exit (void)
{
	struct unyaffs2_specfile *spec;
	struct list_head *p, *n;

	list_for_each_safe(p, n, &unyaffs2_specfile_list) {
		spec = list_entry(p, unyaffs2_specfile_t, list);
		if (spec->path)
			free(spec->path);
		list_del(&spec->list);
		free(spec);
	}
}

/*-------------------------------------------------------------------------*/

static int
unyaffs2_mkdir (const char *name, const mode_t mode)
{
	char *p = NULL;
	const char *dname;

	struct stat statbuf;

	dname = strlen(name) ? name : ".";

	p = (char *)dname;
	while ((p = strchr(p, '/')) != NULL) {
		*p = '\0';
		mkdir(dname, 0755);
		*p++ = '/';
	}

	if (mkdir(dname, mode) < 0 && 
	    (stat(dname, &statbuf) < 0 || !S_ISDIR(statbuf.st_mode)))
		return -1;

	return 0;
}

static char *
unyaffs2_prefix_basestr(const char *path, const char *prefix)
{
	char *p = NULL;
	size_t len = 0;

	if ((len = strlen(prefix)) != 0 &&
	    strncasecmp(path, prefix, len) == 0 &&
	    (path[len] == '\0' || path[len] == '/')) {
		p = strrchr(prefix, '/');
		p = p ? (char *)path + (p - prefix) + 1: (char *)path;
	}

	return p;
}

/*-------------------------------------------------------------------------*/

static size_t
unyaffs2_spare2tag (unsigned char *tag, unsigned char *spare, size_t bytes)
{
	unsigned i;
	size_t copied = 0;
	struct nand_oobfree *oobfree = unyaffs2_oobinfo->oobfree;

	for (i = 0; i < 8 && copied < bytes; i++) {
		size_t size = bytes - copied;
		unsigned char *s = spare + oobfree[i].offset;

		if (size > oobfree[i].length)
			size = oobfree[i].length;

		memcpy(tag, s, size);
		if (memcmp(tag, s, size))
			return -1;

		copied += size;
		tag += size;
	}

	return copied;
}

static void
unyaffs2_extract_packedtags (struct yaffs_ext_tags *tag, unsigned char *buf)
{
	if (UNYAFFS2_ISYAFFS1) {
		struct yaffs_packed_tags1 pt1;

		memset(&pt1, 0xff, sizeof(struct yaffs_packed_tags1));
		unyaffs2_spare2tag((unsigned char *)&pt1, buf,
				   sizeof(struct yaffs_packed_tags1));

		if (UNYAFFS2_ISENDIAN)
			packedtags1_endian_transform(&pt1, 1);

		yaffs_unpack_tags1(tag, &pt1);
	}
	else {
		struct yaffs_packed_tags2 pt2;

		memset(&pt2, 0xff, sizeof(struct yaffs_packed_tags2));
		unyaffs2_spare2tag((unsigned char *)&pt2, buf,
				   sizeof(struct yaffs_packed_tags2));

		if (UNYAFFS2_ISENDIAN)
			packedtags2_tagspart_endian_transform(&pt2);

		yaffs_unpack_tags2_tags_only(tag, &pt2.t);
	}
}

static inline int
unyaffs2_isempty (unsigned char *buf, unsigned size)
{
	while (size--) {
		if (*buf != 0xff)
			return 0;
		buf++;
	}
	return 1;
}

static inline loff_t
unyaffs2_extract_oh_size (struct yaffs_obj_hdr *oh)
{
	loff_t retval;

	if(~(oh->file_size_high))
		retval = (((loff_t) oh->file_size_high) << 32) |
			  (((loff_t) oh->file_size_low) & 0xFFFFFFFF);
	else
		retval = (loff_t) oh->file_size_low;

	return retval;
}

/*-------------------------------------------------------------------------*/

static void
unyaffs2_format_filepath (char *path, size_t size, struct unyaffs2_obj *obj)
{
	size_t pathlen = 0;

	if (obj->obj_id == YAFFS_OBJECTID_ROOT)
		return;

	pathlen = strlen(path);
	unyaffs2_format_filepath(path, size, obj->parent_obj);

	if (pathlen < strlen(path))
		strncat(path, "/", size - strlen(path) - 1);

	strncat(path, obj->name, size - strlen(path) - 1);
}


static struct unyaffs2_obj *
unyaffs2_follow_hardlink (struct unyaffs2_obj *obj)
{
	unsigned link_count = 0;
	struct unyaffs2_obj *equiv = obj;

	while (equiv && equiv->valid &&
	       equiv->type == YAFFS_OBJECT_TYPE_HARDLINK) {
		equiv = equiv->variant.hardlink.equiv_obj;
		if (++link_count > YAFFS_MAX_OBJECT_ID) {
			/* make sure everything is right */
			UNYAFFS2_DEBUG("too many links for object %d\n",
					obj->obj_id);
			break;
		}
	}

	return (equiv && equiv->valid &&
		equiv->type != YAFFS_OBJECT_TYPE_HARDLINK) ? equiv : NULL;
}

static void
unyaffs2_obj_chattr (const char *fpath, struct unyaffs2_obj *obj)
{
	/* access time */
#ifdef _HAVE_LUTIMES
	struct timeval ftime[2];

	ftime[0].tv_sec = obj->atime;
	ftime[0].tv_usec = 0;
	ftime[1].tv_sec = obj->mtime;
	ftime[1].tv_usec = 0;

	lutimes(fpath, ftime);
#else
	struct utimbuf ftime;

	ftime.actime = obj->atime;
	ftime.modtime = obj->mtime;

	utime(fpath, &ftime);
#endif

	/* owner */
	lchown(fpath, obj->uid, obj->gid);

	/* mode - no effect on symbolic link */
	if (obj->type != YAFFS_OBJECT_TYPE_SYMLINK)
		chmod(fpath, obj->mode);
}

static int
unyaffs2_objtree_chattr (struct unyaffs2_obj *obj)
{
	struct list_head *p;
	struct unyaffs2_obj *child;

	if (obj == NULL) {
		if (unyaffs2_objtree.root == NULL)
			return 0;

		return unyaffs2_objtree_chattr(unyaffs2_objtree.root);
	}

	/* format the file path */
	if (unyaffs2_curfile[0] != '\0' &&
	    unyaffs2_curfile[strlen(unyaffs2_curfile) - 1] != '/')
		strncat(unyaffs2_curfile, "/",
			sizeof(unyaffs2_curfile) -
			strlen(unyaffs2_curfile) - 1);

		 strncat(unyaffs2_curfile, obj->name,
			 sizeof(unyaffs2_curfile) -
				strlen(unyaffs2_curfile) - 1);

	/* travel */
	if (obj->type == YAFFS_OBJECT_TYPE_DIRECTORY) {
		list_for_each(p, &obj->children) {
			child = list_entry(p, unyaffs2_obj_t, siblings);
			unyaffs2_objtree_chattr(child);
		}
	}

	if (obj->type != YAFFS_OBJECT_TYPE_HARDLINK)
		unyaffs2_obj_chattr(unyaffs2_curfile, obj);

	/* restore current file path */
	if (!strcmp(dirname(unyaffs2_curfile), "."))
		unyaffs2_curfile[0] = '\0';

	return 0;
}

/*-------------------------------------------------------------------------*/

static inline void
unyaffs2_scan_img_status (unsigned status)
{
	char st = '-';

	switch (status % 4) {
	case 1:
		st = '\\';
		break;
	case 2:
		st = '|';
		break;
	case 3:
		st = '/';
		break;
	default:
		st = '-';
		break;
	}

	UNYAFFS2_PRINT("\b\b\b[%c]", st);
	fflush(stdout);
}

static int
unyaffs2_scan_img (void)
{
	off_t offset = 0;
#ifdef _HAVE_MMAP
	size_t remains;
#else
	ssize_t reads;
#endif

	if (unyaffs2_image_fd < 0) {
		UNYAFFS2_DEBUG("bad file descriptor\n");
		return 0;
	}

#ifdef _HAVE_MMAP
	if (unyaffs2_mmapinfo.addr == NULL) {
		UNYAFFS2_DEBUG("NULL address while mmap\n");
		return 0;
	}
#endif

#ifdef _HAVE_MMAP
	remains = unyaffs2_mmapinfo.size;
	while (offset < unyaffs2_mmapinfo.size && remains >= unyaffs2_bufsize &&
	       memcpy(unyaffs2_databuf,
		      unyaffs2_mmapinfo.addr + offset, unyaffs2_bufsize)) {
#else
	offset = lseek(unyaffs2_image_fd, 0, SEEK_SET);
	while ((reads = safe_read(unyaffs2_image_fd,
				  unyaffs2_databuf, unyaffs2_bufsize)) != 0) {
#endif
		struct yaffs_ext_tags tag;
		struct unyaffs2_obj *obj;
		struct yaffs_obj_hdr *oh;

#ifdef _HAVE_MMAP
		if (memcmp(unyaffs2_databuf, 
		    unyaffs2_mmapinfo.addr + offset, unyaffs2_bufsize)) {
#else
		if (reads != unyaffs2_bufsize) {
#endif
			/* parse image failed */
			UNYAFFS2_ERROR("error while parsing the image ");
			UNYAFFS2_ERROR("@ offset %lu\n", offset);
			return -1;
		}

		unyaffs2_extract_packedtags(&tag,
					    unyaffs2_databuf +
					    unyaffs2_chunksize);

		if (unyaffs2_isempty(unyaffs2_databuf, unyaffs2_bufsize) ||
		    !tag.obj_id || !tag.chunk_used) {
			UNYAFFS2_DEBUG("empty page skipped\n");
			goto next;
		}

		/* a new object */
		if (tag.chunk_id == 0 &&
		    tag.obj_id > YAFFS_OBJECTID_DELETED) {
			obj = unyaffs2_obj_alloc();
			if (obj == NULL) {
				UNYAFFS2_ERROR("cannot allocate memory ");
				UNYAFFS2_ERROR("for object %u\n", tag.obj_id);
				return -1;
			}

			oh = (struct yaffs_obj_hdr *)unyaffs2_databuf;
			if (UNYAFFS2_ISENDIAN)
				oh_endian_transform(oh);

			obj->obj_id = tag.obj_id;
			obj->parent_id = oh->parent_obj_id;
			obj->hdr_off = offset;

			unyaffs2_objtable_insert(obj);
			unyaffs2_scan_img_status(++unyaffs2_image_objs);
		}
next:
#if _HAVE_MMAP
		offset += unyaffs2_bufsize;
		remains -= unyaffs2_bufsize;
#else
		offset = lseek(unyaffs2_image_fd, 0, SEEK_CUR);
#endif
	}

	return 0;
}

/*-------------------------------------------------------------------------*/

static struct unyaffs2_obj*
unyaffs2_create_fakeroot (const char *path)
{
	struct stat s;
	struct unyaffs2_obj *obj;

	if (stat(path, &s) || !S_ISDIR(s.st_mode))
		return NULL;

	obj = unyaffs2_obj_alloc();
	if (!obj)
		return NULL;

	/* update root info */
	obj->obj_id = YAFFS_OBJECTID_ROOT;
	obj->parent_id = YAFFS_OBJECTID_ROOT;
	obj->type = YAFFS_OBJECT_TYPE_DIRECTORY;

	obj->mode = s.st_mode;

	obj->uid = s.st_uid;
	obj->gid = s.st_gid;
	obj->atime = s.st_atime;
	obj->mtime = s.st_mtime;
	obj->ctime = s.st_ctime;

	unyaffs2_image_objs++;

	return obj;
}

static int
unyaffs2_create_objtree (void)
{
	unsigned n, objs = 0;
	struct list_head *p;
	struct unyaffs2_obj *obj, *parent;

	unyaffs2_objtree.root = unyaffs2_objtable_lookup(YAFFS_OBJECTID_ROOT);

	for (n = 0; n < UNYAFFS2_OBJTABLE_SIZE; n++) {
		list_for_each(p, &unyaffs2_objtable[n]) {
			obj = list_entry(p, unyaffs2_obj_t, hashlist);

			parent = unyaffs2_objtable_lookup(obj->parent_id);
			if (parent && obj != parent) {
				list_add_tail(&obj->siblings,
					      &parent->children);
				obj->parent_obj = parent;
			}
			unyaffs2_scan_img_status(++objs);
		}
	}

	return 0;
}

static int
unyaffs2_validate_objtree (struct unyaffs2_obj *obj)
{
	struct list_head *p;
	struct unyaffs2_obj *child;

	if (obj == NULL) {
		if (unyaffs2_objtree.root == NULL &&
		    (unyaffs2_objtree.root =
		     unyaffs2_objtable_lookup(YAFFS_OBJECTID_ROOT)) == NULL) {
			UNYAFFS2_ERROR("cannot find the root object ");
			UNYAFFS2_ERROR("(image broken?)\n");
			return -1;
		}

		unyaffs2_objtree.objs = 0;
		return unyaffs2_validate_objtree(unyaffs2_objtree.root);
	}

	/* FIXME: validation? */
	obj->valid = 1;
	unyaffs2_scan_img_status(++unyaffs2_objtree.objs);

	list_for_each(p, &obj->children) {
		child = list_entry(p, unyaffs2_obj_t, siblings);
		if (unyaffs2_validate_objtree(child) < 0)
			return -1;
	}

	return 0;
}

static int
unyaffs2_build_objtree (void)
{
	return unyaffs2_create_objtree() ||
	       unyaffs2_validate_objtree(unyaffs2_objtree.root);
}

/*-------------------------------------------------------------------------*/

#ifdef _HAVE_MMAP
static int
unyaffs2_extract_file_mmap (unsigned char *addr, size_t size, off_t off,
			    const char *fpath, struct unyaffs2_obj *obj)
{
	int outfd;
	unsigned char *outaddr, *curaddr, *endaddr = addr + size;
	size_t bufsize = unyaffs2_chunksize + unyaffs2_sparesize;
	size_t fsize = obj->variant.file.file_size, remains = 0, written = 0;

	struct yaffs_ext_tags tag;

	outfd = open(fpath, O_RDWR | O_CREAT | O_TRUNC, obj->mode);
	if (outfd < 0) {
		fprintf(stderr, "cannot create file '%s'\n", fpath);
		return -1;
	}

	if (fsize == 0)
		goto out;

	/* stretch the file */
	if (lseek(outfd, fsize - 1, SEEK_SET) < 0 ||
	    safe_write(outfd, "", 1) != 1) {
		UNYAFFS2_ERROR("cannot stretch the file '%s'\n", fpath);
		goto out;
	}

	/* now mmap */
	outaddr = mmap(NULL, fsize, PROT_WRITE | PROT_READ,
		       MAP_SHARED, outfd, 0);
	if (outaddr == NULL) {
		UNYAFFS2_ERROR("cannot mmap the file '%s'\n", fpath);
		goto out;
	}

	addr += off;
	curaddr = outaddr;
	remains = fsize;

	while (addr < endaddr && remains > 0) {
		unyaffs2_extract_packedtags(&tag, addr + unyaffs2_chunksize);

		written = remains < tag.n_bytes ? remains : tag.n_bytes;
		memcpy(curaddr, addr, written);
		if (memcmp(curaddr, addr, written)) {
			UNYAFFS2_ERROR("error while writing file '%s'\n", fpath);
			break;
		}

		remains -= written;
		curaddr += written;
		addr += bufsize;
	}

	munmap(outaddr, fsize);
out:
	close(outfd);

	return !(remains == 0);
}
#else
static int
unyaffs2_extract_file (const int fd, off_t off,
		       const char *fpath, struct unyaffs2_obj *obj)
{
	int outfd;
	size_t written = 0, size = obj->variant.file.file_size;
	ssize_t w, r;

	struct yaffs_ext_tags tag;

	if (obj->type != YAFFS_OBJECT_TYPE_FILE)
		return 0;

	outfd = open(fpath, O_WRONLY | O_CREAT | O_TRUNC, obj->mode);
	if (outfd < 0) {
		UNYAFFS2_ERROR("cannot create file '%s'\n", fpath);
		return -1;
	}

	lseek(fd, off, SEEK_SET);

	/* read image until the size is reached */
	while (written < size &&
	       (r = safe_read(fd, unyaffs2_databuf, unyaffs2_bufsize)) != 0)
	{
		if (r != unyaffs2_bufsize) {
			UNYAFFS2_DEBUG("error while reading image for '%s'\n",
					fpath);
			break;
		}

		unyaffs2_extract_packedtags(&tag,
					    unyaffs2_databuf +
					    unyaffs2_chunksize);

		w = safe_write(outfd, unyaffs2_databuf, tag.n_bytes);
		if (w != tag.n_bytes) {
			UNYAFFS2_DEBUG("error while writing file '%s'", fpath);
			break;
		}

		written += tag.n_bytes;
	}

	close(outfd);

	return !(written == size);
}
#endif

static int
unyaffs2_extract_hardlink (struct list_head *hardlink)
{
	char *dstfile, *lnkfile;
	struct list_head *p, *list;
	struct unyaffs2_obj *obj, *equiv;

	list = hardlink ? hardlink : &unyaffs2_hardlink_list;

	list_for_each(p, list) {
		UNYAFFS2_PROGRESS_BAR(++unyaffs2_image_objs,
				      unyaffs2_objtree.objs);

		obj = list_entry(p, unyaffs2_obj_t, hardlink);
		equiv = unyaffs2_follow_hardlink(obj);
		if (equiv == NULL)
			continue;

		memset(unyaffs2_curfile, 0, sizeof(unyaffs2_curfile));
		unyaffs2_format_filepath(unyaffs2_curfile,
					 sizeof(unyaffs2_curfile), obj);

		memset(unyaffs2_linkfile, 0, sizeof(unyaffs2_linkfile));
		unyaffs2_format_filepath(unyaffs2_linkfile,
					 sizeof(unyaffs2_linkfile), equiv);

		/* if a file(set) is specified */
		dstfile = unyaffs2_curfile;
		lnkfile = unyaffs2_linkfile;
		if (!list_empty(&unyaffs2_specfile_list)) {
			struct unyaffs2_specfile *spec;

			spec = unyaffs2_specfile_lookup(unyaffs2_curfile);
			dstfile = (spec == NULL) ? NULL : 
				  unyaffs2_prefix_basestr(unyaffs2_curfile,
							  spec->path);

			spec = unyaffs2_specfile_lookup(unyaffs2_linkfile);
			lnkfile = (spec == NULL) ? NULL : 
				  unyaffs2_prefix_basestr(unyaffs2_linkfile,
							  spec->path);
		}

		if (!dstfile)
			continue;

		/* unlink the file if it is existed */
		if (!access(dstfile, F_OK))
			unlink(dstfile);

		/* link them, silent on errors */
		if (lnkfile && equiv->extracted) {
			link(lnkfile, dstfile);
			continue;
		}

		/* 
		 * if the linked file was NOT existed (or extracted),
		 * extracting the file content based on the equiv obj.
		 */
		obj->type = equiv->type;
		obj->mode = equiv->mode;
		obj->uid = equiv->uid;
		obj->gid = equiv->gid;
		obj->atime = equiv->atime;
		obj->mtime = equiv->mtime;
		obj->ctime = equiv->ctime;

		switch (obj->type) {
		case YAFFS_OBJECT_TYPE_FILE:
			obj->variant.file.file_size =
				equiv->variant.file.file_size;
#ifdef _HAVE_MMAP
			unyaffs2_extract_file_mmap(unyaffs2_mmapinfo.addr,
						   unyaffs2_mmapinfo.size,
						   equiv->hdr_off +
						   unyaffs2_bufsize,
						   dstfile, obj);
#else
			unyaffs2_extract_file(unyaffs2_image_fd,
					      equiv->hdr_off + unyaffs2_bufsize,
					      dstfile, obj);
#endif
		break;
		case YAFFS_OBJECT_TYPE_DIRECTORY:
			unyaffs2_mkdir(dstfile, 0755);
			break;
		case YAFFS_OBJECT_TYPE_SYMLINK:
			obj->variant.symlink.alias =
				strdup(equiv->variant.symlink.alias);
			if (obj->variant.symlink.alias) { 
				unlink(dstfile);
				symlink(obj->variant.symlink.alias, dstfile);
			}
			break;
		case YAFFS_OBJECT_TYPE_SPECIAL:
			if ((obj->mode & S_IFMT) &
			    (S_IFBLK | S_IFCHR | S_IFIFO | S_IFSOCK)) {
				obj->variant.dev.rdev = obj->variant.dev.rdev;
				mknod(dstfile, obj->mode,
				      obj->variant.dev.rdev);
			}
			break;
		default:
			/* unsupported type, including HARDLINK. */
			break;
		}
	}

	return 0;
}

static int
unyaffs2_extract_objtree (struct unyaffs2_obj *obj)
{
	int retval = 0;
	struct list_head *p;
#ifndef _HAVE_MMAP
	ssize_t reads = 0;
#endif
	char *dstfile = unyaffs2_curfile;

	struct yaffs_ext_tags tag;
	struct yaffs_obj_hdr oh;
	struct unyaffs2_obj *child;

	if (obj == NULL) {
		if (unyaffs2_objtree.root == NULL)
			return 0;

		return unyaffs2_extract_objtree(unyaffs2_objtree.root);
	}

	if (!obj->valid) {
		/* others should NOT happend */
		UNYAFFS2_ERROR("obj %u is invalid!!!\n", obj->obj_id);
		return -1;
	}

	/* skip root object always */
	if (obj->obj_id == YAFFS_OBJECTID_ROOT) {
		obj->extracted = 1;
		goto next;
	}

	/*
	 * extract the object content
	 */
#ifdef _HAVE_MMAP
	memcpy(unyaffs2_databuf, unyaffs2_mmapinfo.addr + obj->hdr_off,
	       unyaffs2_bufsize);
#else
	lseek(unyaffs2_image_fd, obj->hdr_off, SEEK_SET);
	reads = safe_read(unyaffs2_image_fd,
			  unyaffs2_databuf, unyaffs2_bufsize);
#endif

#ifdef _HAVE_MMAP
	if (memcmp(unyaffs2_databuf, unyaffs2_mmapinfo.addr + obj->hdr_off,
	    unyaffs2_bufsize)) {
#else
	if (reads != unyaffs2_bufsize) {
#endif
		/* parse image failed */
		UNYAFFS2_DEBUG("error while reading the image ");
		UNYAFFS2_DEBUG("@ offset %lu\n", obj->hdr_off);
		return -1;
	}

	memcpy(&oh, unyaffs2_databuf, sizeof(struct yaffs_obj_hdr));
	if (UNYAFFS2_ISENDIAN)
		oh_endian_transform(&oh);

	unyaffs2_extract_packedtags(&tag,
				    unyaffs2_databuf +
				    unyaffs2_chunksize);

	if (unyaffs2_isempty(unyaffs2_databuf, unyaffs2_bufsize) ||
	    !tag.chunk_used || tag.chunk_id != 0 || tag.obj_id != obj->obj_id ||
	    oh.parent_obj_id != obj->parent_id) {
		/* parse image failed */
		UNYAFFS2_DEBUG("error while parsing the image ");
		UNYAFFS2_DEBUG("@ offset %lu",obj->hdr_off);
		UNYAFFS2_DEBUG("(is the same image?)\n");
		return -1;
	}

	strncpy(obj->name, oh.name, NAME_MAX);
	obj->type = oh.type;

	/* format the file path */
	if (unyaffs2_curfile[0] != '\0' &&
	    unyaffs2_curfile[strlen(unyaffs2_curfile) - 1] != '/')
		strncat(unyaffs2_curfile, "/",
			sizeof(unyaffs2_curfile) -
			strlen(unyaffs2_curfile) - 1);

	 strncat(unyaffs2_curfile, obj->name,
		 sizeof(unyaffs2_curfile) - strlen(unyaffs2_curfile) - 1);

	/* if a file(set) is specified */
	if (!list_empty(&unyaffs2_specfile_list)) {
		struct unyaffs2_specfile *spec = NULL;
		dstfile = NULL;
		spec = unyaffs2_specfile_lookup(unyaffs2_curfile);
		if (spec) {
			dstfile = unyaffs2_prefix_basestr(unyaffs2_curfile,
							  spec->path);
			if (!strcmp(unyaffs2_curfile, spec->path))
				spec->obj = obj;
		}

		if (!dstfile)
			goto next;
	}

	/* update obj field for hardlink and chattr used */
	if (obj->type == YAFFS_OBJECT_TYPE_HARDLINK) {
		/* 
		 * all hardlink are listed into the unyaffs2_hardlink_list,
		 * and they will be travel and extracted in the another process.
		 */
		UNYAFFS2_VERBOSE("hardlink: '%s'\n", dstfile);
		obj->variant.hardlink.equiv_obj =
			unyaffs2_objtable_lookup(oh.equiv_id);
		list_add_tail(&obj->hardlink, &unyaffs2_hardlink_list);
		goto next;
	}
	else {
		obj->mode = oh.yst_mode;
		obj->uid = oh.yst_uid;
		obj->gid = oh.yst_gid;
		obj->atime = oh.yst_atime;
		obj->mtime = oh.yst_mtime;
		obj->ctime = oh.yst_ctime;
	}

	switch (obj->type) {
	case YAFFS_OBJECT_TYPE_FILE:
		UNYAFFS2_VERBOSE("file: '%s'\n", dstfile);
		obj->variant.file.file_size = unyaffs2_extract_oh_size(&oh);
		retval =
#ifdef _HAVE_MMAP
		unyaffs2_extract_file_mmap(unyaffs2_mmapinfo.addr,
					   unyaffs2_mmapinfo.size,
					   obj->hdr_off + unyaffs2_bufsize,
					   dstfile, obj);
#else
		unyaffs2_extract_file(unyaffs2_image_fd,
				      obj->hdr_off + unyaffs2_bufsize,
				      dstfile, obj);
#endif
		break;
	case YAFFS_OBJECT_TYPE_DIRECTORY:
		UNYAFFS2_VERBOSE("dir: '%s'\n", dstfile);
		retval = unyaffs2_mkdir(dstfile, 0755);
		break;
	case YAFFS_OBJECT_TYPE_SYMLINK:
		UNYAFFS2_VERBOSE("symlink: '%s'\n", dstfile);
		retval = -1;
		obj->variant.symlink.alias = strdup(oh.alias);
		if (obj->variant.symlink.alias) { 
			unlink(dstfile);
			retval = symlink(obj->variant.symlink.alias, dstfile);
		}
		break;
	case YAFFS_OBJECT_TYPE_SPECIAL:
		if ((obj->mode & S_IFMT) &
		    (S_IFBLK | S_IFCHR | S_IFIFO | S_IFSOCK)) {
			obj->variant.dev.rdev = oh.yst_rdev;
			UNYAFFS2_VERBOSE("dev: '%s'\n", dstfile);
			retval = mknod(dstfile,
				       obj->mode, obj->variant.dev.rdev);
		}
		break;
	default:
		if (UNYAFFS2_ISVERBOSE)
			UNYAFFS2_WARN("unsupported type (%08x) for '%s'\n",
				      obj->type, dstfile);
		break;
	}

next:
	if (retval) {
		UNYAFFS2_ERROR("%cerror while extracting '%s'\n",
				UNYAFFS2_ISVERBOSE ? '\0' : '\n',
				unyaffs2_curfile);
	}
	else {
		if (!dstfile) {
		/* skip silently */
			UNYAFFS2_PROGRESS_BAR(++unyaffs2_image_objs,
					      unyaffs2_objtree.objs);
		}
		else if (obj->type != YAFFS_OBJECT_TYPE_HARDLINK) {
			obj->extracted = 1;
			UNYAFFS2_PROGRESS_BAR(++unyaffs2_image_objs,
					      unyaffs2_objtree.objs);
		}

		/* search its children if it is a directory. */
		if (obj->type == YAFFS_OBJECT_TYPE_DIRECTORY) {
			list_for_each(p, &obj->children) {
				child = list_entry(p, unyaffs2_obj_t,
						   siblings);
				retval |= unyaffs2_extract_objtree(child);
			}
		}
	}

	/* restore current file path */
	if (!strcmp(dirname(unyaffs2_curfile), "."))
		unyaffs2_curfile[0] = '\0';

	return retval;
}

/*-------------------------------------------------------------------------*/

static int
unyaffs2_load_spare (const char *oobfile)
{
	int fd, retval = 0;
	ssize_t reads;

	if (oobfile == NULL)
		return 0;

	if ((fd = open(oobfile, O_RDONLY)) < 0) {
		UNYAFFS2_DEBUG("open oob image failed\n");
		return -1;
	}

	reads = safe_read(fd, &nand_oob_user, sizeof(nand_ecclayout_t));
	if (reads != sizeof(nand_ecclayout_t)) {
		UNYAFFS2_DEBUG("parse oob image failed\n");
		retval = -1;
	}

	close(fd);

	return retval;
}

/*-------------------------------------------------------------------------*/

static int
unyaffs2_extract_image (const char *imgfile, const char *dirpath)
{
	int retval = 0;
	struct stat statbuf;
	struct unyaffs2_obj *root;

	/* verify whether the input image is valid */
	if (stat(imgfile, &statbuf) < 0 || !S_ISREG(statbuf.st_mode)) {
		UNYAFFS2_ERROR("image is not a regular file: '%s'\n", imgfile);
		return -1;
	}

	if ((statbuf.st_size % (unyaffs2_chunksize + unyaffs2_sparesize)) != 0)
	{
		UNYAFFS2_ERROR("image size (%lu) is NOT a mutiple of %u + %u\n",
				statbuf.st_size, unyaffs2_chunksize,
				unyaffs2_sparesize);
		return -1;
	}

	unyaffs2_image_fd = open(imgfile, O_RDONLY);
	if (unyaffs2_image_fd < 0) {
		UNYAFFS2_ERROR("cannot open the image file: '%s'\n", imgfile);
		return -1;
	}

#if _HAVE_MMAP
	unyaffs2_mmapinfo.addr = mmap(NULL, statbuf.st_size, PROT_READ,
				      MAP_PRIVATE, unyaffs2_image_fd, 0);
	if (unyaffs2_mmapinfo.addr == NULL) {
		UNYAFFS2_ERROR("mapping image failed\n");
		retval = -1;
		goto free_and_out;
	}

	unyaffs2_mmapinfo.size = statbuf.st_size;
#endif

	unyaffs2_bufsize = unyaffs2_chunksize + unyaffs2_sparesize;
	unyaffs2_databuf = (unsigned char *)malloc(unyaffs2_bufsize);
	if (unyaffs2_databuf == NULL) {
		UNYAFFS2_ERROR("cannot allocate working buffer ");
		UNYAFFS2_ERROR("(default: %u bytes)\n",
				unyaffs2_chunksize + unyaffs2_sparesize);
		goto free_and_out;
	}

	umask(0);

	if (unyaffs2_mkdir(dirpath, 0755) < 0 || chdir(dirpath) < 0 ||
	    (root = unyaffs2_create_fakeroot(".")) == NULL) {
		UNYAFFS2_ERROR("cannot access the directory ");
		UNYAFFS2_ERROR("'%s' (permission deny?)", dirpath);
		retval = -1;
		goto free_and_out;
	}

	unyaffs2_objtable_init();
	unyaffs2_objtree_init(&unyaffs2_objtree);

	unyaffs2_objtable_insert(root);

	/* stage 1: scanning image */
	UNYAFFS2_PRINT("scanning image '%s'... [*]", imgfile);

	if (unyaffs2_scan_img() < 0) {
		UNYAFFS2_ERROR("\nerror while scanning '%s'\n ", imgfile);
		retval = -1;
		goto exit_and_out;
	}

	UNYAFFS2_PRINT("\b\b\b[done]\nscanning complete, total objects: %d\n",
			unyaffs2_image_objs);

	UNYAFFS2_PRINT("building fs tree ... [*]");
	if (unyaffs2_build_objtree() < 0) {
		UNYAFFS2_ERROR("\nerror while building fs tree");
		retval = -1;
		goto exit_and_out;
	}
	unyaffs2_objtree.objs = unyaffs2_image_objs;
	UNYAFFS2_PRINT("\b\b\b[done]\nbuilding complete, ");
	UNYAFFS2_PRINT("total valid objects: %d\n", unyaffs2_objtree.objs);

	/* stage 2: extracting image */
	UNYAFFS2_PRINT("extracting image into '%s'\n", dirpath);

	UNYAFFS2_PROGRESS_INIT();
	unyaffs2_image_objs = 0;

	/* extract objs in the obj tree */
	memset(unyaffs2_curfile, 0, sizeof(unyaffs2_curfile));
	retval = unyaffs2_extract_objtree(NULL);

	/* extract hardlinks in the obj tree */
	retval |= unyaffs2_extract_hardlink(NULL);

	/* modify attr for objects in the objtree */
	UNYAFFS2_PRINT("\nmodify files attributes... [*]");

	if (!list_empty(&unyaffs2_specfile_list)) {
		struct list_head *p;
		struct unyaffs2_specfile *spec;
		list_for_each(p, &unyaffs2_specfile_list) {
			spec = list_entry(p, unyaffs2_specfile_t, list);
			if (spec->obj) {
				memset(unyaffs2_curfile, 0,
				       sizeof(unyaffs2_curfile));
				unyaffs2_objtree_chattr(spec->obj);
			}
			else {
				retval = -1;
				UNYAFFS2_ERROR("File NOT found: '%s'\n",
						spec->path);
			}
		}
	}
	else {
		memset(unyaffs2_curfile, 0, sizeof(unyaffs2_curfile));
		unyaffs2_objtree_chattr(NULL);
	}

	if (!retval)
		UNYAFFS2_PRINT("\b\b\b[done]\n");

exit_and_out:
	unyaffs2_objtree_exit(&unyaffs2_objtree);
	unyaffs2_objtable_exit();
free_and_out:
	if (unyaffs2_image_fd >= 0)
		close(unyaffs2_image_fd);
	if (unyaffs2_databuf)
		free(unyaffs2_databuf);

	return retval;
}

/*-------------------------------------------------------------------------*/

static int
unyaffs2_helper (void)
{
	UNYAFFS2_HELP("Usage: ");
	UNYAFFS2_HELP("unyaffs2 [-h] [-e] [-v] [-p pagesize] [-s sparesize] "
		      "[-o file] [-f file] imgfile dirname\n");
	UNYAFFS2_HELP("unyaffs2: A utility to extract the yaffs2 image\n");
	UNYAFFS2_HELP("version: %s\n", YAFFS2UTILS_VERSION);
	UNYAFFS2_HELP("options:\n");
	UNYAFFS2_HELP("	-h	display this help message and exit.\n");
	UNYAFFS2_HELP("	-e	convert endian differed from local machine.\n");
	UNYAFFS2_HELP("	-v	verbose details instead of progress bar.\n");
	UNYAFFS2_HELP("	-p size	page size of target device.\n"
		      "		(512|2048|4096|(8192)|(16384) bytes, default: %u).\n",
		      DEFAULT_CHUNKSIZE);
	UNYAFFS2_HELP("	-s size	spare size of target device.\n"
		      "		(default: pagesize/32 bytes; max: pagesize)\n");
	UNYAFFS2_HELP("	-o file	load external oob image file.\n");;
	UNYAFFS2_HELP("	-f file	extract the specified file.\n");;

	return -1;
}

/*-------------------------------------------------------------------------*/

int
main (int argc, char* argv[])
{
	int retval;
	char *imgfile = NULL, *dirpath = NULL, *oobfile = NULL;

	int option, option_index;
	static const char *short_options = "hvep:s:o:f:";
	static const struct option long_options[] = {
		{"pagesize",	required_argument, 	0, 'p'},
		{"sparesize",	required_argument,	0, 's'},
		{"oobimg",	required_argument, 	0, 'o'},
		{"file",	required_argument, 	0, 'f'},
		{"endian",	no_argument, 		0, 'e'},
		{"verbose",	no_argument,	 	0, 'v'},
		{"help",	no_argument, 		0, 'h'},
	};

	UNYAFFS2_PRINT("unyaffs2-%s: image extracting tool for YAFFS2\n",
		YAFFS2UTILS_VERSION);

	if (getuid() != 0) {
		unyaffs2_flags |= UNYAFFS2_FLAGS_NONROOT;
		UNYAFFS2_WARN("warning: non-root users\n");
		UNYAFFS2_WARN("suggest: executing this tool as root\n");
	}

	unyaffs2_chunksize = DEFAULT_CHUNKSIZE;

	while ((option = getopt_long(argc, argv, short_options,
				     long_options, &option_index)) != EOF) 
	{
		switch (option) {
		case 'p':
			unyaffs2_chunksize = strtol(optarg, NULL, 10);
			break;
		case 's':
			unyaffs2_sparesize = strtol(optarg, NULL, 10);
			break;
		case 'o':
			oobfile = optarg;
			break;
		case 'f':
			retval = unyaffs2_specfile_insert(optarg);
			if (retval) {
				UNYAFFS2_ERROR("cannot specify the file '%s'",
						optarg);
				UNYAFFS2_ERROR("(invalid string ?)\n");
				unyaffs2_specfile_exit();
				return -1;
			}
			break;
		case 'e':
			unyaffs2_flags |= UNYAFFS2_FLAGS_ENDIAN;
			break;
		case 'v':
			unyaffs2_flags |= UNYAFFS2_FLAGS_VERBOSE;
			break;
		case 'h':
		default:
			return unyaffs2_helper();
		}
	}

	if (argc - optind < 2)
		return unyaffs2_helper();

	imgfile = argv[optind];
	dirpath = argv[optind + 1];

	/* validate the page size */
	switch (unyaffs2_chunksize) {
	case 512:
		unyaffs2_flags |= UNYAFFS2_FLAGS_YAFFS1;
		if (oobfile == NULL)
			unyaffs2_oobinfo = &nand_oob_16;
		break;
	case 2048:
		if (oobfile == NULL)
			unyaffs2_oobinfo = &nand_oob_64;
		break;
	case 4096:
	case 8192:
	case 16384:
		/* FIXME: The OOB scheme for 8192 and 16384. */
		if (oobfile == NULL)
			unyaffs2_oobinfo = &nand_oob_128;
		break;
	default:
		UNYAFFS2_ERROR("%u bytes page size is not supported\n",
				unyaffs2_chunksize);
		return -1;
	}

	/* spare size */
	if (!unyaffs2_sparesize)
		unyaffs2_sparesize = unyaffs2_chunksize / 32;

	if (unyaffs2_sparesize > unyaffs2_chunksize) {
		UNYAFFS2_ERROR("spare size is too large (%u)\n",
				unyaffs2_sparesize);
		return -1;
	}

	if (oobfile) {
		if (unyaffs2_load_spare(oobfile) < 0) {
			UNYAFFS2_ERROR("parse oob image failed\n");
			return -1;
		}
		unyaffs2_oobinfo = &nand_oob_user;
		/* FIXME: verify for the various ecc layout */
	}

	retval = unyaffs2_extract_image(imgfile, dirpath);
	if (!retval) {
		UNYAFFS2_PRINT("%coperation complete\n",
				UNYAFFS2_ISVERBOSE ? '\n' : '\0');
		UNYAFFS2_PRINT("files are extracted into '%s'\n", dirpath);
	}
	else {
		UNYAFFS2_ERROR("\noperation incomplete\n");
		UNYAFFS2_ERROR("files contents may be broken\n");
	}

	unyaffs2_specfile_exit();

	return retval;
}
