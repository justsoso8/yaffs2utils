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
#include <unistd.h>
#include <stdlib.h>
#include <dirent.h>
#include <getopt.h>
#include <string.h>
#include <limits.h>
#include <libgen.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifdef _HAVE_OSX_SYSLIMITS
#include <sys/syslimits.h>
#endif

#include "yaffs_trace.h"
#include "yaffs_packedtags1.h"
#include "yaffs_packedtags2.h"

#include "yaffs2utils_io.h"
#include "yaffs2utils_ecc.h"
#include "yaffs2utils_list.h"
#include "yaffs2utils_endian.h"
#include "yaffs2utils_progress.h"

#include "yaffs2utils_version.h"

/*----------------------------------------------------------------------------*/

#define MKYAFFS2_OBJTABLE_SIZE	YAFFS_NOBJECT_BUCKETS

#define MKYAFFS2_FLAGS_NONROOT	0x01
#define MKYAFFS2_FLAGS_YAFFS1	0x02
#define MKYAFFS2_FLAGS_ENDIAN	0x04
#define MKYAFFS2_FLAGS_VERBOSE	0x08

#define MKYAFFS2_ISYAFFS1	(mkyaffs2_flags & MKYAFFS2_FLAGS_YAFFS1)
#define MKYAFFS2_ISENDIAN	(mkyaffs2_flags & MKYAFFS2_FLAGS_ENDIAN)
#define MKYAFFS2_ISVERBOSE	(mkyaffs2_flags & MKYAFFS2_FLAGS_VERBOSE)

#define MKYAFFS2_PRINT(s, args...)	fprintf(stdout, s, ##args)

#define MKYAFFS2_ERROR(s, args...)	fprintf(stderr, s, ##args)

#define MKYAFFS2_WARN(s, args...)	MKYAFFS2_ERROR(s, ##args)

#define MKYAFFS2_HELP(s, args...)	MKYAFFS2_ERROR(s, ##args)

#ifdef _MKYAFFS2_DEBUG
#define MKYAFFS2_DEBUG(s, args...)	MKYAFFS2_ERROR(s, ##args)
#else
#define MKYAFFS2_DEBUG(s, args...)
#endif

#define MKYAFFS2_VERBOSE(s, args...) \
		({ if (MKYAFFS2_ISVERBOSE) \
			MKYAFFS2_PRINT(s, ##args);})

#define MKYAFFS2_PROGRESS_INIT() \
		({ if (!MKYAFFS2_ISVERBOSE) \
			progress_init();})

#define MKYAFFS2_PROGRESS_BAR(objs, total) \
		({ if (!MKYAFFS2_ISVERBOSE) \
			progress_bar(objs, total);})

/*----------------------------------------------------------------------------*/

/* symlink */
typedef union mkyaffs2_link {
	char *alias;
	struct mkyaffs2_obj *equiv_obj;
} mkyaffs2_link_t;

typedef struct mkyaffs2_obj {
	dev_t dev;
	ino_t ino;

	unsigned obj_id;
	char name[NAME_MAX + 1];

	struct mkyaffs2_obj *parent_obj;
	struct list_head children;	/* for a directory */
	struct list_head siblings;	/* neighbors in the same directory */
	struct list_head hashlist;	/* hash table */
} mkyaffs2_obj_t;

typedef struct mkyaffs2_fstree {
	unsigned objs;
	struct mkyaffs2_obj *root;
} mkyaffs2_fstree_t;

/*----------------------------------------------------------------------------*/

static unsigned mkyaffs2_flags = 0;

static unsigned mkyaffs2_chunksize = 0;
static unsigned mkyaffs2_sparesize = 0;

static unsigned mkyaffs2_image_obj_id = YAFFS_NOBJECT_BUCKETS;
static unsigned mkyaffs2_image_objs = 0;
static unsigned mkyaffs2_image_pages = 0;

static int mkyaffs2_image_fd = -1;

static char mkyaffs2_curfile[PATH_MAX + PATH_MAX] = {0};
static char mkyaffs2_linkfile[PATH_MAX] = {0};

static nand_ecclayout_t *mkyaffs2_oobinfo = NULL;
static int (*mkyaffs2_writechunk)(unsigned, unsigned, unsigned) = NULL;

static unsigned mkyaffs2_bufsize = 0;
static unsigned char *mkyaffs2_databuf = NULL;

static struct mkyaffs2_fstree mkyaffs2_objtree = {0};
static struct list_head mkyaffs2_objtable[MKYAFFS2_OBJTABLE_SIZE];

/*----------------------------------------------------------------------------*/

static struct mkyaffs2_obj *
mkyaffs2_obj_alloc (void)
{
	struct mkyaffs2_obj *obj;

	obj = calloc(sizeof(struct mkyaffs2_obj), sizeof(unsigned char));
	if (obj == NULL)
		return NULL;

	obj->parent_obj = obj;

	INIT_LIST_HEAD(&obj->hashlist);
	INIT_LIST_HEAD(&obj->children);
	INIT_LIST_HEAD(&obj->siblings);

	return obj;
}

static void
mkyaffs2_obj_free (struct mkyaffs2_obj *object)
{
	list_del(&object->children);
	list_del(&object->siblings);
	list_del(&object->hashlist);

	free(object);
}

/*----------------------------------------------------------------------------*/

static inline unsigned
mkyaffs2_objtable_hash (unsigned hash)
{
	return hash % MKYAFFS2_OBJTABLE_SIZE;
}

static inline void
mkyaffs2_objtable_insert (struct mkyaffs2_obj *object)
{
	unsigned n = mkyaffs2_objtable_hash(object->ino);
	list_add_tail(&object->hashlist, &mkyaffs2_objtable[n]);
}

static inline struct mkyaffs2_obj *
mkyaffs2_objtable_lookup (dev_t dev, ino_t ino)
{
	unsigned n = mkyaffs2_objtable_hash(ino);
	struct list_head *p;
	struct mkyaffs2_obj *obj;

	list_for_each(p, &mkyaffs2_objtable[n]) {
		obj = list_entry(p, mkyaffs2_obj_t, hashlist);
		if (obj->dev == dev && obj->ino == ino)
			return obj;
	}

	return NULL;
}

static inline void
mkyaffs2_objtable_init (void)
{
	unsigned n;

	for (n = 0; n < MKYAFFS2_OBJTABLE_SIZE; n++)
		INIT_LIST_HEAD(&mkyaffs2_objtable[n]);
}

static inline void
mkyaffs2_objtable_exit (void)
{
	unsigned i;
	struct mkyaffs2_obj *obj;
	struct list_head *p, *n;

	for (i = 0; i < MKYAFFS2_OBJTABLE_SIZE; i++) {
		list_for_each_safe(p, n, &mkyaffs2_objtable[i]) {
			obj = list_entry(p, struct mkyaffs2_obj, hashlist);
			mkyaffs2_obj_free(obj);
		}
	}
}

/*----------------------------------------------------------------------------*/

static void
mkyaffs2_objtree_cleanup (struct mkyaffs2_obj *object)
{
	struct mkyaffs2_obj *obj;
	struct list_head *p, *n;

	if (object == NULL)
		return;

	list_for_each_safe(p, n, &object->children) {
		obj = list_entry(p, mkyaffs2_obj_t, siblings);
		mkyaffs2_objtree_cleanup(obj);
	}

	mkyaffs2_obj_free(object);
}

static struct mkyaffs2_fstree *
mkyaffs2_objtree_init (struct mkyaffs2_fstree *fst)
{
	struct mkyaffs2_fstree *f = fst;

	if (f == NULL) {
		f = malloc(sizeof(struct mkyaffs2_fstree));
		if (f == NULL)
			return NULL;
	}

	/* initialize */
	memset(f, 0, sizeof(struct mkyaffs2_fstree));

	return f;
}

static void
mkyaffs2_objtree_exit (struct mkyaffs2_fstree *fst)
{
	mkyaffs2_objtree_cleanup(fst->root);
}

/*----------------------------------------------------------------------------*/

static void 
mkyaffs2_packedtags1_ecc (struct yaffs_packed_tags1 *pt)
{
	unsigned char *b = ((union yaffs_tags_union *)pt)->as_bytes;
	unsigned i, j;
	unsigned ecc = 0, bit = 0;

	/* clear the ecc field */
	if (MKYAFFS2_ISYAFFS1) {
#if defined(__LITTLE_ENDIAN_BITFIELD)
		b[6] &= 0xc0;
		b[7] &= 0x03;
#elif defined(__BIG_ENDIAN_BITFIELD)
		b[6] &= 0x03;
		b[7] &= 0xc0;
#endif
	}
	else
		pt->ecc = 0;

	/* calculate ecc */
	for (i = 0; i < 8; i++) {
		for (j = 1; j & 0xff; j <<= 1) {
			bit++;
			if (b[i] & j)
				ecc ^= bit;
		}
	}

	/* write ecc back to tags */
	if (MKYAFFS2_ISENDIAN) {
#if defined(__LITTLE_ENDIAN_BITFIELD)
		b[6] |= ((ecc >> 6) & 0x3f);
		b[7] |= ((ecc & 0x3f) << 2);
#elif defined(__BIG_ENDIAN_BITFIELD)
		b[6] |= ((ecc & 0x3f) << 2);
		b[7] |= ((ecc >> 6) & 0x3f);
#endif
	}
	else
		pt->ecc = ecc;
}

static ssize_t
mkyaffs2_tag2spare (unsigned char *spare, unsigned char *tag, size_t bytes)
{
	unsigned i;
	size_t copied = 0;
	struct nand_oobfree *oobfree = mkyaffs2_oobinfo->oobfree;

	for (i = 0; i < MTD_MAX_OOBFREE_ENTRIES && copied < bytes; i++) {
		size_t size = bytes - copied;
		unsigned char *s = spare + oobfree[i].offset;

		if (size > oobfree[i].length)
			size = oobfree[i].length;

		memcpy(s, tag, size);
		if (memcmp(s, tag, size))
			return -1;

		copied += size;
		tag += size;
	}

	return copied;
}

/*----------------------------------------------------------------------------*/

static int 
mkyaffs2_yaffs1_writechunk (unsigned bytes, unsigned obj_id, unsigned chunk_id)
{
	ssize_t written;
	struct yaffs_ext_tags tag;
	struct yaffs_packed_tags1 pt;
	unsigned char *spare = mkyaffs2_databuf + mkyaffs2_chunksize;

	/* prepare the spare (oob) first */
	memset(&tag, 0, sizeof(struct yaffs_ext_tags));

	tag.chunk_id = chunk_id;
	tag.serial_number = 1;	// double check
	tag.n_bytes = bytes;
	tag.obj_id = obj_id;
	tag.is_deleted = 0;	// double check

	memset(&pt, 0xff, sizeof(struct yaffs_packed_tags1));
	yaffs_pack_tags1(&pt, &tag);

	if (MKYAFFS2_ISENDIAN)
		packedtags1_endian_transform(&pt, 0);

#ifndef YAFFS_IGNORE_TAGS_ECC
	mkyaffs2_packedtags1_ecc(&pt);
#endif

	/* write the spare (oob) into the buffer */
	memset(spare, 0xff, mkyaffs2_sparesize);
	written = mkyaffs2_tag2spare(spare, (unsigned char *)&pt,
				     sizeof(struct yaffs_packed_tags1) -
				     sizeof(pt.should_be_ff));
	if (written < 0)
		return -1;

	/* write a whole "chunk + spare" back to the image */
	written = safe_write(mkyaffs2_image_fd, 
			     mkyaffs2_databuf, mkyaffs2_bufsize);
	if (written != mkyaffs2_bufsize)
		return -1;

	mkyaffs2_image_pages++;

	return 0;
}

static int
mkyaffs2_yaffs2_writechunk (unsigned bytes, unsigned obj_id, unsigned chunk_id)
{
	ssize_t written;
	struct yaffs_ext_tags tag;
	struct yaffs_packed_tags2 pt;
	unsigned char *spare = mkyaffs2_databuf + mkyaffs2_chunksize;

	/* prepare the spare (oob) first */
	memset(&tag, 0, sizeof(struct yaffs_ext_tags));
	
	tag.chunk_id = chunk_id;
	tag.serial_number = 1;	// double check
	tag.n_bytes = bytes;
	tag.obj_id = obj_id;
	tag.chunk_used = 1;
	tag.seq_number = YAFFS_LOWEST_SEQUENCE_NUMBER;

	memset(&pt, 0xff, sizeof(struct yaffs_packed_tags2));
	yaffs_pack_tags2_tags_only(&pt.t, &tag);

	if (MKYAFFS2_ISENDIAN)
		packedtags2_tagspart_endian_transform(&pt);

#ifndef YAFFS_IGNORE_TAGS_ECC
	yaffs_ecc_calc_other((unsigned char *)&pt.t,
				sizeof(struct yaffs_packed_tags2_tags_only),
				&pt.ecc);
	if (MKYAFFS2_ISENDIAN)
		packedtags2_eccother_endian_transform(&pt);
#endif

	/* write the spare (oob) into the buffer */
	memset(spare, 0xff, mkyaffs2_sparesize);
	written = mkyaffs2_tag2spare(spare, (unsigned char *)&pt,
				     sizeof(struct yaffs_packed_tags2));
	if (written < 0)
		return -1;

	/* write a whole "chunk + spare" back to the image */
	written = safe_write(mkyaffs2_image_fd,
			     mkyaffs2_databuf, mkyaffs2_bufsize);
	if (written != mkyaffs2_bufsize)
		return -1;

	mkyaffs2_image_pages++;

	return 0;
}

static int 
mkyaffs2_write_oh (struct mkyaffs2_obj *obj,
		   struct stat *s,
		   enum yaffs_obj_type type,
		   union mkyaffs2_link *ylink)
{
	int retval;
	struct yaffs_obj_hdr oh;

	memset(&oh, 0xff, sizeof(struct yaffs_obj_hdr));

	oh.type = type;
	oh.parent_obj_id = obj->parent_obj->obj_id;
	strncpy(oh.name, obj->name, YAFFS_MAX_NAME_LENGTH);
	if (strlen(obj->name) > YAFFS_MAX_NAME_LENGTH && MKYAFFS2_ISVERBOSE)
		MKYAFFS2_WARN("file name is too long, it will be truncated\n");
	
	if(type != YAFFS_OBJECT_TYPE_HARDLINK) {
		oh.yst_mode = s->st_mode;
		oh.yst_uid = s->st_uid;
		oh.yst_gid = s->st_gid;
		oh.yst_atime = s->st_atime;
		oh.yst_mtime = s->st_mtime;
		oh.yst_ctime = s->st_ctime;
		oh.yst_rdev  = s->st_rdev;
	}

	switch (type) {
	case YAFFS_OBJECT_TYPE_FILE:
		oh.file_size_low = s->st_size;
		break;
	case YAFFS_OBJECT_TYPE_HARDLINK:
		oh.equiv_id = ylink->equiv_obj->obj_id;
		break;
	case YAFFS_OBJECT_TYPE_SYMLINK:
		strncpy(oh.alias, ylink->alias, YAFFS_MAX_ALIAS_LENGTH);
		if (MKYAFFS2_ISVERBOSE &&
		    strlen(obj->name) > YAFFS_MAX_ALIAS_LENGTH)
			MKYAFFS2_WARN("alias name will be truncated\n");
		break;
	default:
		break;
	}

	if (MKYAFFS2_ISENDIAN)
 	   	oh_endian_transform(&oh);

	/* copy header into the buffer */
	memset(mkyaffs2_databuf, 0xff, mkyaffs2_chunksize);
	memcpy(mkyaffs2_databuf, &oh, sizeof(struct yaffs_obj_hdr));

	/* write buffer */
	retval = mkyaffs2_writechunk(0xffff, obj->obj_id, 0);

	return retval;
}

static int 
mkyaffs2_write_regfile (const char *fpath, unsigned obj_id)
{
	int fd, retval = 0;
	unsigned chunk = 0;
	unsigned char *databuf = mkyaffs2_databuf;
	ssize_t bytes;

	fd = open(fpath, O_RDONLY);
	if (fd < 0) {
		MKYAFFS2_DEBUG("cannot open the file: '%s'\n", fpath);
		return -1;
	}

	memset(databuf, 0xff, mkyaffs2_chunksize);
	while((bytes = safe_read(fd, databuf, mkyaffs2_chunksize)) != 0) {
		if (bytes < 0) {
			MKYAFFS2_DEBUG("error while reading file '%s'\n",
					fpath);
			retval = bytes;
			break;
		}

		/* write buffer */
		retval = mkyaffs2_writechunk(bytes, obj_id, ++chunk);
		if (retval) {
			MKYAFFS2_DEBUG("error while writing file '%s'\n",
					fpath);
			break;
		}

		memset(databuf, 0xff, mkyaffs2_chunksize);
	}

	close(fd);

	return retval;
}

/*----------------------------------------------------------------------------*/

static inline void
mkyaffs2_scan_dir_status (unsigned status)
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

	MKYAFFS2_PRINT("\b\b\b[%c]", st);
	fflush(stdout);
}

static int
mkyaffs2_scan_dir (struct mkyaffs2_obj *parent)
{
	DIR *dir;
	struct stat s;
	struct dirent *dent;
	struct mkyaffs2_obj *obj = NULL;

	if (parent == NULL) {
		if (mkyaffs2_objtree.root) {
			mkyaffs2_objtree_exit(&mkyaffs2_objtree);
			mkyaffs2_objtree_init(&mkyaffs2_objtree);
		}

		if (stat(mkyaffs2_curfile[0] == '\0' ? 
			 "." : mkyaffs2_curfile, &s) ||
		    !S_ISDIR(s.st_mode)) {
			MKYAFFS2_DEBUG("root is NOT a directory ('%s')\n",
					mkyaffs2_curfile);
			return -1;
		}

		obj = mkyaffs2_obj_alloc();
		if (obj == NULL) {
			MKYAFFS2_DEBUG("allocate object failed for '%s'\n",
					mkyaffs2_curfile);
			return -1;
		}

		mkyaffs2_objtree.root = obj;
		mkyaffs2_scan_dir_status(++mkyaffs2_objtree.objs);

		return mkyaffs2_scan_dir(obj);
	}

	dir = opendir(mkyaffs2_curfile[0] == '\0' ? "." : mkyaffs2_curfile);
	if (dir == NULL) {
		MKYAFFS2_ERROR("cannot open the directory: '%s'\n",
				mkyaffs2_curfile);
		return -1;
	}

	while((dent = readdir(dir)) != NULL) {
		if (!strcmp(dent->d_name, ".") || !strcmp(dent->d_name, ".."))
			continue;

		if (mkyaffs2_curfile[0] != '\0' &&
		    mkyaffs2_curfile[strlen(mkyaffs2_curfile) - 1] != '/')
			strncat(mkyaffs2_curfile, "/", 
				sizeof(mkyaffs2_curfile) -
				strlen(mkyaffs2_curfile) - 1);

		strncat(mkyaffs2_curfile, dent->d_name,
			sizeof(mkyaffs2_curfile) - strlen(mkyaffs2_curfile) - 1);

		obj = mkyaffs2_obj_alloc();
		if (obj == NULL) {
			MKYAFFS2_DEBUG("allocate object failed for '%s'\n",
					mkyaffs2_curfile);
			return -1;
		}

		strncpy(obj->name, dent->d_name, NAME_MAX);
		obj->parent_obj = parent;
		list_add_tail(&obj->siblings, &parent->children);
		mkyaffs2_scan_dir_status(++mkyaffs2_objtree.objs);

		MKYAFFS2_DEBUG("object '%s' : '%s'\n", 
				obj->name, mkyaffs2_curfile);

		if (!lstat(mkyaffs2_curfile, &s) && S_ISDIR(s.st_mode))
			mkyaffs2_scan_dir(obj);

		if (!strcmp(dirname(mkyaffs2_curfile), "."))
			mkyaffs2_curfile[0] = '\0';
	}

	closedir(dir);

	return 0;
}

static int
mkyaffs2_process_objtree (struct mkyaffs2_obj *obj)
{
	int retval = 0;
	struct stat s;

	struct list_head *p;
	struct mkyaffs2_obj *child;
	union mkyaffs2_link ylink;

	if (obj == NULL) {
		if (mkyaffs2_objtree.root == NULL)
			return 0;

		return mkyaffs2_process_objtree(mkyaffs2_objtree.root);
	}

	/* root object */
	if (obj == mkyaffs2_objtree.root) {
		if (stat(mkyaffs2_curfile[0] == '\0' ?
			 "." : mkyaffs2_curfile, &s) < 0 ||
		    !S_ISDIR(s.st_mode)) {
			MKYAFFS2_DEBUG("root object is NOT a directory '%s'\n",
					mkyaffs2_curfile);
			return -1;
		}

		mkyaffs2_image_objs = 0;
		mkyaffs2_image_obj_id = YAFFS_NOBJECT_BUCKETS;

		obj->dev = s.st_dev;
		obj->ino = s.st_ino;
		obj->obj_id = YAFFS_OBJECTID_ROOT;

		mkyaffs2_objtable_insert(obj);

		/* only write root object when yaffs2 is applied */
		if (MKYAFFS2_ISYAFFS1)
			retval = mkyaffs2_write_oh(obj, &s,
						   YAFFS_OBJECT_TYPE_DIRECTORY,
						   NULL);

		goto next;
	}

	if (!strlen(obj->name)) {
		/* it should NOT happen! */
		MKYAFFS2_DEBUG("skipping obj with empty name\n");
		return 0;
	}

	/* format file path */
	if (mkyaffs2_curfile[0] != '\0' &&
	    mkyaffs2_curfile[strlen(mkyaffs2_curfile) - 1] != '/')
		strncat(mkyaffs2_curfile, "/",
			sizeof(mkyaffs2_curfile) -
			strlen(mkyaffs2_curfile) - 1);

	strncat(mkyaffs2_curfile, obj->name,
		sizeof(mkyaffs2_curfile) - strlen(mkyaffs2_curfile) - 1);

	retval = lstat(mkyaffs2_curfile, &s);
	if (retval) {
		MKYAFFS2_VERBOSE("error while processing file '%s' ",
				 mkyaffs2_curfile);
		MKYAFFS2_VERBOSE("(permission denied?)");
		goto next;
	}

		/* update the obj */
		obj->dev = s.st_dev;
		obj->ino = s.st_ino;
		obj->obj_id = ++mkyaffs2_image_obj_id;

	if (obj->obj_id > YAFFS_MAX_OBJECT_ID && MKYAFFS2_ISVERBOSE)
		MKYAFFS2_WARN("too many files!\n ");

	MKYAFFS2_VERBOSE("object %u, '%s' is a ", 
			 obj->obj_id, mkyaffs2_curfile);

	/* hardlink? */
	ylink.equiv_obj = mkyaffs2_objtable_lookup(obj->dev, obj->ino);
	if (ylink.equiv_obj != NULL) {
		MKYAFFS2_VERBOSE("hard link to object %u\n", 
				 ylink.equiv_obj->obj_id);
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_HARDLINK, &ylink);
		goto next;
	}

	mkyaffs2_objtable_insert(obj);

	switch (s.st_mode & S_IFMT) {
	case S_IFREG:
		MKYAFFS2_VERBOSE("file\n");
		retval = mkyaffs2_write_oh(obj, &s, YAFFS_OBJECT_TYPE_FILE,
					   NULL);
		if (!retval)
			retval = mkyaffs2_write_regfile(mkyaffs2_curfile,
							obj->obj_id);
		break;
	case S_IFLNK:
		memset(mkyaffs2_linkfile, 0,
		       sizeof(mkyaffs2_linkfile));
		readlink(mkyaffs2_curfile, mkyaffs2_linkfile,
			 sizeof(mkyaffs2_linkfile) - 1);
		MKYAFFS2_VERBOSE("symbolic link to '%s'\n",
				 mkyaffs2_linkfile);
		ylink.alias = mkyaffs2_linkfile;
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_SYMLINK, &ylink);
		break;
	case S_IFDIR:
		MKYAFFS2_VERBOSE("directory\n");
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_DIRECTORY, NULL);
		break;
	case S_IFBLK:
		MKYAFFS2_VERBOSE("block device\n");
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_SPECIAL, NULL);
		break;
	case S_IFCHR:
		MKYAFFS2_VERBOSE("character device\n");
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_SPECIAL, NULL);
		break;
	case S_IFIFO:
		MKYAFFS2_VERBOSE("fifo\n");
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_SPECIAL, NULL);
		break;
	case S_IFSOCK:
		MKYAFFS2_VERBOSE("socket\n");
		retval = mkyaffs2_write_oh(obj, &s,
					   YAFFS_OBJECT_TYPE_SPECIAL, NULL);
		break;
	default:
		/* skipping un-supported files silently */
		MKYAFFS2_DEBUG("skipped (unsupported file)\n");
	}

next:
	if (retval) {
		MKYAFFS2_ERROR("%cerror while parsing '%s'\n",
				MKYAFFS2_ISVERBOSE ? '\0' : '\n',
				mkyaffs2_curfile);
	}
	else {
		MKYAFFS2_PROGRESS_BAR(++mkyaffs2_image_objs,
				      mkyaffs2_objtree.objs);

		if (S_ISDIR(s.st_mode)) {
			list_for_each(p, &obj->children) {
				child = list_entry(p, mkyaffs2_obj_t, siblings);
				retval = mkyaffs2_process_objtree(child);
				if (retval < 0)
					break;
			}
		}
	}

	/* restore current file path */
	if (!strcmp(dirname(mkyaffs2_curfile), "."))
		mkyaffs2_curfile[0] = '\0';

	return retval;
}

/*----------------------------------------------------------------------------*/

static int
mkyaffs2_load_spare (const char *oobfile)
{
	int fd, retval = 0;
	ssize_t reads;

	if (oobfile == NULL)
		return 0;

	if ((fd = open(oobfile, O_RDONLY)) < 0) {
		MKYAFFS2_DEBUG("open oob image failed\n");
		return -1;
	}

	reads = safe_read(fd, &nand_oob_user, sizeof(nand_ecclayout_t));
	if (reads != sizeof(nand_ecclayout_t)) {
		MKYAFFS2_DEBUG("parse oob image failed\n");
		retval = -1;
	}

	close(fd);

	return retval;
}


/*----------------------------------------------------------------------------*/

static int
mkyaffs2_create_image (const char *dirpath, const char *imgfile)
{
	int retval;

	/* table initiailzation */
	mkyaffs2_objtable_init();
	mkyaffs2_objtree_init(&mkyaffs2_objtree);

	/* allocate working buffer */
	mkyaffs2_bufsize = mkyaffs2_chunksize + mkyaffs2_sparesize;
	mkyaffs2_databuf = (unsigned char *)malloc(mkyaffs2_bufsize);
	if (mkyaffs2_databuf == NULL) {
		MKYAFFS2_ERROR("cannot allocate working buffer ");
		MKYAFFS2_ERROR("(default: %u bytes)\n",
				mkyaffs2_chunksize + mkyaffs2_sparesize);
		retval = -1;
		goto exit_and_out;
	}

	mkyaffs2_image_fd = open(imgfile, O_WRONLY | O_CREAT | O_TRUNC, 0644);
	if (mkyaffs2_image_fd < 0) {
		MKYAFFS2_ERROR("cannot open the image file: '%s'\n", imgfile);
		retval = -1;
		goto free_and_out;
	}

	/* stage 1: scanning direcotry */
	snprintf(mkyaffs2_curfile, PATH_MAX, "%s", dirpath);
	MKYAFFS2_PRINT("stage 1: scanning directory '%s'... [*]",
			mkyaffs2_curfile);

	retval = mkyaffs2_scan_dir(NULL);
	if (retval < 0) {
		MKYAFFS2_ERROR("\nerrors while scanning '%s'\n", dirpath);
		retval = -1;
		goto free_and_out;
	}

	MKYAFFS2_PRINT("\b\b\b[done]\nscanning complete, total %u objects.\n",
			mkyaffs2_objtree.objs);

	/* stage 2: making a image */
	MKYAFFS2_PRINT("stage 2: making image '%s'\n", imgfile);

	MKYAFFS2_PROGRESS_INIT();

	snprintf(mkyaffs2_curfile, PATH_MAX, "%s", dirpath);
	retval = mkyaffs2_process_objtree(NULL);

free_and_out:
	if (mkyaffs2_image_fd >= 0)
		close(mkyaffs2_image_fd);
	free(mkyaffs2_databuf);
exit_and_out:
	mkyaffs2_objtree_exit(&mkyaffs2_objtree);
	mkyaffs2_objtable_exit();

	return retval;
}

/*----------------------------------------------------------------------------*/

static int
mkyaffs2_helper (void)
{
	MKYAFFS2_HELP("Usage: ");
	MKYAFFS2_HELP("mkyaffs2 [-h] [-e] [-v] [-p pagesize] [-s sparesize] "
		      "[-o file] dirname imgfile\n");
	MKYAFFS2_HELP("mkyaffs2: A utility to make the yaffs2 image\n");
	MKYAFFS2_HELP("version: %s\n", YAFFS2UTILS_VERSION);
	MKYAFFS2_HELP("options:\n");
	MKYAFFS2_HELP("	-h	display this help message and exit.\n");
	MKYAFFS2_HELP("	-e	convert endian differed from local machine.\n");
	MKYAFFS2_HELP("	-v	verbose details instead of progress bar.\n");
	MKYAFFS2_HELP("	-p size	page size of target device.\n"
		      "		(512|2048|4096|(8192)|(16384) bytes, default: %u).\n",
		      DEFAULT_CHUNKSIZE);
	MKYAFFS2_HELP("	-s size spare size of target device.\n"
		      "		(default: pagesize/32 bytes; max: pagesize)\n");
	MKYAFFS2_HELP("	-o file	load external oob image file.\n");

	return -1;
}

/*----------------------------------------------------------------------------*/

int 
main (int argc, char *argv[])
{
	int retval;
	char *dirpath = NULL, *imgfile = NULL, *oobfile = NULL;
	struct stat statbuf;
	
	int option, option_index;
	static const char *short_options = "hvep:s:o:";
	static const struct option long_options[] = {
		{"pagesize", 	required_argument, 	0, 'p'},
		{"sparesize", 	required_argument, 	0, 's'},
		{"oobimg",	required_argument,	0, 'o'},
		{"endian", 	no_argument, 		0, 'e'},
		{"verbose", 	no_argument, 		0, 'v'},
		{"help", 	no_argument, 		0, 'h'},
	};

	MKYAFFS2_PRINT("mkyaffs2-%s: image building tool for YAFFS2\n",
		YAFFS2UTILS_VERSION);

	if (getuid() != 0) {
		mkyaffs2_flags |= MKYAFFS2_FLAGS_NONROOT;
		MKYAFFS2_WARN("warning: non-root users.\n");
		MKYAFFS2_WARN("suggest: executing this tool as root.\n");
	}

	mkyaffs2_chunksize = DEFAULT_CHUNKSIZE;

	while ((option = getopt_long(argc, argv, short_options,
				     long_options, &option_index)) != EOF) {
		switch (option) {
		case 'p':
			mkyaffs2_chunksize = strtoul(optarg, NULL, 10);
			break;
		case 's':
			mkyaffs2_sparesize = strtoul(optarg, NULL, 10);
			break;
		case 'o':
			oobfile = optarg;
			break;
		case 'e':
			mkyaffs2_flags |= MKYAFFS2_FLAGS_ENDIAN;
			break;
		case 'v':
			mkyaffs2_flags |= MKYAFFS2_FLAGS_VERBOSE;
			break;
		case 'h':
		default:
			return mkyaffs2_helper();
		}
	}

	if (argc - optind < 2)
		return mkyaffs2_helper();

	dirpath = argv[optind];
	imgfile = argv[optind + 1];

	/* veridate the page size */
	mkyaffs2_writechunk = &mkyaffs2_yaffs2_writechunk;
	switch (mkyaffs2_chunksize) {
	case 512:
		mkyaffs2_writechunk = &mkyaffs2_yaffs1_writechunk;
		if (oobfile == NULL)
			mkyaffs2_oobinfo = &nand_oob_16;
		mkyaffs2_flags |= MKYAFFS2_FLAGS_YAFFS1;
		break;
	case 2048:
		if (oobfile == NULL)
			mkyaffs2_oobinfo = &nand_oob_64;
		break;
	case 4096:
	case 8192:
	case 16384:
		/* FIXME: The OOB scheme for 8192 and 16384 bytes */
		if (oobfile == NULL)
			mkyaffs2_oobinfo = &nand_oob_128;
		break;
	default:
		MKYAFFS2_ERROR("%u bytes page size is NOT supported\n",
				mkyaffs2_chunksize);
		return -1;
	}

	/* spare size */
	if (!mkyaffs2_sparesize)
		mkyaffs2_sparesize = mkyaffs2_chunksize / 32;

	if (mkyaffs2_sparesize > mkyaffs2_chunksize) {
		MKYAFFS2_ERROR("spare size is too large (%u)\n",
				mkyaffs2_sparesize);
		return -1;
	}

	/* verify spare image if it is existed */
	if (oobfile) {
		if (mkyaffs2_load_spare(oobfile) < 0) {
			MKYAFFS2_ERROR("parse oob image failed\n");
			return -1;
		}
		mkyaffs2_oobinfo = &nand_oob_user;
		/* FIXME: verify for the various ecc layout */
	}

	/* verify whether the input directory is valid */
	if (strlen(dirpath) >= PATH_MAX || strlen(imgfile) >= PATH_MAX) {
		MKYAFFS2_ERROR("directory or image path is too long \n");
		MKYAFFS2_ERROR("(max: %u characters)\n", PATH_MAX - 1);
		return -1;
	}

	if (stat(dirpath, &statbuf) < 0 && !S_ISDIR(statbuf.st_mode)) {
		MKYAFFS2_ERROR("ROOT is not a directory '%s'\n", dirpath);
		return -1;
	}

	retval = mkyaffs2_create_image(dirpath, imgfile);
	if (!retval) {
		MKYAFFS2_PRINT("%coperation complete.\n",
			MKYAFFS2_ISVERBOSE ? '\0' : '\n');
		MKYAFFS2_PRINT("%u objects in %u NAND pages\n", 
			mkyaffs2_image_objs, mkyaffs2_image_pages);
	}
	else {
		MKYAFFS2_ERROR("\noperation incomplete!\n");
		MKYAFFS2_ERROR("image may be broken!!!\n");
	}

	return retval;
}
