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

#ifndef _YAFFS2UTILS_MTD_H_
#define _YAFFS2UTILS_MTD_H_

#define MTD_MAX_OOBFREE_ENTRIES	8

struct nand_oobfree {
	unsigned offset;
	unsigned length;
};

struct nand_ecclayout_user {
	unsigned eccbytes;
	unsigned eccpos[64];
	unsigned oobavail;
	struct nand_oobfree oobfree[MTD_MAX_OOBFREE_ENTRIES];
};

#define ECCGETLAYOUT		_IOR('M', 17, struct nand_ecclayout_user)

typedef struct nand_ecclayout_user nand_ecclayout_t;

#endif
