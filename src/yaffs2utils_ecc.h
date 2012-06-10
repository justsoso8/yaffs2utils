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

#ifndef _YAFFS2UTILS_ECC_H_
#define _YAFFS2UTILS_ECC_H_

#ifndef _HAVE_BROKEN_MTD_H
 #include <mtd/mtd-user.h>
#else
 #include <yaffs2utils_mtd.h>
#endif

static nand_ecclayout_t nand_oob_16 = {
	.eccbytes	= 6,
	.eccpos		= {0, 1, 2, 3, 6, 7},
	.oobfree	= {{.offset = 8, .length = 8}},
};

static nand_ecclayout_t nand_oob_64 = {
	.eccbytes	= 24,
	.eccpos		= {40, 41, 42, 43, 44, 45, 46, 47,
			   48, 49, 50, 51, 52, 53, 54, 55,
			   56, 57, 58, 59, 60, 61, 62, 63},
#ifndef _HAVE_ANDROID
	.oobfree	= {{.offset = 2, .length = 38}},
#else
	.oobfree	= {{.offset = 0, .length = 38}},
#endif
};

static nand_ecclayout_t nand_oob_128 = {
	.eccbytes	= 48,
	.eccpos		= {
			   80, 81, 82, 83, 84, 85, 86, 87,
			   88, 89, 90, 91, 92, 93, 94, 95,
			   96, 97, 98, 99, 100, 101, 102, 103,
			   104, 105, 106, 107, 108, 109, 110, 111,
			   112, 113, 114, 115, 116, 117, 118, 119,
			   120, 121, 122, 123, 124, 125, 126, 127},
#ifndef _HAVE_ANDROID
	.oobfree	= {{.offset = 2, .length = 78}}
#else
	.oobfree	= {{.offset = 0, .length = 78}}
#endif
};

static nand_ecclayout_t nand_oob_user = {0};

#endif
