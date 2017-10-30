/**
 * @file
 * Constants for all the config types
 *
 * @authors
 * Copyright (C) 2017 Richard Russon <rich@flatcap.org>
 *
 * @copyright
 * This program is free software: you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 2 of the License, or (at your option) any later
 * version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef _CONFIG_TYPES_H
#define _CONFIG_TYPES_H

/* Data Types */
#define DT_BOOL       1   /**< boolean option */
#define DT_NUMBER     2   /**< a number */
#define DT_STRING     3   /**< a string */
#define DT_PATH       4   /**< a pathname */
#define DT_QUAD       5   /**< quad-option (yes/no/ask-yes/ask-no) */
#define DT_SORT       6   /**< sorting methods */
#define DT_REGEX      7   /**< regular expressions */
#define DT_MAGIC      8   /**< mailbox type */
#define DT_SYNONYM    9   /**< synonym for another variable */
#define DT_ADDRESS   10   /**< e-mail address */
#define DT_MBTABLE   11   /**< multibyte char table */
#define DT_HCACHE    12   /**< header cache backend */

#define DTYPE(x) ((x) & 0x0f) /**< Mask for the Data Type */

/* subtypes for... */
#define DT_SUBTYPE_MASK 0xff0 /**< Mask for the Data Subtype */

/* Private config item flags */
#define DT_INHERITED    0x0200 /**< Config item is inherited */
#define DT_INITIAL_SET  0x0400 /**< Config item must have its initial value freed */
#define DT_DISABLED     0x0800 /**< Config item is disabled */
#define DT_MY_CONFIG    0x1000 /**< Config item is a "my_" variable */

/* forced redraw/resort types + other flags */
#define R_NONE        0        /**< No refresh/resort flags */
#define R_INDEX       (1 << 0) /**< redraw the index menu (MENU_MAIN) */
#define R_PAGER       (1 << 1) /**< redraw the pager menu */
#define R_PAGER_FLOW  (1 << 2) /**< reflow line_info and redraw the pager menu */
#define R_RESORT      (1 << 3) /**< resort the mailbox */
#define R_RESORT_SUB  (1 << 4) /**< resort subthreads */
#define R_RESORT_INIT (1 << 5) /**< resort from scratch */
#define R_TREE        (1 << 6) /**< redraw the thread tree */
#define R_REFLOW      (1 << 7) /**< reflow window layout and full redraw */
#define R_SIDEBAR     (1 << 8) /**< redraw the sidebar */
#define R_MENU        (1 << 9) /**< redraw all menus */
#define R_BOTH        (R_INDEX | R_PAGER)
#define R_RESORT_BOTH (R_RESORT | R_RESORT_SUB)

/* general flags, to be OR'd with the R_ flags above (so keep shifting..) */
#define F_SENSITIVE   (1 << 10) /**< Config item contains sensitive value */
#define IS_SENSITIVE(x) (((x).flags & F_SENSITIVE) == F_SENSITIVE)

#endif /* _CONFIG_TYPES_H */
