/**
 * @file
 * Definitions of NeoMutt Configuration
 *
 * @authors
 * Copyright (C) 2016 Bernard Pratz <z+mutt+pub@m0g.net>
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

#ifndef _MUTT_OPTIONS_H
#define _MUTT_OPTIONS_H

#include <stddef.h>
#include <stdbool.h>
#include "config/set.h"

struct Buffer;

/**
 * struct Option - Definition of a user-variable
 */
struct Option
{
  const char  *name;      /**< user-visible name */
  unsigned int type;      /**< variable type, e.g. *DT_STRING */
  short        flags;     /**< notification flags, e.g. R_PAGER */
  intptr_t     var;       /**< pointer to the global variable */
  intptr_t     initial;   /**< initial value */
  cs_validator validator; /**< validator callback function */
};

int mutt_option_to_string(const struct Option *opt, char *val, size_t len);

bool mutt_option_get(const char *s, struct Option *opt);
int mutt_option_set(const struct Option *val, struct Buffer *err);

#endif /* _MUTT_OPTIONS_H */
