/**
 * @file
 * Type representing an email address
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

#ifndef _CONFIG_ADDRESS_H
#define _CONFIG_ADDRESS_H

#include <stdbool.h>

struct ConfigSet;

/**
 * struct Address - An email address
 */
struct Address
{
  char *personal;        /**< Real name of address */
  char *mailbox;         /**< Mailbox and host address */
  int group;             /**< Group mailbox? */
  struct Address *next;  /**< Next item in the list */
  bool is_intl : 1;      /**< Is this an IDN (Internationalised Domain Name) */
  bool intl_checked : 1; /**< Has the IDN status been checked? */
};

void address_init(struct ConfigSet *cs);
struct Address *address_create(const char *addr);
void address_free(struct Address **addr);

#endif /* _CONFIG_ADDRESS_H */
