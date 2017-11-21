/**
 * @file
 * General purpose object for storing and parsing strings
 *
 * @authors
 * Copyright (C) 2017 Ian Zimmerman <itz@primate.net>
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

/**
 * @page buffer General purpose object for storing and parsing strings
 *
 * The Buffer object make parsing and manipulating strings easier.
 *
 * | Function               | Description
 * | :--------------------- | :--------------------------------------------------
 * | mutt_buffer_add()      | Add a string to a Buffer, expanding it if necessary
 * | mutt_buffer_addch()    | Add a single character to a Buffer
 * | mutt_buffer_addstr()   | Add a string to a Buffer
 * | mutt_buffer_alloc()    | Create a new Buffer
 * | mutt_buffer_deinit()   | Release the memory allocated by a Buffer
 * | mutt_buffer_from()     | Initialize a Buffer from an existing string
 * | mutt_buffer_init()     | Initialise a new Buffer
 * | mutt_buffer_is_empty() | Is the Buffer empty?
 * | mutt_buffer_printf()   | Format a string into a Buffer
 * | mutt_buffer_reset()    | Reset an existing Buffer
 */

#include "config.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include "buffer.h"
#include "memory.h"
#include "string2.h"

/**
 * mutt_buffer_init - Initialise a new Buffer
 * @param b Buffer to initialise
 *
 * This must not be called on a Buffer that already contains data.
 */
void mutt_buffer_init(struct Buffer *b)
{
  if (!b)
    return;
  memset(b, 0, sizeof(struct Buffer));
}

/**
 * mutt_buffer_deinit - Release the memory allocated by a Buffer
 * @param b Buffer to release
 */
void mutt_buffer_deinit(struct Buffer *b)
{
  FREE(&b->data);
}

/**
 * mutt_buffer_reset - Reset an existing Buffer
 * @param b Buffer to reset
 *
 * This can be called on a Buffer to reset the pointers,
 * effectively emptying it.
 */
void mutt_buffer_reset(struct Buffer *b)
{
  if (!b)
    return;
  memset(b->data, 0, b->dsize);
  b->dptr = b->data;
}

/**
 * mutt_buffer_from - Initialize a Buffer from an existing string
 * @param buf Buffer to initialize
 * @param seed String to put in the Buffer
 */
void mutt_buffer_from(struct Buffer *buf, char *seed)
{
  if (!seed)
    return;

  mutt_buffer_init(buf);
  buf->data = mutt_str_strdup(seed);
  buf->dsize = mutt_str_strlen(seed);
  buf->dptr = (char *) buf->data + buf->dsize;
}

/**
 * mutt_buffer_add - Add a string to a Buffer, expanding it if necessary
 * @param buf Buffer to add to
 * @param s   String to add
 * @param len Length of the string
 * @retval num Bytes written to Buffer
 *
 * Dynamically grow a Buffer to accommodate s, in increments of 128 bytes.
 * Always one byte bigger than necessary for the null terminator, and the
 * buffer is always NUL-terminated
 */
size_t mutt_buffer_add(struct Buffer *buf, const char *s, size_t len)
{
  if (!buf || !s)
    return 0;

  if ((buf->dptr + len + 1) > (buf->data + buf->dsize))
  {
    size_t offset = buf->dptr - buf->data;
    buf->dsize += (len < 128) ? 128 : len + 1;
    mutt_mem_realloc(&buf->data, buf->dsize);
    buf->dptr = buf->data + offset;
  }
  if (!buf->dptr)
    return 0;
  memcpy(buf->dptr, s, len);
  buf->dptr += len;
  *(buf->dptr) = '\0';
  return len;
}

/**
 * mutt_buffer_printf - Format a string into a Buffer
 * @param buf Buffer
 * @param fmt printf-style format string
 * @param ... Arguments to be formatted
 * @retval num Characters written
 */
int mutt_buffer_printf(struct Buffer *buf, const char *fmt, ...)
{
  if (!buf)
    return 0;

  va_list ap, ap_retry;
  int len, blen, doff;

  va_start(ap, fmt);
  va_copy(ap_retry, ap);

  if (!buf->dptr)
    buf->dptr = buf->data;

  doff = buf->dptr - buf->data;
  blen = buf->dsize - doff;
  /* solaris 9 vsnprintf barfs when blen is 0 */
  if (!blen)
  {
    blen = 128;
    buf->dsize += blen;
    mutt_mem_realloc(&buf->data, buf->dsize);
    buf->dptr = buf->data + doff;
  }
  len = vsnprintf(buf->dptr, blen, fmt, ap);
  if (len >= blen)
  {
    blen = ++len - blen;
    if (blen < 128)
      blen = 128;
    buf->dsize += blen;
    mutt_mem_realloc(&buf->data, buf->dsize);
    buf->dptr = buf->data + doff;
    len = vsnprintf(buf->dptr, len, fmt, ap_retry);
  }
  if (len > 0)
    buf->dptr += len;

  va_end(ap);
  va_end(ap_retry);

  return len;
}

/**
 * mutt_buffer_addstr - Add a string to a Buffer
 * @param buf Buffer to add to
 * @param s   String to add
 * @retval num Bytes written to Buffer
 *
 * If necessary, the Buffer will be expanded.
 */
size_t mutt_buffer_addstr(struct Buffer *buf, const char *s)
{
  if (!buf || !s)
    return 0;
  return mutt_buffer_add(buf, s, mutt_str_strlen(s));
}

/**
 * mutt_buffer_addch - Add a single character to a Buffer
 * @param buf Buffer to add to
 * @param c   Character to add
 * @retval num Bytes written to Buffer
 *
 * If necessary, the Buffer will be expanded.
 */
size_t mutt_buffer_addch(struct Buffer *buf, char c)
{
  if (!buf)
    return 0;
  return mutt_buffer_add(buf, &c, 1);
}

/**
 * mutt_buffer_is_empty - Is the Buffer empty?
 * @param buf Buffer to inspect
 * @retval bool True, if Buffer is empty
 */
bool mutt_buffer_is_empty(const struct Buffer *buf)
{
  if (!buf)
    return true;

  return (buf->data && (buf->data[0] == '\0'));
}

/**
 * mutt_buffer_alloc - Create a new Buffer
 * @param size Size of Buffer to create
 * @retval ptr Newly allocated Buffer
 */
struct Buffer *mutt_buffer_alloc(size_t size)
{
  struct Buffer *b = mutt_mem_calloc(1, sizeof(struct Buffer));

  b->data = mutt_mem_calloc(1, size);
  b->dptr = b->data;
  b->dsize = size;

  return b;
}
