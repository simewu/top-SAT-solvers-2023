#ifndef _file_h_INCLUDED
#define _file_h_INCLUDED

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

bool kissat_file_readable(const char *path);
bool kissat_file_writable(const char *path);
size_t kissat_file_size(const char *path);
bool kissat_find_executable(const char *name);

typedef struct file file;

struct file {
    FILE *file;
    bool close;
    bool reading;
    bool compressed;
    const char *path;
    uint64_t bytes;
    int cur_len;
    char * buf;
};

void kissat_read_already_open_file(file *, FILE *, const char *path);
void kissat_write_already_open_file(file *, FILE *, const char *path);

bool kissat_open_to_read_file(file *, const char *path);
bool kissat_open_to_write_file(file *, const char *path);

void kissat_close_file(file *);

static inline int kissat_getc(file *file)
{
    assert(file);
    assert(file->file);
    assert(file->reading);
#ifdef _POSIX_C_SOURCE
    int res = getc_unlocked(file->file);
#else
    int res = getc(file->file);
#endif
    if (res != EOF)
        file->bytes++;
    return res;
}
static inline void file_flush_buffer(file * file) {
    fwrite(file->buf, sizeof(char), file->cur_len, file->file);
    file->cur_len = 0;
}
static inline void unchecked_putc(file *file, char ch)
{
    //return;//don't write to file when testing
    file->buf[file->cur_len++] = ch;
    if(file->cur_len == 1048576) {
        file_flush_buffer(file);
    }
//#ifdef _POSIX_C_SOURCE
//    return putc_unlocked(ch, file->file);
//#else
//    return putc(ch, file->file);
//#endif
}
static inline void kissat_putc(file *file, int ch)
{
    assert(file);
    assert(file->file);
    assert(!file->reading);
    unchecked_putc(file, ch);
}

static inline void kissat_puts(file *file, char *st)
{
    assert(file);
    assert(file->file);
    assert(!file->reading);
    for (char *p = st; *p; p++) {
        unchecked_putc(file, *p);
    }
}

static inline void kissat_putint(file *file, long long x)
{
    assert(file);
    assert(file->file);
    assert(!file->reading);
    if (x < 0) {
        unchecked_putc(file, '-');
        x = -x;
    }
    if (x == 0) {
        unchecked_putc(file, '0');
    }
    char buf[23];
    int len = 0;
    while (x) {
        buf[len++] = x % 10 + '0';
        x /= 10;
    }
    for (int i = len - 1; i >= 0; i--) {
        unchecked_putc(file, buf[i]);
    }
}

#endif
