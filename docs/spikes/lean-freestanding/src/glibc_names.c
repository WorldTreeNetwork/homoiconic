/* The Lean toolchain's libraries were compiled against glibc. These are the
   glibc-only names they use, in terms of standard ones, so the image can link
   against musl. The checked variants drop their extra size or flag argument. */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>

int __fprintf_chk(FILE *f, int flag, const char *fmt, ...) {
    (void)flag;
    va_list ap;
    va_start(ap, fmt);
    int r = vfprintf(f, fmt, ap);
    va_end(ap);
    return r;
}
int __snprintf_chk(char *s, size_t n, int flag, size_t size, const char *fmt, ...) {
    (void)flag; (void)size;
    va_list ap;
    va_start(ap, fmt);
    int r = vsnprintf(s, n, fmt, ap);
    va_end(ap);
    return r;
}
int __open_2(const char *path, int flags) { return open(path, flags); }
ssize_t __read_chk(int fd, void *buf, size_t n, size_t size) { (void)size; return read(fd, buf, n); }
ssize_t __pread_chk(int fd, void *buf, size_t n, off_t off, size_t size) { (void)size; return pread(fd, buf, n, off); }
char *__realpath_chk(const char *path, char *out, size_t size) { (void)size; return realpath(path, out); }
int backtrace(void **buffer, int size) { (void)buffer; (void)size; return 0; }
char **backtrace_symbols(void *const *buffer, int size) { (void)buffer; (void)size; return 0; }
const char *gnu_get_libc_version(void) { return "2.0"; }
