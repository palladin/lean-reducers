#include <lean/lean.h>

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#define LR_OPEN _open
#define LR_READ _read
#define LR_CLOSE _close
#define LR_SEEK _lseeki64
#define LR_O_RDONLY _O_RDONLY
#define LR_O_BINARY _O_BINARY
#else
#include <fcntl.h>
#include <unistd.h>
#define LR_OPEN open
#define LR_CLOSE close
#endif

static lean_obj_res lean_reducers_io_error(char const * context, char const * path, int err) {
    char msg[1024];
    snprintf(msg, sizeof(msg), "%s '%s': %s", context, path, strerror(err));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

LEAN_EXPORT lean_obj_res lean_reducers_pread(b_lean_obj_arg path, uint64_t offset, uint64_t count) {
    lean_object * path_string = lean_is_string(path) ? (lean_object *)path : lean_ctor_get(path, 0);
    char const * path_cstr = lean_string_cstr(path_string);

    if (count > SIZE_MAX) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("read size exceeds platform limit")));
    }

    size_t size = (size_t)count;
    lean_object * bytes = lean_alloc_sarray(1, 0, size);
    if (size == 0) {
        return lean_io_result_mk_ok(bytes);
    }

#ifdef _WIN32
    int fd = LR_OPEN(path_cstr, LR_O_RDONLY | LR_O_BINARY);
#else
    int fd = LR_OPEN(path_cstr, O_RDONLY);
#endif
    if (fd < 0) {
        lean_dec(bytes);
        return lean_reducers_io_error("could not open", path_cstr, errno);
    }

#ifdef _WIN32
    if (LR_SEEK(fd, (__int64)offset, SEEK_SET) < 0) {
        int err = errno;
        LR_CLOSE(fd);
        lean_dec(bytes);
        return lean_reducers_io_error("could not seek", path_cstr, err);
    }

    int nread = LR_READ(fd, lean_sarray_cptr(bytes), (unsigned int)size);
    if (nread < 0) {
        int err = errno;
        LR_CLOSE(fd);
        lean_dec(bytes);
        return lean_reducers_io_error("could not read", path_cstr, err);
    }
#else
    ssize_t nread = pread(fd, lean_sarray_cptr(bytes), size, (off_t)offset);
    if (nread < 0) {
        int err = errno;
        LR_CLOSE(fd);
        lean_dec(bytes);
        return lean_reducers_io_error("could not read", path_cstr, err);
    }
#endif

    if (LR_CLOSE(fd) < 0) {
        int err = errno;
        lean_dec(bytes);
        return lean_reducers_io_error("could not close", path_cstr, err);
    }

    lean_to_sarray(bytes)->m_size = (size_t)nread;
    return lean_io_result_mk_ok(bytes);
}
