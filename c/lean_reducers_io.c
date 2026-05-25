#include <lean/lean.h>

#include <errno.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__APPLE__) && defined(__MACH__)
#include <libproc.h>
#include <mach/mach.h>
#include <mach/mach_host.h>
#include <mach/processor_info.h>
#include <sys/resource.h>
#endif

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

#define LEAN_REDUCERS_UNKNOWN_U64 UINT64_MAX

static int lean_reducers_append_sample_field(char * out, size_t cap, size_t * used, uint64_t value) {
    int written;
    if (value == LEAN_REDUCERS_UNKNOWN_U64) {
        written = snprintf(out + *used, cap - *used, *used == 0 ? "-" : " -");
    } else {
        written = snprintf(out + *used, cap - *used, *used == 0 ? "%" PRIu64 : " %" PRIu64, value);
    }
    if (written < 0 || (size_t)written >= cap - *used) {
        return -1;
    }
    *used += (size_t)written;
    return 0;
}

static lean_obj_res lean_reducers_process_sample_ok(uint64_t rss_kb, uint64_t read_bytes, uint64_t write_bytes) {
    char out[128];
    size_t used = 0;
    out[0] = '\0';
    if (lean_reducers_append_sample_field(out, sizeof(out), &used, rss_kb) != 0 ||
        lean_reducers_append_sample_field(out, sizeof(out), &used, read_bytes) != 0 ||
        lean_reducers_append_sample_field(out, sizeof(out), &used, write_bytes) != 0) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("process sample buffer was too small")));
    }
    return lean_io_result_mk_ok(lean_mk_string(out));
}

static lean_obj_res lean_reducers_cpu_percentages_ok(unsigned int const * percentages, size_t count) {
    if (count == 0) {
        return lean_io_result_mk_ok(lean_mk_string(""));
    }

    size_t cap = count * 8 + 1;
    char * out = (char *)malloc(cap);
    if (out == NULL) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("could not allocate CPU sample buffer")));
    }

    size_t used = 0;
    out[0] = '\0';
    for (size_t i = 0; i < count; i++) {
        int written = snprintf(out + used, cap - used, i == 0 ? "%u" : " %u", percentages[i]);
        if (written < 0 || (size_t)written >= cap - used) {
            free(out);
            return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("CPU sample buffer was too small")));
        }
        used += (size_t)written;
    }

    lean_object * result = lean_mk_string(out);
    free(out);
    return lean_io_result_mk_ok(result);
}

#if defined(__APPLE__) && defined(__MACH__)
static processor_cpu_load_info_data_t * lean_reducers_prev_cpu_load = NULL;
static natural_t lean_reducers_prev_cpu_count = 0;

LEAN_EXPORT lean_obj_res lean_reducers_cpu_percentages(void) {
    processor_cpu_load_info_t cpu_load = NULL;
    mach_msg_type_number_t msg_count = 0;
    natural_t cpu_count = 0;
    kern_return_t kr = host_processor_info(
        mach_host_self(),
        PROCESSOR_CPU_LOAD_INFO,
        &cpu_count,
        (processor_info_array_t *)&cpu_load,
        &msg_count);

    if (kr != KERN_SUCCESS || cpu_load == NULL || cpu_count == 0) {
        return lean_io_result_mk_ok(lean_mk_string(""));
    }

    unsigned int * percentages = (unsigned int *)calloc(cpu_count, sizeof(unsigned int));
    if (percentages == NULL) {
        vm_deallocate(mach_task_self(), (vm_address_t)cpu_load, msg_count * sizeof(integer_t));
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("could not allocate CPU percentages")));
    }

    int have_prev = lean_reducers_prev_cpu_load != NULL && lean_reducers_prev_cpu_count == cpu_count;
    for (natural_t i = 0; i < cpu_count; i++) {
        uint64_t user = (uint64_t)cpu_load[i].cpu_ticks[CPU_STATE_USER];
        uint64_t system = (uint64_t)cpu_load[i].cpu_ticks[CPU_STATE_SYSTEM];
        uint64_t idle = (uint64_t)cpu_load[i].cpu_ticks[CPU_STATE_IDLE];
        uint64_t nice = (uint64_t)cpu_load[i].cpu_ticks[CPU_STATE_NICE];
        uint64_t total = user + system + idle + nice;

        if (have_prev) {
            uint64_t prev_user = (uint64_t)lean_reducers_prev_cpu_load[i].cpu_ticks[CPU_STATE_USER];
            uint64_t prev_system = (uint64_t)lean_reducers_prev_cpu_load[i].cpu_ticks[CPU_STATE_SYSTEM];
            uint64_t prev_idle = (uint64_t)lean_reducers_prev_cpu_load[i].cpu_ticks[CPU_STATE_IDLE];
            uint64_t prev_nice = (uint64_t)lean_reducers_prev_cpu_load[i].cpu_ticks[CPU_STATE_NICE];
            uint64_t prev_total = prev_user + prev_system + prev_idle + prev_nice;
            uint64_t total_delta = total >= prev_total ? total - prev_total : 0;
            uint64_t idle_delta = idle >= prev_idle ? idle - prev_idle : 0;
            uint64_t busy_delta = total_delta >= idle_delta ? total_delta - idle_delta : 0;
            if (total_delta > 0) {
                percentages[i] = (unsigned int)((busy_delta * 100 + total_delta / 2) / total_delta);
                if (percentages[i] > 100) {
                    percentages[i] = 100;
                }
            }
        }
    }

    processor_cpu_load_info_data_t * next =
        (processor_cpu_load_info_data_t *)malloc(cpu_count * sizeof(processor_cpu_load_info_data_t));
    if (next == NULL) {
        free(percentages);
        vm_deallocate(mach_task_self(), (vm_address_t)cpu_load, msg_count * sizeof(integer_t));
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("could not allocate previous CPU sample")));
    }
    memcpy(next, cpu_load, cpu_count * sizeof(processor_cpu_load_info_data_t));
    free(lean_reducers_prev_cpu_load);
    lean_reducers_prev_cpu_load = next;
    lean_reducers_prev_cpu_count = cpu_count;

    vm_deallocate(mach_task_self(), (vm_address_t)cpu_load, msg_count * sizeof(integer_t));
    lean_obj_res result = lean_reducers_cpu_percentages_ok(percentages, cpu_count);
    free(percentages);
    return result;
}
#elif defined(__linux__)
typedef struct {
    uint64_t total;
    uint64_t idle;
} lean_reducers_cpu_sample;

static lean_reducers_cpu_sample * lean_reducers_prev_cpu_samples = NULL;
static size_t lean_reducers_prev_cpu_count = 0;

static int lean_reducers_read_linux_cpu_samples(lean_reducers_cpu_sample ** samples_out, size_t * count_out) {
    FILE * file = fopen("/proc/stat", "r");
    if (file == NULL) {
        return -1;
    }

    lean_reducers_cpu_sample * samples = NULL;
    size_t count = 0;
    char * line = NULL;
    size_t line_cap = 0;

    while (getline(&line, &line_cap, file) != -1) {
        if (strncmp(line, "cpu", 3) != 0 || !isdigit((unsigned char)line[3])) {
            continue;
        }

        char name[32];
        unsigned long long user = 0;
        unsigned long long nice = 0;
        unsigned long long system = 0;
        unsigned long long idle = 0;
        unsigned long long iowait = 0;
        unsigned long long irq = 0;
        unsigned long long softirq = 0;
        unsigned long long steal = 0;
        unsigned long long guest = 0;
        unsigned long long guest_nice = 0;
        int scanned = sscanf(
            line,
            "%31s %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu",
            name,
            &user,
            &nice,
            &system,
            &idle,
            &iowait,
            &irq,
            &softirq,
            &steal,
            &guest,
            &guest_nice);
        if (scanned < 5) {
            continue;
        }

        lean_reducers_cpu_sample sample;
        sample.idle = (uint64_t)idle + (uint64_t)iowait;
        sample.total =
            (uint64_t)user +
            (uint64_t)nice +
            (uint64_t)system +
            (uint64_t)idle +
            (uint64_t)iowait +
            (uint64_t)irq +
            (uint64_t)softirq +
            (uint64_t)steal +
            (uint64_t)guest +
            (uint64_t)guest_nice;

        lean_reducers_cpu_sample * grown =
            (lean_reducers_cpu_sample *)realloc(samples, (count + 1) * sizeof(lean_reducers_cpu_sample));
        if (grown == NULL) {
            free(samples);
            free(line);
            fclose(file);
            return -1;
        }
        samples = grown;
        samples[count] = sample;
        count++;
    }

    free(line);
    fclose(file);
    *samples_out = samples;
    *count_out = count;
    return 0;
}

LEAN_EXPORT lean_obj_res lean_reducers_cpu_percentages(void) {
    lean_reducers_cpu_sample * samples = NULL;
    size_t count = 0;
    if (lean_reducers_read_linux_cpu_samples(&samples, &count) != 0 || count == 0) {
        free(samples);
        return lean_io_result_mk_ok(lean_mk_string(""));
    }

    unsigned int * percentages = (unsigned int *)calloc(count, sizeof(unsigned int));
    if (percentages == NULL) {
        free(samples);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("could not allocate CPU percentages")));
    }

    int have_prev = lean_reducers_prev_cpu_samples != NULL && lean_reducers_prev_cpu_count == count;
    for (size_t i = 0; i < count; i++) {
        if (have_prev) {
            uint64_t total_delta =
                samples[i].total >= lean_reducers_prev_cpu_samples[i].total
                    ? samples[i].total - lean_reducers_prev_cpu_samples[i].total
                    : 0;
            uint64_t idle_delta =
                samples[i].idle >= lean_reducers_prev_cpu_samples[i].idle
                    ? samples[i].idle - lean_reducers_prev_cpu_samples[i].idle
                    : 0;
            uint64_t busy_delta = total_delta >= idle_delta ? total_delta - idle_delta : 0;
            if (total_delta > 0) {
                percentages[i] = (unsigned int)((busy_delta * 100 + total_delta / 2) / total_delta);
                if (percentages[i] > 100) {
                    percentages[i] = 100;
                }
            }
        }
    }

    free(lean_reducers_prev_cpu_samples);
    lean_reducers_prev_cpu_samples = samples;
    lean_reducers_prev_cpu_count = count;

    lean_obj_res result = lean_reducers_cpu_percentages_ok(percentages, count);
    free(percentages);
    return result;
}
#else
LEAN_EXPORT lean_obj_res lean_reducers_cpu_percentages(void) {
    return lean_io_result_mk_ok(lean_mk_string(""));
}
#endif

#if defined(__APPLE__) && defined(__MACH__)
LEAN_EXPORT lean_obj_res lean_reducers_process_sample(void) {
    uint64_t rss_kb = LEAN_REDUCERS_UNKNOWN_U64;
    uint64_t read_bytes = LEAN_REDUCERS_UNKNOWN_U64;
    uint64_t write_bytes = LEAN_REDUCERS_UNKNOWN_U64;

    struct rusage_info_v4 rusage;
    memset(&rusage, 0, sizeof(rusage));
    if (proc_pid_rusage(getpid(), RUSAGE_INFO_V4, (rusage_info_t *)&rusage) == 0) {
        if (rusage.ri_resident_size > 0) {
            rss_kb = rusage.ri_resident_size / 1024;
        } else if (rusage.ri_phys_footprint > 0) {
            rss_kb = rusage.ri_phys_footprint / 1024;
        }
        read_bytes = rusage.ri_diskio_bytesread;
        write_bytes = rusage.ri_diskio_byteswritten;
    }

    return lean_reducers_process_sample_ok(rss_kb, read_bytes, write_bytes);
}
#elif defined(__linux__)
static uint64_t lean_reducers_linux_rss_kb(void) {
    FILE * file = fopen("/proc/self/status", "r");
    if (file == NULL) {
        return LEAN_REDUCERS_UNKNOWN_U64;
    }

    char line[256];
    uint64_t rss_kb = LEAN_REDUCERS_UNKNOWN_U64;
    while (fgets(line, sizeof(line), file) != NULL) {
        unsigned long long value = 0;
        if (sscanf(line, "VmRSS: %llu kB", &value) == 1) {
            rss_kb = (uint64_t)value;
            break;
        }
    }

    fclose(file);
    return rss_kb;
}

static void lean_reducers_linux_io_bytes(uint64_t * read_bytes, uint64_t * write_bytes) {
    *read_bytes = LEAN_REDUCERS_UNKNOWN_U64;
    *write_bytes = LEAN_REDUCERS_UNKNOWN_U64;

    FILE * file = fopen("/proc/self/io", "r");
    if (file == NULL) {
        return;
    }

    char line[256];
    while (fgets(line, sizeof(line), file) != NULL) {
        char key[64];
        unsigned long long value = 0;
        if (sscanf(line, "%63[^:]: %llu", key, &value) != 2) {
            continue;
        }
        if (strcmp(key, "rchar") == 0) {
            *read_bytes = (uint64_t)value;
        } else if (strcmp(key, "wchar") == 0) {
            *write_bytes = (uint64_t)value;
        }
    }

    fclose(file);
}

LEAN_EXPORT lean_obj_res lean_reducers_process_sample(void) {
    uint64_t rss_kb = lean_reducers_linux_rss_kb();
    uint64_t read_bytes = LEAN_REDUCERS_UNKNOWN_U64;
    uint64_t write_bytes = LEAN_REDUCERS_UNKNOWN_U64;
    lean_reducers_linux_io_bytes(&read_bytes, &write_bytes);
    return lean_reducers_process_sample_ok(rss_kb, read_bytes, write_bytes);
}
#else
LEAN_EXPORT lean_obj_res lean_reducers_process_sample(void) {
    return lean_io_result_mk_ok(lean_mk_string(""));
}
#endif

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
