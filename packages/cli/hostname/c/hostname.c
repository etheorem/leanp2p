#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res interop_participant_hostname(lean_obj_arg world) {
    (void)world;
    char name[256] = {0};
    if (gethostname(name, sizeof(name) - 1) != 0) {
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("gethostname failed")));
    }
    return lean_io_result_mk_ok(lean_mk_string(name));
}
