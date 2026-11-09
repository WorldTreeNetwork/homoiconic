#include <lean/lean.h>

/* Keep Lean object layout and reference counting behind its C API. */
uint8_t kernel_finish_initialization(lean_obj_arg result) {
    if (!lean_io_result_is_ok(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        return 0;
    }
    lean_dec(result);
    lean_io_mark_end_initialization();
    return 1;
}
