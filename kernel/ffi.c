#include <lean/lean.h>

/* Borrow the caller's bytes only long enough to make a Lean-owned copy. */
lean_obj_res kernel_copy_bytes(size_t address, size_t length) {
    lean_object *bytes = lean_alloc_sarray(1, length, length);
    const uint8_t *source = (const uint8_t *)address;
    uint8_t *target = lean_sarray_cptr(bytes);
    for (size_t i = 0; i < length; ++i) {
        target[i] = source[i];
    }
    return bytes;
}
