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

/* Copy a rendering into the caller's buffer when it fits. Always report how
   many bytes the rendering has, so the caller can retry with more room. */
size_t reflect_store_bytes(size_t out, size_t capacity, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    if (size <= capacity) {
        const uint8_t *source = lean_sarray_cptr(bytes);
        uint8_t *target = (uint8_t *)out;
        for (size_t i = 0; i < size; ++i) {
            target[i] = source[i];
        }
    }
    return size;
}

/* Every exported function that takes a Lean value uses it up. A caller that
   will pass the same value again keeps it with this first. */
void kernel_retain(lean_object *value) {
    lean_inc(value);
}
