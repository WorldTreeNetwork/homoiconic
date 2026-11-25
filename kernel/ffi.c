#include <lean/lean.h>

/* The C library's, named here because the Lean toolchain's compiler comes
   without the library's headers. */
void *malloc(size_t size);
void *calloc(size_t count, size_t size);
void *realloc(void *block, size_t size);
void free(void *block);

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

/* Where `o` goes in a table of `slots`, a power of two. */
static size_t reflect_slot(lean_object *o, size_t slots) {
    return ((((size_t)o >> 3) * (size_t)0x9E3779B97F4A7C15ull) >> 20) & (slots - 1);
}

/* How many cells `root` holds, each object counted once however many times it
   is held. A constructor object is one cell, and the walk goes on through its
   fields. A number too large for a machine word is three cells and one more
   for each 64 bits, so that with the box around it it is `Reflect.natCells`.
   Any other object is one cell and is not looked inside; a machine state
   holds none. The walk stops once the count passes `cut` and answers
   `cut + 1`; it answers the same when it cannot get the memory to remember
   what it has counted, so a caller that compares the answer with `cut` errs
   toward "too many". `cut` is kept below a quarter of the largest size, so
   `cut + 1` is a size. Nothing is changed.

   The table of objects counted starts at 4096 slots of eight bytes and is
   made four times as large when it is three quarters full, up to the least
   power of two that is at least four thirds of `cut` and two, which it never
   fills past three quarters. So a count of a small state takes little, and
   the most a count takes is that last table and, for a moment, the one
   before it: ten bytes and two thirds for each cell of `cut`, rounded up to
   a power of two, and a quarter more. The stack holds what is still to look
   at, at most one entry for each cell counted. Objects are told apart by
   address: this is the one place the kernel package reads what the runtime
   shares, and so the one place whose answer is not a function of the value
   it is given. */
size_t reflect_live_cells(b_lean_obj_arg root, size_t cut) {
    if (cut >= ((size_t)-1) / 4) {
        cut = ((size_t)-1) / 4 - 1;
    }
    size_t most = 4096;
    while (most < cut + cut / 3 + 2) {
        most *= 2;
    }
    size_t slots = 4096, held = 0, count = 0;
    size_t room = 256, depth = 0;
    lean_object **table = calloc(slots, sizeof *table);
    lean_object **stack = malloc(room * sizeof *stack);
    if (table == NULL || stack == NULL) {
        free(table);
        free(stack);
        return cut + 1;
    }
    stack[depth++] = root;
    while (depth > 0 && count <= cut) {
        lean_object *o = stack[--depth];
        if (lean_is_scalar(o)) {
            continue;
        }
        size_t at = reflect_slot(o, slots);
        while (table[at] != NULL && table[at] != o) {
            at = (at + 1) & (slots - 1);
        }
        if (table[at] == o) {
            continue;
        }
        /* Every object counted adds at least one to `count`, so no more than
           `cut + 1` are ever held: three quarters of the largest table. */
        table[at] = o;
        held += 1;
        if (held * 4 > slots * 3 && slots < most) {
            size_t wider = slots * 4 > most ? most : slots * 4;
            lean_object **next = calloc(wider, sizeof *next);
            if (next == NULL) {
                count = cut + 1;
                break;
            }
            for (size_t i = 0; i < slots; ++i) {
                lean_object *p = table[i];
                if (p != NULL) {
                    size_t to = reflect_slot(p, wider);
                    while (next[to] != NULL) {
                        to = (to + 1) & (wider - 1);
                    }
                    next[to] = p;
                }
            }
            free(table);
            table = next;
            slots = wider;
        }
        unsigned tag = lean_ptr_tag(o);
        if (tag == LeanMPZ) {
            lean_object *bits = lean_nat_log2(o);
            count += lean_is_scalar(bits) ? 3 + lean_unbox(bits) / 64 : cut + 1;
            lean_dec(bits);
            continue;
        }
        count += 1;
        if (tag > LeanMaxCtorTag) {
            continue;
        }
        unsigned fields = lean_ctor_num_objs(o);
        if (depth + fields > room) {
            size_t more = room * 2 + fields;
            lean_object **grown = realloc(stack, more * sizeof *stack);
            if (grown == NULL) {
                count = cut + 1;
                break;
            }
            stack = grown;
            room = more;
        }
        /* The first field is looked at first, so a list's items are counted
           as it is walked and only its rest waits on the stack. */
        for (unsigned i = fields; i > 0; --i) {
            lean_object *field = lean_ctor_get(o, i - 1);
            if (!lean_is_scalar(field)) {
                stack[depth++] = field;
            }
        }
    }
    free(table);
    free(stack);
    return count > cut ? cut + 1 : count;
}
