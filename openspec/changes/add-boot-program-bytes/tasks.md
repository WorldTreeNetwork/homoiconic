# Tasks

- [x] Layer: take one PVH boot module, bound it, move it above the image before the stack and allocators are laid out, clear where it was; serve it as `/boot/program`; pass the command line's words as arguments when it is present.
- [x] Program: `reflect <bytes-file> [step-budget [levels]]` calls `reflect_interp` with the byte-form flag; no words keeps `reflect_run` on the built-in source.
- [x] Build: link `out/reply` from the same objects for `reply source`.
- [x] Check on morphie (Cloud Hypervisor 54.0): one image, not rebuilt, runs text, factorial (levels 0, 1, 2), the quine and a 5000-step budget from bytes given at boot; refuses non-program bytes through the kernel, a non-number budget through the program, and more than 16 MiB in the layer; still runs its built-in program with nothing given. Whole serial stream against the Linux process each time.
- [x] `unikernel/check-net.sh` still passes on morphie. Both passed 2026-11-19; the image suite's log is `unikernel/evidence/check-boot-bytes.log`.
- [ ] Read by another model family (advise), then fold into `openspec/specs/unikernel-image/spec.md` and archive.
