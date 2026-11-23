# Run a program given to the image at boot

> **ACTIVE BUILD**, 2026-11-19. The owner's orchestrator activated `homoiconic-q59.32` on 2026-11-19, after `homoiconic-q59.15` closed, with the goal and acceptance below. Not yet read by another model family.

**Rigor:** instrument (trusted, unproved image code; no kernel or semantics change). Bead: `homoiconic-q59.32`.

## Why

The image runs the one source built into it. A different program needs a different image: a build, a link and a new file. The kernel already has what removes that: a program has a byte form (`wire-bytes`), and `reflect_interp` runs a byte form through the interpreter (`zig-host`). The image only has to be handed the bytes.

## What

- Cloud Hypervisor's `--initramfs <file>` puts a file's bytes in guest memory and names them in the PVH start record as one boot module. The layer (`unikernel/kernel.zig`) moves those bytes to just above the image, before the stack and the allocators exist, and serves them as one read-only file, `/boot/program`. It does not read them.
- When bytes were given, the layer starts the program with the words `reflect /boot/program` followed by the words of the PVH command line. With nothing given the program starts with `reflect` alone, as before.
- The image program (`unikernel/main.zig`) with one to three words after its name reads the named file and calls `reflect_interp` with the byte-form flag: `reflect <bytes-file> [step-budget [levels]]`. The budget defaults to the one built in; the levels default to 1. With no words it calls `reflect_run` on the built-in source, as before. The same program is the Linux comparison process, so the comparison takes the same file and words.
- `unikernel/build.sh` also links `unikernel/out/reply`, the existing tool whose `reply source <file>` writes a source's byte form, from the same Lean objects.
- `unikernel/check.sh` builds one image and boots it with several byte forms without building it again, comparing each serial stream with the Linux process.

## Not in this change

- The network image (`add-unikernel-net`) is not edited: `netmain.zig` ignores its words, and bytes at boot are not offered to it.
- Source given at boot. Bytes only: the byte form is what crosses a boundary (vision D8).
- The text-output flag of `reflect_interp`, more than one boot module, a module larger than 16 MiB.
- QUIC, Mjolnir, network channels, log signing, operation costs.

## Impact

- Capability: MODIFIED and ADDED requirements in `unikernel-image`. No other living spec changes: `reflect_interp` is already an evaluating Lean export in `zig-host`.
- Trusted, unproved code grows by the module copy, one more file in the layer's `open`/`read`/`close`/`fstat`, and the argument words. `ARCHITECTURE.md` and `unikernel/README.md` are amended.
- No Lean file changes, so the image's Lean objects are the ones `add-unikernel-net` checked.
