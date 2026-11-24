# unikernel-image delta: the layer can hand the boot file over once

## ADDED Requirements

### Requirement: The layer hands the file given at boot over once

The layer SHALL export `reflect_boot_take(out, capacity)`. It SHALL return the length of the file given at boot, or 0 when none was given or it was taken before. When the length is no more than `capacity` it SHALL copy the bytes to `out`; in every case it SHALL then clear its own copy and forget the file, so that `/boot/program` does not open afterwards (`unikernel/kernel.zig`). The one-program image SHALL NOT call it, so the requirement "One image runs a byte form given at boot" holds of that image unchanged: there the layer does not read or change the bytes. The network image calls it for its entity key (`openspec/specs/unikernel-net/spec.md`).

#### Scenario: The one-program image does not name it

- GIVEN `unikernel/out/reflect.elf`
- WHEN `unikernel/check.sh` lists the kernel symbols the program names
- THEN `reflect_boot_take` is not among them, and the cases for a program given at boot pass as before
