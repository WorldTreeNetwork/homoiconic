# unikernel-image

## MODIFIED Requirements

### Requirement: One image boots under Cloud Hypervisor with no operating system
<!-- base: 942ec71444252ba6e8a211aac95f019142bfb5a6 openspec/specs/unikernel-image/spec.md -->

The build SHALL produce one static x86_64 ELF file that Cloud Hypervisor starts by direct kernel boot through the PVH entry, with no firmware, no file system and no operating system in the guest. Bytes handed to the image at boot with `--initramfs` are one program's byte form, not a file system. The image SHALL hold the same compiled Lean objects as its Linux comparison process. Lean SHALL own reading, compilation, evaluation and rendering. Non-Lean image code SHALL NOT implement a language reader or evaluator.

#### Scenario: The factorial program

- GIVEN an image built from `examples/factorial.hom`
- WHEN Cloud Hypervisor boots it with one processor and 512 MiB
- THEN the serial port shows `265252859812191058636308480000000`, the machine powers off, and Cloud Hypervisor exits with status 0

### Requirement: The image runs its program through the kernel and writes the kernel's text
<!-- base: 942ec71444252ba6e8a211aac95f019142bfb5a6 openspec/specs/unikernel-image/spec.md -->

On boot an image given no bytes SHALL pass the program source built into it, and the step budget built into it, to `reflect_run`; an image given bytes SHALL run them as the requirement "One image runs a byte form given at boot" says. In both cases it SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. A syntax error, an error outcome, a run that does not finish in its budget, and a value are all text the kernel wrote, and all of them SHALL end with `reflect: exit 0`.

#### Scenario: A program that does not finish

- GIVEN an image built from `examples/forever.hom` with a budget of 5000
- WHEN it boots
- THEN the serial port shows `no result within 5000 steps` and then `reflect: exit 0`

#### Scenario: A program that is not syntax

- GIVEN an image built from a file the reader refuses
- WHEN it boots
- THEN the serial port shows the reader's error text, the same text `unikernel/out/reflect-linux` prints for that file, and then `reflect: exit 0`

### Requirement: Successful reproducible Linux build
<!-- base: 942ec71444252ba6e8a211aac95f019142bfb5a6 openspec/specs/unikernel-image/spec.md -->

The build SHALL compile the pinned Lean-generated C on Linux x86_64 and link the same objects into the image and Linux comparison process. Missing, modified, stale or wrong-platform artifacts SHALL fail validation. A clean output build SHALL succeed with Lean 4.35.0, Zig 0.16.0/musl 1.2.5 and Cloud Hypervisor 54.0 without requiring host/check.sh.

#### Scenario: Clean provenance

- GIVEN no unikernel output directory
- WHEN the check builds and boots factorial
- THEN it records toolchain versions, source provenance and object hashes, compares the complete serial stream to the Linux process and rejects changed inputs or objects on reuse

#### Scenario: Lean owns semantics

- GIVEN the image sources and linked objects
- WHEN their call paths and symbol references are inspected
- THEN non-Lean code only initializes, passes bytes and supplies runtime services; main calls reflect_run and reflect_interp and no other export that evaluates or reads, and the identical Lean objects occur in both links

## ADDED Requirements

### Requirement: One image runs a byte form given at boot

When Cloud Hypervisor is started with `--initramfs <file>`, the image SHALL treat that file's bytes as one program's byte form (`wire-bytes`). It SHALL pass exactly those bytes to `reflect_interp` with the byte-form flag set and the text flag clear, SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. The PVH command line SHALL be `[step-budget [levels]]`: the budget SHALL default to the one built into the image and the levels to 1; level 0 runs the program itself and level k runs it through k interpreters. The program built into the image SHALL NOT run when bytes are given. One image file SHALL serve any number of different byte forms, one per boot, without being built again.

The layer SHALL move the bytes out of the memory the stack and the allocators will use before it lays those out, SHALL NOT hand that memory out while the bytes are still read from it, and SHALL NOT read or change the bytes. Non-Lean code SHALL NOT decide whether the bytes are a program: bytes the kernel refuses SHALL end in the kernel's text and `reflect: exit 0`. More than 16 MiB of bytes, or more than one boot module, SHALL stop the image with a line saying so before the C library starts. A budget or a level count that is not a whole number SHALL end in a line saying so and `reflect: exit 2`. The Linux comparison process SHALL take the same file and the same words, `reflect-linux <bytes-file> [step-budget [levels]]`, and call the same export.

#### Scenario: Two programs, one image

- GIVEN one image file, built once, and the byte forms of `examples/factorial.hom` and of a program whose answer is a text
- WHEN Cloud Hypervisor boots that file once with each byte form given at boot
- THEN each serial stream is byte for byte what the Linux process prints for the same bytes followed by `reflect: exit 0`, the factorial stream shows `265252859812191058636308480000000`, and the image file's hash is unchanged between the boots

#### Scenario: Levels and budget come from the command line

- GIVEN the factorial byte form and the byte form of `examples/forever.hom`
- WHEN the image boots with factorial and command lines naming 0, 1 and 2 levels, and with forever and the command line `5000`
- THEN factorial's answer is the same at every level, and forever shows `no result within 5000 steps`

#### Scenario: Bytes that are no program, and too many bytes

- GIVEN a megabyte of bytes that is no program, a program's byte form with one byte added, and a file of 16 MiB and one byte
- WHEN the image boots with each
- THEN the first two end in the text the Linux process prints for them and `reflect: exit 0`, and the third shows only `reflect: the program given at boot is too large`

#### Scenario: Nothing given

- GIVEN the same image file
- WHEN it boots with no bytes given
- THEN it runs the program built into it, as before
