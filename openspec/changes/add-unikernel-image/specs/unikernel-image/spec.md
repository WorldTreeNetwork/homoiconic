# unikernel-image

## ADDED Requirements

### Requirement: One image boots under Cloud Hypervisor with no operating system

The build SHALL produce one static x86_64 ELF file that Cloud Hypervisor starts by direct kernel boot through the PVH entry, with no firmware, no initial file system and no operating system in the guest. The image SHALL hold the compiled Lean objects the host links, and SHALL NOT hold a second evaluator or a reader.

#### Scenario: The factorial program

- GIVEN an image built from `examples/factorial.hom`
- WHEN Cloud Hypervisor boots it with one processor and 512 MiB
- THEN the serial port shows `265252859812191058636308480000000`, the machine powers off, and Cloud Hypervisor exits with status 0

### Requirement: The image runs its program through the kernel and writes the kernel's text

On boot the image SHALL pass the program source built into it, and the step budget built into it, to `reflect_run`, SHALL write the text that comes back to the serial port followed by a line end, and SHALL power the machine off. A syntax error, an error outcome, a run that does not finish in its budget, and a value are all text the kernel wrote, and all of them SHALL end with `reflect: exit 0`.

#### Scenario: A program that does not finish

- GIVEN an image built from `examples/forever.hom` with a budget of 5000
- WHEN it boots
- THEN the serial port shows `no result within 5000 steps` and then `reflect: exit 0`

#### Scenario: A program that is not syntax

- GIVEN an image built from a file the reader refuses
- WHEN it boots
- THEN the serial port shows the reader's error text, the same text `host/out/run` prints for that file, and then `reflect: exit 0`

### Requirement: What the image does not provide is said, not hidden

A system call the layer does not answer SHALL write a line naming its number to the serial port and SHALL return "not implemented". A processor fault SHALL write a line with the fault's number, the instruction's address and the faulting address, and SHALL power the machine off. Running off the end of the stack SHALL be a fault and SHALL NOT write over other memory. The check SHALL fail when either line appears where it is not expected.

#### Scenario: A system call nobody answers

- GIVEN an image whose layer lacks an answer for a call the start-up makes
- WHEN the check boots it
- THEN the check fails and shows the line that names the call

#### Scenario: Nesting too deep

- GIVEN an image built from a program whose source nests deeper than the stack holds
- WHEN it boots
- THEN the serial port shows a fault report or the runtime's own stack report, and the machine powers off

### Requirement: The image has one thread and no clock

The image SHALL run on one processor with one thread. It SHALL NOT start the Lean runtime's event loop. The time it reports SHALL NOT be relied on by anything a program computes. Random bytes SHALL come from the processor's random instruction, and an image on a processor without one SHALL say so and stop.
