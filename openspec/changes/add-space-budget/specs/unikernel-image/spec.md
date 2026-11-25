# unikernel-image

## ADDED Requirements

### Requirement: A run on the image has a space limit

The image SHALL pass a space to `reflect_run` and `reflect_interp`: the kernel's default (`reflect_default_space`), or the third word of the command line, `[step-budget [levels [space]]]`, a whole number below 2^64. A word that is not such a number SHALL end the image with a line of its own and `reflect: exit 2`. A run that passes its space SHALL end in the kernel's text, `no result within <space> cells`, and `reflect: exit 0`, as a run out of steps does, and SHALL NOT end in `INTERNAL PANIC: out of memory`. The default SHALL be a limit under which, on a 512 MiB machine started by `given.sh`, each of these ends in the kernel's text at the budget 100000000 at levels 0, 1 and 2: `def deep x = [x, ...deep x]`, `def build acc = build [0, ...acc]`, a text of 2 million characters whose `codes` is kept and that is then consed onto, an array of 2 million numbers of 19 digits answered, and an answer built by doubling. Where the budget ends such a run before it holds that much (`deep` through two interpreters, `build` through one or two), the budget's text is the kernel's text too. A machine with other memory is given another space by whoever starts it; the space is not in proportion to the machine's memory, since the image and the program are fixed costs (`unikernel/README.md`). The limit bounds what a run makes; what the program's bytes cost to read is bounded by the byte limit, as before.

#### Scenario: A recursion that waits, given at boot

- GIVEN the byte form of `def deep x = [x, ...deep x]` applied to 0
- WHEN `given.sh` boots it with `100000000 0` and with `100000000 1`
- THEN the serial port says `no result within 4000000 cells` and `reflect: exit 0`, the same as the Linux process

#### Scenario: A smaller space on the command line

- GIVEN the same bytes
- WHEN `given.sh` boots it with `100000000 2 100000`
- THEN the serial port says `no result within 100000 cells`

#### Scenario: The limit undone

- GIVEN the same bytes
- WHEN `given.sh` boots it with `100000000 0 18446744073709551615`
- THEN the image ends in `INTERNAL PANIC: out of memory`: the limit, not the budget, is what stops it
