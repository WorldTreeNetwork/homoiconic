# unikernel-net

## ADDED Requirements

### Requirement: A run that passes its space is a reply, and the guest goes on

The network image SHALL pass a space to `reflect_reply_bytes` for every run frame, over UDP and over QUIC: the kernel's default, or the number of the command-line word `reflect.space=<cells>`, a whole number below 2^64; a word that is not one SHALL stop the guest before it is ready, as a malformed `reflect.port` does. The `RFL1` frame SHALL NOT change: a sender chooses the step budget, the guest's owner chooses the space. A run that passes its space, and an answer larger written out than its space, SHALL be answered with the reply `81 07` and transport status 0, as a run out of steps is answered with `81 01`, and the guest SHALL serve the next request. A guest of a crossing runs each turn under `Reflect.turnSpace` with no count, whatever `reflect.space` says, so that the record it writes replays the same elsewhere.

#### Scenario: A recursion that waits over UDP

- GIVEN a ready guest with 512 MiB and the default space
- WHEN the client sends `def deep x = [x, ...deep x]` applied to 0, and then `def build acc = build [0, ...acc]` applied to `[]`, each with the budget 100000000, and then factorial
- THEN the first two replies are `81 07`, each equal to the Linux process's, and factorial is answered after them in the same boot

#### Scenario: The limit undone

- GIVEN a guest started with `reflect.space=18446744073709551615`
- WHEN the client sends `deep` with the budget 100000000
- THEN the guest ends in `INTERNAL PANIC: out of memory` and answers nothing more
