# Learnings

## 2026-11-09 — speed of the Lean-compiled machine

`kernel/Bench.lean`, built with `lake build reflectBench`, Lean 4.35.0, Apple M1 Max, three runs each.

| Program | Machine steps | Time | Steps per second |
|---|---|---|---|
| Count down from 1,000,000, direct | 23,000,025 | 557–584 ms | about 40 million |
| Count down from 20,000, through the interpreter | 23,801,006 | 626–629 ms | about 38 million |
| Count down from 300, through the interpreter twice | 25,373,970 | 666–673 ms | about 38 million |

- One loop iteration is 23 steps direct, about 1,190 through one interpreter, and about 84,600 through two. One interpreter level costs a factor of about 52. The second level costs about 71.
- The machine does not reuse frames for calls in tail position, so the direct run holds about three frames per iteration, roughly three million at its deepest. It still runs.
- This is the unoptimized machine on continuation-form code. No flattening, no primitive beyond `succ`, `cons`, and the case form.

## 2026-11-09 — a proof found what the scenarios missed

Eighteen programs agreed across direct evaluation, the interpreter, and the machine. The forward simulation then failed on one rule: a case form whose scrutinee errors. The interpreter's `bind` helper reused the name `rs`, which shadowed the result it was meant to pass on. Scenarios now cover it. A helper that binds names needs names no caller can use.

## 2026-11-09 — fuel does not bound machine steps

A hint given to the machine-proof worker was false: "halting in `n` steps forces `evalFuel (n+1)` to be `some`". `app (app (var 5) a) b` at the empty environment halts in one machine step and needs fuel 3. Fuel bounds derivation height. The worker proved the reverse direction by strong induction on the step count instead.

## 2026-11-09 — reverse simulation without inversion

To show that a run of the interpreter comes from a source derivation, it is enough to show that a source evaluation out of fuel leaves the interpreter out of fuel. That is a goal-directed walk, like the forward direction. Then completeness, the forward direction, and determinism finish it. The interpreter's run is never taken apart.

## 2026-11-10 — the host was built without optimisation, and a check passed a crash

- The host's Lean objects had been compiled without optimisation since the host landed. Nobody noticed until `host/out/run` made the speed visible: about 3.7 million steps a second. With `-O3` it is about 34 million. Defining `NDEBUG` reaches about 45 million but removes Lean's runtime assertions on the generated C, so it stays off.
- Review of `retire-circular-kernel` found shell checks of the form "a non-zero exit is a pass". Such a check also passes a crash. `host/check.sh` now asserts the exact exit status, empty standard output, and the exact error line.

## 2026-11-10 — one statement for every operation

- The vision expected one lemma per primitive (P8). Making the operation number a runtime value and the table a typeclass parameter removed the per-operation lemma entirely: the interpreter's branch for an operation is the same construct, `prim`, applied to the evaluated parts. The cost is the shape of an operation: total, data to data, with no failure outcome.
- Lean includes an instance-implicit section variable in every theorem of the section, whether or not the theorem uses it. Theorems that do not need the table had to be marked `omit [Ops] in`.
- A contract file that imports an instance can silently check a theorem for one table only. The contracts import no table and quantify over it explicitly, `∀ [Ops], …`.

## 2026-11-10 — one driver, one simulation lemma

- The request driver was defined once, over an abstract way of evaluating (`Sys`), with one simulation lemma (`Sim.drive`) that lifts turn-by-turn agreement to whole runs. The interpreter and machine agreement theorems for requests then each cost only a turn-level equivalence, proved from the existing `reflective` and machine theorems.
- Review caught that a request carries no mark. The driver reads every function a turn ends in as a request, so `fn x -> 42` asks `42` and a driven program cannot finish with a function. The first description said such functions end as `wrong`; only some do.

## 2026-11-11 — one type for pieces, progress one place at a time

- Pieces use one type, `P`, for data, values and environments. Resolution, `Unf`, is then one inductive relation, and the store proofs go by induction on it. Mutual definitions remain only where a piece is built from the machine's own separate types.
- Progress of the lazy machine is proved by forcing one place at a time (`force`): induction on the resolution of the piece at that place, fetching until it is not a reference. No global measure on the store or the state was needed.
- The check cuts a state as a tree, with no sharing. The interpreter interpreting itself on `2`, stopped after 300 steps, gave 1,110,817 pieces. Storing by content removes the duplicates, and needs bytes.

## 2026-11-11 — a byte form for code

- `decompile` reads code that no compilation produces: `decomp` drops `checkFun`, `checkData` and `checkNat`. So "decompile, then compile" is not the identity on arbitrary code, and two different function values wrote the same bytes until review caught it. The writer now compiles the decompiled program again and compares (`Wire.blockTerm`). `decompile_compile` holds only in the other direction.
- Lean 4.35 accepted `Wire.unreify` by structural recursion over the nested type `Data` (`arr : List Data`), with patterns several list items deep, and no termination proof. `unreify_reify` was `induction t <;> simp_all [reify, unreify]`.
- In Lean 4.35 a doc comment (`/-- … -/`) directly before `#eval` is a parse error: a doc comment must precede a declaration. Use `--` there.

## 2026-11-12 — kept state

- Lean 4.35 refuses borrow annotations (`@&`) on an `@[export]` declaration ("marked as `export` but some of its parameters have borrow annotations"). An exported function therefore always uses up each Lean-object argument, and a C caller that will pass the same object again must `lean_inc` it first. The host does this through `kernel_retain` in `kernel/ffi.c` before every call that takes the session.
- A fuel counter spent on a data-dependent loop looked like success when it ran out. `Surface.Keep.advance` spent fuel following references, and at zero returned the session unchanged; with 70 references in a chain the turn ended with no text and exit 0. Review found it. References are now followed by `Keep.chase` with no limit, fuel only bounds phases that come in one order, and running out says `error: the turn did not settle`.
- Blake3, written in Lean from its specification in about 100 lines (`kernel/Wire/Blake3.lean`), matched all 22 official vectors, and the reviewer's 135 further inputs against Python's `blake3`. The file has not changed since it landed.
- Writing Lean through an unquoted shell heredoc (`<<EOF`) runs each backticked word in a doc comment as a command. Use a quoted heredoc (`<<'EOF'`) for Lean source.

## 2026-11-12 — channels

- The request driver's cases could not be reused for one turn of a process. `Drive` is indexed by the list of answers and the list of requests asked, so its four cases were restated without those lists as `Settle` (`kernel/Reflect/Channel.lean`). The cases are the same; the restatement is the cost.
- The simulation from requests, `Sim`, carried over to schedules with one added field: `PSim` is `Sim` plus `start`, which says the two ways of evaluating start a program alike. The machine agreement theorems for schedules then followed from the turn-level ones already proved for requests.
- Review found no fault in the definitions and two in what the printed text claimed. The last line, then `nothing more can happen`, described the chooser, which never offers an answer from outside and does not run the machine, not what the semantics allows. And a printed schedule replays to the same last line only when the first run was not refused and did not run out of budget.

## 2026-11-12 — unikernel image

- The Lean runtime needed no rewrite to run with no operating system: musl, linked as Zig ships it, reaches a Zig layer through the `syscall` instruction as it would reach Linux. The one runtime edit is weakening `initialize_libuv` in a copied archive so an empty function wins, because the stock initializer starts the event-loop thread.
- With one privilege level, `syscall` lands on the caller's stack, so the layer must step over the 128-byte red zone and save vector state itself. The negative controls show both matter: removing either makes the preservation probe fail.
- Review sent the contract back once with six fixes, chiefly that the Linux comparison must be built from the same clean, provenance-checked objects rather than the partial artifacts of the failing Linux `host/check.sh` link.

## 2026-11-12 — event log

- P14 did not need hashing. The plan had it depend on P5; with the identifier as data the log supplies, a repeated entry is recognised by equality and nothing about hashes is assumed. What a hash would add, that the identifier names this entry and no other, is the host's to supply.
- A kept state has to be read in the form the cutter leaves it, not embedded by its root. `keep` puts the root reference into the next turn's environment, and a small root piece then stays a reference where a run from the start would hold it inline, so the two are cut differently. The VM session takes the function out of the state piece, and a restarted state then has the root a replay has. This is tested on examples, not proved.
- `Settle` and `Turn`, written for processes, were the handler's cases as they stood. The log needed no new statement about evaluation; its proofs are about lists.
- The derived `==` on data has no proof behind it, so list membership could not be decided through it. Equality of data is decided by a definition written with the log.
- Review found the reader of a kept state too loose: it dropped list tails, so several pieces read as one state. It also found that the session and the proved fold count different steps, so one budget is not one bound.

## 2026-11-12 — logged processes

- Splitting an event into a plan of machine runs and a function from where they end to the next configuration let one definition serve two machines. `plan` is polymorphic in how a function is held, proved to be `Step` for any way of evaluating, and used unchanged by the session, where a function is a stored piece. What is left unproved in the session is running the jobs and joining them, not deciding what an event does.
- The dedup proofs for a node are the log's without the finished case, and shorter. They were written again rather than shared: the one-program VM ignores entries after its program ends, and a node refuses an op for a finished process, so the two handlers are not instances of one.
- An op that cannot happen was given no next state rather than being skipped. With that, every op in a log was applied, so "already in the log" and "already acted on" are the same thing and the restart theorem needs no side condition.
- Review found no fault in code or proofs, and one limit that understated what is read when a kept node is opened.

## 2026-11-13 — interpreted runs and text

- A data kind that `case` goes wrong on would break the interpreter theorem. `interp` must answer a wrong outcome as the data `[2]`, and it cannot tell that a value is of a kind it may not take apart, so it would not answer `[2]` where the program goes wrong. A text kind of its own must therefore be visible to `case` as the list of its code points (`homoiconic-q59.35`).
- In `examples/sieve.hom` every filter process ends up holding channel 0. Held names are found by matching numbers anywhere in a process's start data, quoted code included, so any 0 in the code a process is started with counts as holding channel 0 (`homoiconic-q59.36`).
- `--text` first treated any array of valid code points as text and printed `[1, 2, 3, 4]` as control characters. The rule is now printable characters, tab and line feed; any other number leaves the result printed as numbers.

## 2026-11-14 — definitions that name one another, and array patterns

- The old reader never read a catch-all arm that no branch fell to, so a `case` covering `0`, `m + 1`, `[]` and `[h, ...t]` with `_ -> ghost` read and ran even though `ghost` is bound nowhere. The new reader first read every catch-all, and that old program became a syntax error; advise (gpt-6.1-sol) found it, though every file of `examples/` read to its old bytes. The reader again leaves such an arm unread (`95ba66e`): a promise that old programs read to the same term covers what the old reader skipped, not only what it checked.
- A definition with no parameter in a ring is worked out again at each use, not once where it is bound, so `def a = b` and `def b = a` do not end rather than being refused.

## 2026-11-17 — text and names as data

- With `interp` unchanged, a new kind of data must be seen by `case` as a number or a list and go `wrong` exactly where that one does: `interp` tests a value only with its own `case` and builds its answer with its own `succ`, `cons` and `prim`. That forced `succ` of a name to be a plain number (not a name) and a name used as an operation number to run that operation; arithmetic operands were then left plain, so a name is a number only where the language's own constructs look.
- The first early proof gate could not have run: `ReflectContract.lean` imports the umbrella `Reflect`, whose machine, channel, node and store proofs do not compile until their own tasks are done, so a check of it mid-change either fails or reads stale `.olean` files. A focused gate, `kernel/InterpGate.lean`, importing `Reflect.Correctness` alone and restating the four interpreter theorems, replaced it; it passed in both steps with the same axioms.
- The design's text for `examples/guess.hom` did not read: its splice `~[2, ch]` sat under the binder `fn nothing` of its quotation, which the reader refuses. The example quotes the body alone and builds the function's code as data, `[1, body]`; what runs is the same.
- Measured (Lean 4.35.0, Apple M1 Max, `kernel/Bench.lean`): a `case` walk over a text of 100,000 ASCII characters takes about 68 ms (2,900,030 machine steps), and `codes` followed by the same walk over the array about 69 ms; `codes` alone is about 2 ms. A walk is linear, about 0.7 µs a character, and a text costs no more to walk than the array of its code points, though each character is still a list cell.
- The unikernel image links the same Lean objects and has not been rebuilt or checked since `Data` changed (`homoiconic-q59.40`); `unikernel/build.sh` finds its modules by `lean --deps` and should need no edit, but that was not run.
- `StoreCheck.lean` and `KeepCheck.lean` stopped compiling when `Data.name` was added, because their own piece walkers match every leaf; no gate before `host/check.sh` builds them, so a test file can fall behind a data type silently until the full check runs.
- The machine and the lazy machine needed fewer new lines than the wildcard list predicted: `succ` and `checkNat` on a text, and `cons` onto a name, already fall to lines that answer `wrong`, which is the right answer. `stuck_core` took the new cases within its old heartbeat limit, and `Proof.lean` builds in about 24 s.
- Checking `ReflectRun.lean` went from about 55 s to about 105 s with the text and name scenarios at interpreter levels 1 and 2.
- Review of the implementation by another model family accepted it with no required fix, after two design reads had sent it back with three fixes and then one; the fixes were all made in the documents before any code was written.

## 2026-11-17 — entries named by their hash

- "Should the kernel check that the identifier is the hash of the entry?" had a simpler answer than a check: the kernel computes the identifier, so a log has no way to supply one. No definition of handling changed, and every earlier log theorem stands as it was.
- A single "last entry" in place of the list of entries acted on would need the hash to have no cycles to prove that an old entry is passed over. That does not follow from "different data, different names", so the list stays.
- Printing a refused op with its identifier would have printed a 77-digit number. The line now gives the op's place in the log.
- Review (gpt-6.1-sol) found the proofs sound and two sentences too strong: `sealed_first` says which entries count as deliveries, not that each is used, and the step from the abstract theorem to `entryName` also rests on the byte form telling data apart, which is tested only.

## 2026-11-22 — folding the network stage

- `add-unikernel-quic` and `add-network-channels` landed with a short proposal, checked tasks and no banner or spec delta, so fold could not admit them; the code (QUIC on `reflect.quic_port`, `reflect.wire_port`, `reflect.peer`, and the evaluating exports `reflect_remote_offer`, `reflect_remote_take`, `reflect_remote_log`, `reflect_remote_same`) is ahead of the living specs. The `zig-host` sentence naming every evaluating export was false from `793b583` until a delta adds them.
- `add-boot-program-bytes` (rigor instrument) reached fold without the read by another model family its own task asked for; it was folded on the orchestrator's instruction with that box left open.
- `add-unikernel-net` passed on morphie on 2026-11-19 and waited three days for fold behind one unchecked box ("publish the endpoint contract for Mjolnir") that Mjolnir had already consumed (`homoiconic-q59.17`).

## 2026-11-22 — the interpreter on a schedule

- 2026-11-22: `homoiconic-q59.25` needed no new lemma. `PSim`'s `start` field for the interpreter is `reflective` with `reflective_coverage`, and its turn-level `Sim` was already `sim_interpreted`, so `network_reflective` is two instances and an injectivity fact about `Config.map`. The limit the bead cites was never in `openspec/specs/channels/spec.md`; it was one sentence in `ARCHITECTURE.md` and a dated note in the vision's `design.md`.

## 2026-11-22 — the fault state

- `machine_never_faults` needed no hypothesis on the term: an open term halts with `unbound` and an ill-typed one with `wrong`, so every fault case in `step` is a stack-shape error that the check instructions the compiler emits rule out. The `fault` branch of `Surface.replyBytes` (reply tag 5) is therefore unreachable for program bytes; it stays as the answer for code the compiler did not make.

## 2026-11-22 — one root for one value

- Proving that equal values are saved under one root (`homoiconic-q59.29`) showed where it is false. `save` stores the top piece whatever its size, so a root can name a piece of at most 256 bytes, which `cut` would have left in place. `keep answer` starts the turn from the root itself, and a waiting program that keeps hold of the function it was resumed from (`λf. f 5 (λx. ask 7 (λy. f))`, 36 bytes) was saved under `af0852f8…` by the session and `c53dc525…` held whole. A VM and a node open the pieces under the root and do not carry it, so their roots were not affected in any run. The invariant that makes the statement true needs no assumption on the hash: a reference is good when it is the one `cut` gives the value it stands for.

## 2026-11-23 — writing the network specs from the code

- Writing `add-unikernel-quic`'s SHALLs from `unikernel/net.zig` and `quic.zig`, rather than from the proposal, found four things the proposal does not say: the paravirtual clock read scales with a wrapping 64-bit multiply and goes backwards after a few seconds without a clock update (`homoiconic-q59.48`); the certificate's private key is a constant in the source, so the pin names the tree, not a guest (`q59.49`); QUIC datagrams skip the UDP checksum and any datagram to the port moves where the guest sends next (`q59.53`); `check-quic.sh` leaves the guest to its timeout when a step fails. `check-quic.sh` passing was not evidence for any of them.
- `add-network-channels`'s proposal says the schedule of the deliveries is the log; the code prints the schedule the scheduler takes on one machine, and the receiving guest runs the function only to its first send (`homoiconic-q59.51`). Given back to `reflect_channels`, that log does run the same events to 42 (checked by hand). `reflect.quic_port` given with `reflect.wire_port` or `reflect.peer` is accepted and shares one connection with it (`q59.50`).
- Operation costs (`ab8e361`) reached the run command only: `runText` and `runBytes` call `runPriced`, while `reflect_interp`, `reflect_reply_bytes` and the request, channel and store exports still call `runUntil`. `mul` of two 40-digit numbers stops at budget 200 under `host/out/run` and finishes under `--interp=0`, and a network budget does not bound work inside an operation (`homoiconic-q59.52`).

## 2026-11-23 — a turn holds a small root in place

- 2026-11-23: `homoiconic-q59.47` was fixed on the reading side, not in `save`: `keep answer` holds the piece under a root in place when it is at most 256 bytes (`Wire.opened`), so no root of a value changed and only the wrong root of the counterexample did. A fix in `save` or `cut` would have needed the store inside `cut` or a second rule for the top. `chase` got its bound back, but as the number of pieces the session holds and one more, which only a chain that meets a reference twice can pass; that made it total, and `advance_turn` proves one turn of `keep` holds and saves only references saving made. The hash map of pieces has no lawful `ByteArray` keys in Lean 4.35, so that a supplied piece is found again stays a hypothesis (`homoiconic-q59.54`).

## 2026-11-23 — one budget on every path

- 2026-11-23: Moving every budgeted path from `runUntil` to `runPriced` (`homoiconic-q59.52`) changed no proof beyond one line at each use: the driver proofs needed only that the run reaches its state by `run` in some number of steps, so `rw [runUntil_eq] at h` became `obtain ⟨_, h⟩ := runPriced_reach h`. The interpreter needed no change of its own: `interp` performs an operation as the machine primitive on the same number and argument, so it pays the program's charge and its own steps on top (`mul` of two 40-digit numbers finishes directly at 18000 and not through one interpreter). The mjolnir fixtures (factorial at 100000000, forever at 5000) reply with the same bytes. The one expected value that moved was `LogCheck`'s "fold finishes, session does not" budget, 41 to 50, because `add 20 22` now costs 10.

## 2026-11-23 — the guest's clock and its one QUIC connection

- 2026-11-23: `check-quic.sh` passed its loss step only by accident. The wrong-pin step before it leaves the guest in an unfinished handshake, which nothing replaced; the next client finished that same handshake because `quic-client` drew its connection IDs and its X25519 secret from a fixed sequence, so it was the abandoned client again, byte for byte. With real randomness the guest was stuck for good, and the client's key share had been public all along (`homoiconic-q59.55`).
- 2026-11-23: "retarget only after the packet opens" does not settle `homoiconic-q59.53`. An Initial opens under keys made from an ID in the packet itself, so anyone can send one that opens. What keeps a forged Initial from resetting an exchange is the rule for when a connection gives way (it has answered, or two idle seconds), and the reply address is fixed at the first Initial, not moved by later packets that open.
- 2026-11-23: the first adversarial step passed against a guest with the old retargeting put back. A guest that has accepted has nothing left to resend (the client's Handshake acknowledgement clears the Initial flight too, `homoiconic-q59.56`), and the client's own next datagram moved the address back. The old behaviour fails only when the client loses the reply, the second address sends last and the client then keeps silent; each fix was undone in turn to see its step fail (`unikernel/evidence/check-quic-controls.log`).
- 2026-11-23: read from the code, not run: under the old rule the client's own resent Finished, a long-header packet the server never acknowledges, replaced the connection after the reply, so a lost reply was never resent even with no attacker.
- 2026-11-23: on morphie a non-interactive `ssh morphie <command>` has no `zig`; Zig 0.16.0 is at `~/.local/share/mise/installs/zig/0.16.0/bin`, and elan at `~/.elan/bin`.
- 2026-11-24: making a QUIC acknowledgement count only in its own packet number space (`homoiconic-q59.56`) was not a one-line fix. The old rule was the only thing that ended two flights: the guest's Initial ServerHello (the client sends no Initial after its own is acknowledged) and the client's Finished (the guest sends no Handshake packet once it accepts). They now end by RFC 9001's rules (4.9.1, 4.1.2). With either rule out, `quic-self` exits 28 or 26 (`unikernel/evidence/check-quic-controls-q59.56-57.log`).
- 2026-11-24: no step against a real guest fails with the old acknowledgement rule put back; all fourteen pass. The guest's Initial and Handshake flights travel in one datagram and this client acknowledges nothing in the Initial space, so the two never part on a TAP. `quic-self` has to cut that datagram between its packets and have the client resend its first flight on a stale packet number to get an Initial acknowledgement at all. On a network, whoever saw the client's first datagram can seal one, since Initial keys come from it; that was read, not run.
- 2026-11-24: no QUIC reply is ever acknowledged. A client that has the reply has nothing pending, and an ACK frame only rides on a flight. With `homoiconic-q59.57` undone the guest sent 36 datagrams in 11 s after a client had left, and would have gone on until the next connection. It now sends each reply ten times over 6.36 s and stops (`homoiconic-q59.58`).
- 2026-11-24: a give-up does not bound amplification, and the three-times limit needs the source address. With the limit out and the give-up kept, a forged 1200-byte first flight drew 7490 bytes. With the limit in but a server connection taking datagrams from any address, the same flight replayed from a second address raised the limit and the forged address drew 7470: a replayed Initial opens, since packets are not checked for replay. The guest answers in datagrams of 748 bytes, not 1200, so one first flight draws four of them and four bare ServerHellos, 3568 bytes (`homoiconic-q59.59`).
- 2026-11-24: a flight held back by the three-times limit must not count as a try. The first version of the in-process check threw away the datagram the server sent when the limit rose, and the exchange then missed its 1.2 s: the ServerHello had used eight of its ten tries on sends the limit let through alone.

## 2026-11-24 — a VM's and a node's session, the half that is about references

- 2026-11-24: `full` being `partial` did not stand in the way of `homoiconic-q59.54`. A `partial` function is still a function of its type, and `full` gives data, so the proof never looks inside it. Only `parts` had to change, because it hands pieces on. Its bound is the one `chase` has, counted over the whole list and not over each run of references; fuel that counted list items would have needed the size of every piece.
- 2026-11-24: the invariant for a node has to speak of a function. `Doing.done` turns the statuses of an event's runs into the next configuration, so `DoingGood` says: from statuses that hold only saved references it gives a configuration that does. `plan_good` proves it for every event `Reflect.plan` plans.
- 2026-11-24: reading a kept state needs less than "the root is a reference saving made", which is false of a small root. `openState` and `openNode` only use the piece under the root, so `RootGood` asks what `answer_turn` asks, and `save_opened` gives it.
- 2026-11-24: an unconditional `restart_same_root` for a session needs two halves, and this was one. `Made` is `Good` and `Unf`. `Good` is now proved of every session. `Unf`, that the saved piece resolves to the state `Logged` gives, is the session computing what `handleRun` computes, and nothing proves that yet (`homoiconic-q59.54`, left open).
- 2026-11-24: taking a `do` block with early returns apart in a proof: `simp only [bind, Except.bind, pure, Except.pure]`, then `split at h <;> try (simp at h; done)` repeated with `repeat'`, leaves one goal for each way the block can succeed, with the equations of the path in context.

## 2026-11-23 — hardening the boot-bytes boundary (homoiconic-q59.60)

- 2026-11-23: Cloud Hypervisor 54.0 exits 0 when the guest is destroyed under it. A 500 MiB `--initramfs` with 512 MiB of memory lands on the ELF at 16 MiB; the vCPU stops with `InternalError`, the serial port stays empty, and the exit status is still 0. "CH exited 0" says nothing about whether the guest ran; the check has to look at what the serial port said.
- 2026-11-23: the image and the Linux process disagreed on 16 MiB of bytes `81`: the Linux process, with all the memory it wants, printed the bytes error, and the 512 MiB image printed `INTERNAL PANIC: out of memory`. Agreement with the comparison process holds only for inputs that fit the guest's memory; valid data within 16 MiB can still exceed it (`homoiconic-q59.61`).
- 2026-11-23: cutting the command line at 1023 bytes turned `000…000x` (1100 zeros, then x), a word the Linux process refuses, into a valid budget of 0: the image printed `no result within 0 steps`.
- 2026-11-23: `unikernel/out/reflect.elf` after `check.sh` is the last image the check built, a `PRETEND=random_fails_when_served PROBE=random` probe, not factorial. An experiment that boots it says "the processor gave no random bytes"; build a factorial image of your own for experiments.

## 2026-11-24 — acknowledging the reply, padding the first answer, bounding levels in the kernel (homoiconic-q59.58, q59.59, q59.62)

- 2026-11-24: `quic.zig` stepped over every variable-length integer it read by `varLen(value)`, the width of the shortest form, not by the width the prefix bits gave. It read only what it wrote itself, always in the shortest form, so nothing showed it. A two-byte Length on a 50-byte ACK-only Initial put the parser one byte off and the packet did not open. RFC 9000 allows any longer form; parsers now step by the encoded width, and seal still writes the shortest form, because Mjolnir's vendored copy of the old parser (`native/reflect_quic/quic.zig`) has the same fault.
- 2026-11-24: acknowledging by "names the flight's latest packet" left a flight unfinished when the peer acknowledged an earlier copy that a resend had overtaken. With no ACK-only packet it never mattered, because the peer kept resending its own flight and named a later number. Once the client sends one acknowledgement and leaves, it names whatever copy it got; `acked` now takes any number from the flight's first send to its latest.
