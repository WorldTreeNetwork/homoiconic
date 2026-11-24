# bytecode-machine

What is built: `Reflect.Machine`, a stack machine for the `Reflect` language. `compile` takes a term to continuation-form code, `step` is total on an explicit state, and `run n` takes `n` steps. `machine_correct`, `machine_exact`, `machine_never_halts`, `machine_never_faults`, `run_add`, `run_halted`, `runUntil_eq`, `runPriced_run`, `runPriced_reach`, `runPriced_unit`, `machine_exact_priced`, `decompile_compile`, `depth_bound`, `run_cycle`, `runPriced_cycle`, `omega_cycle`, `forever_cycle` and `forever_bounded` are proved and restated in `kernel/MachineContract.lean`. A block entered in tail position, a call or a case whose continuation is `done`, pushes no frame (`push`, `homoiconic-q59.65`), so a loop whose calls are in tail position runs in constant memory. `step`, `run`, and the theorems about them take the operation table `Ops` as a parameter and hold for every table. `runPriced` (`kernel/Reflect/RunUntil.lean`) runs the same steps against a budget that charges each operation the cost its table gives (`ab8e361`); every budgeted path of the host runs it (`homoiconic-q59.52`). The speed measurement is in `docs/LEARNINGS.md`. The host runs `Reflect` programs on this machine through `reflect_run` (`openspec/specs/zig-host/spec.md`).

## Purpose

Name the machine that runs `Reflect` programs one step at a time, and its agreement with direct evaluation. This spec does not contain the language or the interpreter theorem (`openspec/specs/code-as-data/spec.md`), flattening to an array, serialized states, or a native executor.

## Requirements

### Requirement: Programs compile to code

The kernel package SHALL define an instruction set for the `Reflect` language and a total function `compile` from terms to code. The package SHALL prove that `decompile (compile t)` returns `t` for every term `t`.

#### Scenario: Code turns back into its term

- GIVEN any term
- WHEN it is compiled and then decompiled
- THEN the result is that term

### Requirement: The machine agrees with direct evaluation

The package SHALL define a machine state and a total function `step` on states. For every term `t` and outcome `o`, the package SHALL prove that `Direct [] t o` holds if and only if the machine, loaded with `compile t`, halts after some number of steps with an outcome that reads back as `o`. The package SHALL prove that whatever the machine halts with is exactly the compiled form of a source outcome, so that a returned closure holds the compiled code of its body. The package SHALL prove that a term with no derivation never halts. The package SHALL prove that the machine, loaded with `compile t` for any term `t`, is not in the fault state after any number of steps, under `run`, `runUntil` and `runPriced` alike; running out of budget leaves a running state, which is not the fault state. This is stated for compiled code only: `step` faults on code that no term compiles to.

#### Scenario: Identity

- GIVEN `app (lam (var 0)) (lam (var 0))`
- WHEN its code is run for seven steps
- THEN the machine has halted with the compiled identity closure

#### Scenario: Divergence

- GIVEN `omega`
- WHEN its code is run for any number of steps
- THEN the machine has not halted

#### Scenario: No fault without halting

- GIVEN `omega`, or any other term, closed or not
- WHEN its code is run for any number of steps, or under any priced budget
- THEN the machine is not in the fault state

### Requirement: A run can pause and continue

The package SHALL prove that running `n + m` steps from a state equals running `m` steps from the state reached after `n`. A halted state SHALL step to itself.

#### Scenario: Three slices

- GIVEN a program that halts after `n` steps
- WHEN it is run as three slices whose lengths sum to at least `n`
- THEN the outcome equals the outcome of one run

### Requirement: Steps bound control depth

The package SHALL prove that the value stack plus the pending frames after `n` steps is at most that of the starting state plus `n`. This is all a step budget is proved to bound in memory. The environments, closures and data a state holds are not bounded by a theorem: a recursion whose calls wait on each other keeps a frame and its environment per pending call, as `depth_bound` allows, and a program that builds data keeps the data, so what such a run holds grows with its steps. The vision's P3, a bound on the cells a state holds after `n` steps (`docs/DECISIONS.md`), is not proved (`homoiconic-q59.67`).

#### Scenario: A budget bounds the stacks

- GIVEN a step budget
- WHEN any program is run within it
- THEN the stack and frame depth is within the stated bound

### Requirement: A tail call keeps no frame

`step` SHALL push the frame `⟨k, env⟩` when it enters a function's body or a case branch whose continuation `k` is not `done`, and SHALL push nothing when `k` is `done` (`push` in `kernel/Reflect/Machine.lean`; `ppush` on the lazy machine). Such a frame would only end the block it returns to, and it held that block's environment. Dropping it SHALL change no outcome: `machine_correct`, `machine_exact`, `machine_never_faults` and the lazy machine's theorems SHALL hold with their statements unchanged. It SHALL change step counts: each dropped frame is one step `run` no longer takes (factorial 1290 steps to 1165 at level 0, 66758 to 55543 through one interpreter, 4816682 to 4036172 through two). The package SHALL prove that a run that comes back to a state it held stays within its first `a + p` states for any number of steps and any priced budget (`run_cycle`, `runPriced_cycle`), and SHALL prove by evaluation that `omega` and `examples/forever.hom` (`loopForever`) come back: `omega` from step 4 every 4 steps, forever from step 21 every 17, and forever through one interpreter, under `arith`, from step 853 every 832 (`forever_cycle_interp`), so a priced run of forever at any budget ends in one of 38 states, and through one interpreter in one of 1685 (`forever_bounded`). `kernel/Surface/Check.lean` SHALL check that forever's depth after 2000000 steps is at most 64 at levels 0, 1 and 2; with a frame per tail call it was 222222 at level 0.

#### Scenario: A tail loop at the default budget

- GIVEN `examples/forever.hom`
- WHEN `host/out/run` runs it with the budget 100000000 at levels 0, 1 and 2
- THEN each prints `no result within 100000000 steps` with peak resident memory under 64 MiB (`host/check.sh`; about 7 MiB at every budget, where a frame per tail call took 1153, 465 and 136 MiB)

#### Scenario: A recursion that waits still grows

- GIVEN `def deep x = [x, ...deep x]`, whose call waits on the next
- WHEN it runs with the budgets 1000000, 10000000 and 30000000
- THEN its peak memory grows with the budget (15, 91 and 260 MiB as a macOS process), within `depth_bound`

### Requirement: The machine runs operations

`compile` SHALL compile `prim c x` to the code of `c`, an instruction that checks the value on top is a number or a name, the code of `x`, and an instruction that replaces that value and the argument with the table's answer for its number. A value that fails the check SHALL halt the machine with `wrong` before the code of `x` runs. `step` and `run` SHALL take the table as a parameter. `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `run_halted`, `runUntil_eq`, and `depth_bound` SHALL hold for every table, with their statements unchanged by text and names. The instruction set SHALL be unchanged by text and names. An operation SHALL be one step.

#### Scenario: An operation on the machine

- GIVEN each operation scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

#### Scenario: Code with an operation turns back into its term

- GIVEN a term that contains `prim`
- WHEN it is compiled and decompiled
- THEN the result is the term

#### Scenario: Text and names on the machine

- GIVEN each text and name scenario in `kernel/ReflectRun.lean`
- WHEN the compiled program runs on the machine, whole and in three slices
- THEN the halted outcome reads back as the outcome of direct evaluation

### Requirement: The theorems depend on the logic only

`machine_correct`, `machine_exact`, `machine_never_halts`, `machine_never_faults`, `machine_never_faults_until`, `machine_never_faults_priced`, `run_add`, `run_halted`, `runUntil_eq`, `runPriced_run`, `runPriced_reach`, `runPriced_unit`, `machine_exact_priced`, `decompile_compile`, `depth_bound`, `run_cycle`, `runPriced_cycle`, `omega_cycle`, `forever_cycle`, `forever_cycle_interp` and `forever_bounded` SHALL be restated by a contract file. Their axiom dependencies SHALL NOT include `sorryAx` or an axiom declared by this package.

#### Scenario: No admitted correctness

- GIVEN the compiled theorem `machine_correct`
- WHEN its axiom dependencies are printed
- THEN `sorryAx` is absent and no axiom from this package is present

### Requirement: A budget charges an operation its cost before it runs

The table `Ops` SHALL hold `cost : Nat → Data → Nat` beside `op`, with one as its value when a table does not give it. `stepCost` SHALL be `cost n d` for a state whose next step runs operation `n` (a number, or a name whose number is `n`) on the data `d`, and one for every other state. `runPriced fuel s` SHALL take the same steps as `run`, in the same order, from the same states: the charge SHALL decide only whether the next step is taken, never which step it is. It SHALL stop, leaving the running state it is in, before a step whose charge is more than the fuel left; it SHALL take every step whose charge it can pay and subtract that charge, and a charge of zero SHALL use one unit, so every step uses at least one. A halted state SHALL stay halted. `step`, `run`, `runUntil` and the instruction set SHALL be unchanged, and an operation SHALL still be one step of `run`: what the charge counts is the budget, not the steps. For the table `arith`, `arithCost` (`kernel/Reflect/Arith.lean`) SHALL charge addition, subtraction and `less` the sum of the operands' bit lengths, multiplication, division and remainder their product, `text` and `codes` one more than the length of the text or array, and `equal` and every other operation or argument one; the bit length of a number `n` is `log2 n + 1`, so zero costs as one does. The charge SHALL be read from the argument without running the operation. A priced run SHALL stop at the state `run` reaches after some number of steps no more than the fuel (`runPriced_run`, and `runPriced_reach` for a state it stops at), so every theorem about what `run` reaches holds of what a priced run reaches; what a priced run of a compiled program halts with SHALL be what the program evaluates to (`machine_exact_priced`). With a table whose every charge is one, `runPriced` SHALL equal `runUntil` (`runPriced_unit`). `machine_never_faults_priced` covers `runPriced` on compiled code for every table.

#### Scenario: A large product costs more than a small one

- GIVEN `arithCost` and the operation `mul`
- WHEN it is charged for `[2, 3]` and for two numbers of 40 nines
- THEN the charges are 4 and 17689, the product of 133 bits by 133 bits

#### Scenario: Out of budget is not a fault

- GIVEN any term and any fuel
- WHEN the compiled term is run with `runPriced`
- THEN the machine is not in the fault state (`machine_never_faults_priced`)

### Requirement: One budget means the same on every budgeted path

Every machine run the host makes against a budget SHALL be a priced run, charged as `runPriced` charges it: the run command (`Surface.runText`, `Surface.runBytes`), the interpreter (`Surface.renderInterpreted`), the reply bytes (`Surface.replyBytes`), requests (`Reflect.converse`, `Reflect.driveRun`), channels and a guest of a crossing (`Reflect.beginRun`, `Reflect.turnRun`, `Reflect.settleRun`, `Reflect.stepRun`), the VM and the node (`Reflect.vmRun`, `Reflect.nodeRun`, through the channel runs), and the answers and schedule programs those read. A kept session runs on the lazy machine; its `steps` (`kernel/Surface/Keep.lean`) SHALL charge `lstepCost` (`kernel/Reflect/Store.lean`), at least one, before each lazy step: `cost n d` when the step runs operation `n` on an argument that is whole data `d`, and one for every other step, a step that fetches or hydrates the argument included. A lazy step the budget left cannot pay for SHALL NOT be taken. The interpreter SHALL perform each operation of the program it runs as one machine primitive on the same operation number and argument (`interp`, the `prim` case), so a run of `interp` on a program pays the same charge for each operation as a direct run of the program, and at least one for each of the interpreter's own steps. The theorems about these drivers SHALL hold of the priced runs, through `runPriced_reach`.

#### Scenario: The interpreter pays at least what the program pays

- GIVEN `mul` applied to two numbers of 40 nines
- WHEN it is run directly and through one interpreter, each with the budget 18000
- THEN the direct run prints the product and the interpreted run prints `no result within 18000 steps`, and with the budget 200 both print `no result within 200 steps` (`host/check.sh`)

#### Scenario: A turn's budget charges an operation

- GIVEN `examples/ask.hom` and the log answering 20 and 22
- WHEN the VM runs it with the budget 50 and with 49
- THEN it gives a state at 50 and none at 49: `add 20 22` costs 10, where one step used to count one (`kernel/LogCheck.lean`)

