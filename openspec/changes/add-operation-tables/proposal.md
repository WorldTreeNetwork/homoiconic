# add-operation-tables

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `retire-circular-kernel` (folded, `c16513d`). Vision: `add-verifiable-network-vision`, stage 3, obligation P8. Direction from the user, 2026-11-10: operations are added one set at a time, and running them in emulation is enough for now.

## Why

The language can count up by one and build arrays. Anything else, such as adding two numbers, has to be written as a loop in the language. The vision planned for operations to come in through one general statement, so that adding a set of them does not reopen the proofs.

## What

- ADD one construct, `prim c x`: `c` evaluates to an operation number, `x` to a data argument, and the result is what a table says for that number and argument
- The table is a parameter, `Ops`, holding one total function `op : Nat → Data → Data`. `Direct`, `evalFuel`, the machine, and every theorem take it as a parameter. Every theorem holds for every table
- The interpreter gains one branch that evaluates the two parts and uses `prim` itself. The interpreter does not depend on which table is in use, so adding an operation changes neither the interpreter nor any proof
- ADD the first table, `arith`: add, subtract, multiply, divide, remainder, equality of any two data values, and less-than, on natural numbers of any size
- The surface syntax resolves `add`, `sub`, `mul`, `div`, `mod`, `equal`, `less` and the general `op` as built-in names

## What this is and is not

This is stronger than P8 as the vision sketched it. P8 expected one lemma per operation. Here there is none: an operation is an entry in a table, and the theorems are quantified over tables.

The price is the shape of an operation. It is a total function from one data value to one data value. It cannot take a function, cannot fail to answer, and cannot make the program go `wrong`: an operation given something it does not expect answers with a data value of its own choosing. `arith` answers `[]`. Two operands travel as a two-item array.

Not in this change:

- Infix operators such as `a + b`. They wait for the reader's layout rewrite (`homoiconic-q59.6`).
- Bytes, hashing, and fixed-width integers. Each is a later table, or a later extension of this one. Bytes need a decision about the data type first.
- Native code for an operation. The table is a Lean function compiled by Lean. `arith` uses Lean's natural numbers, which are exact at any size.
- A cost per operation. One machine step runs one operation whatever its size, so a step budget does not yet bound work done inside an operation. Filed as a bead.
- P9, the bound on interpreter steps.
- Combining tables. There is one table in use at a time; a second set of operations is added by extending the function.

## Impact

- Capabilities: MODIFIED at fold by ADDED requirements in `code-as-data`, `bytecode-machine`, `surface-syntax`. No existing requirement changes
- `reify` gains tag 6: `[6, c, x]`. The machine gains two instructions, `checkNat` and `prim`
- The contracts in `kernel/ReflectContract.lean` and `kernel/MachineContract.lean` are restated as `∀ [Ops], …`. Neither file imports a table, so a statement cannot silently hold for one table only
- `ARCHITECTURE.md`: the Reflect section gains a paragraph at fold
- Vision: P8 is met by this change for operations of this shape; noted in the vision's changelog at fold

## User journey & surfaces

The surface is program text.

- **Working** — `host/out/run examples/factorial.hom` prints `265252859812191058636308480000000`. `add 2 3` prints `5`. `interpret (quote (add 2 3))` prints `[0, [1, 5]]`.
- **Empty** — a program that uses no operation reads and runs as before.
- **Failed** — an operation gives a different answer directly, interpreted, and on the machine; or a program that names `add` as its own binding gets the built-in one.
- **Off** — `op 99 [1, 2]`, a number no operation has, prints `[]`.

## Out of scope

Listed under "Not in this change".
