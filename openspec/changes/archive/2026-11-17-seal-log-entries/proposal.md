# seal-log-entries

> **FOLDED 2026-11-17** into `openspec/specs/event-log/spec.md`, `openspec/specs/logged-processes/spec.md` and `openspec/specs/zig-host/spec.md`. Archived.

**Rigor:** instrument

Depends on: `add-event-log`, `add-logged-processes` (both folded). Vision: stage 5, D5 and D7. Bead: `homoiconic-q59.28`. Authority: the user, 2026-11-17, "yeah sounds good, hash check in kernel. continue", answering the question whether the kernel or the host should check that an identifier is the hash of its entry.

## Why

A log entry carried an identifier the log supplied. Nothing tied it to the entry, so two different entries could carry one identifier, and the one that arrived first was acted on. Two machines that received the same two entries in different orders would then disagree, and neither would be wrong by the rules. The network stages need an entry's identity to be a fact about the entry.

## What

- **An entry is written as a mark and an answer.** The log file has the shape it had, `[[1, 20], [2, 22]]`. What was read as the identifier is now a mark.
- **The kernel names the entry.** Its identifier is the Blake3 hash of the bytes of the pair `[mark, answer]`, as one number below 2^256 (`Surface.Keep.entryName`, `Reflect.Entry.seal`). A log cannot supply an identifier, so there is nothing to check and nothing to get wrong.
- **The mark is not read.** It tells apart two entries with one answer. A count, the name of the entry before, or a signature can go there later without the kernel changing.
- **Ops are sealed the same way**: `[mark, event]`, named by the hash of the pair as written (`Reflect.Op.seal`).
- **A refused op is reported by its place.** `refused: entry 2, [2, 0, 1], cannot happen`, counted from 0, in place of the op with its identifier.
- **Nothing else changes.** `Handle`, `Apply`, the folds and every earlier theorem are as they were: they hold whatever the identifiers are.

## What is proved

For every naming function `key` that gives different names to different data, with no admitted step:

- `sealed_same`: two sealed entries with one identifier are one entry.
- `sealed_first`: every entry of a sealed log is among its first deliveries. With `log_once` and `log_interact`, the requests the program makes are answered by the distinct entries in the order of first arrival, until the program ends, and none is passed over for a different one. This is about which entries count as deliveries, not about how many are used: an entry that arrives after the program has ended is not acted on.
- `sealed_op_same`, `sealed_op_first`: the same for ops, for every way of reading an event from data.

## What this shows

From `host/check.sh` and `kernel/LogCheck.lean`:

- `[[1, 20], [1, 22]]` on `examples/ask.hom` acts on both entries and ends with 42. Before this change the second was passed over and the program was left waiting.
- `examples/ask-again.log`, five deliveries of two entries, still reaches the root `examples/ask.log` gives.
- The session's root is the root of the proved fold given the same sealed entries, at every length of log tried, for VMs and for nodes.
- An entry's name is its hash: highest byte the first byte of the hash, lowest the last.

## Limits

- **That Blake3 gives different names to different entries is assumed.** It is the hypothesis `Function.Injective key` of the four theorems. It is not an axiom in any proof, and nothing proves it of Blake3; no hash has it in the strict sense. This is the assumption every stored piece already rests on (D5).
- **That different data has different bytes is tested, not proved.** `entryName` hashes the bytes `Wire.write` gives, so applying the four theorems to it also needs `Wire.write` to give different data different bytes. No theorem says so. `kernel/WireCheck.lean` tests the round trip on examples, and `Wire/Cbor.lean` does not cover values whose lengths pass what the byte form can hold. This is the boundary `docs/PROOFS.md` already states for the wire.
- **Reading a log and sealing it is tested, not proved.** `dataEntries` and `dataOps` build each entry with `Entry.seal` and `Op.seal`, so each is sealed by construction, but no theorem is stated about them.
- **Nothing is signed, and an entry does not name the one before it.** Who may add an entry, and in what order entries stand, are still not here. The mark is where both will go.
- **A state still holds the name of every entry acted on.** Each is now a number below 2^256 whatever the mark was. A compact record in place of the list is not attempted: with a chain of parents, that an old entry is passed over would rest on the hash having no cycles, which cannot be proved from "different data, different names" alone.
- **`from` does not check that the log goes with the state.** It checks the shape of the kept state and the hashes of its pieces. A state kept from one log and handed another carries on from where it stood; `log_restart` speaks only of a state handed a log that begins with the one it was reached by.
- **Kept states from before this change do not carry over.** Their lists hold the identifiers the old logs supplied.
- **The hash is the kernel's own Blake3**, written in Lean. It is slow next to a native one (`homoiconic-q59.20`).
- **An exact repeat is not a second event.** Two entries with the same mark and the same answer are one entry. A log that means to answer twice with the same data must give the two different marks.

## Disposition

ACTIVE BUILD, 2026-11-17, after review. Folded and archived, 2026-11-17.
