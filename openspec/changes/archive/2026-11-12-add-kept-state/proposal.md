# add-kept-state

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `add-wire-bytes` (folded, `1379a02`), `add-state-store` (folded). Vision: the state half of stage 5, and D5 (hashing is assumed). Bead: `homoiconic-q59.22`. Authority: the user, 2026-11-12: define Blake3 in Lean, record the Zig version as a later intention (`homoiconic-q59.20`), "go ahead and do this".

## Why

The state store is proved and lives in memory. A waiting program cannot outlast the process, so `ask` replays the whole program from the start on every call. The byte form exists for whole values only: a piece that holds a reference to another piece has none, because a reference had no meaning.

## What

- **A reference is a hash.** `Wire.Blake3.hash` is Blake3 written in Lean from its specification. A reference to a stored piece is the 32-byte hash of that piece's bytes.
- **A piece has a byte form.** A number is itself. An empty list is `[]`. A pair is `[0, head, tail]`. A function is `[1, body, captured]`, with `body` the quoted program of its code. A reference is a 32-byte CBOR byte string. The reader and writer gain byte strings for this; data still has none, and reading data refuses one.
- **Saving is cutting by size.** `Wire.save` cuts a value from the leaves up. A part whose bytes pass 256 is stored under its hash and replaced by its reference. A part that is already a reference is left alone. A long list becomes a chain of stored runs.
- **A session runs one turn against a store** (`Surface.Keep`). It runs the lazy machine. When a step needs a piece the session does not hold, it stops and names the piece; the caller supplies the bytes and it carries on from where it stopped. The session checks the bytes against the name. When the turn ends in a request, the waiting program is saved and its root is reported.
- **The host keeps a program in a directory.** `keep <store-dir> start <program-file>` runs the first turn. `keep <store-dir> answer <root> <answer-file>` runs the next from a root. Each stored piece is one file, named by its hash in hex. The host reads the files the kernel asks for and writes the files the kernel hands back. It does not read, hash or name a piece.

## What this shows

From `host/check.sh`, on `examples/keep.hom`, which builds a list of 2000 numbers and then asks twice:

- The first turn stores 48 pieces.
- The second turn, in a new process, fetches 3 of them and writes 3 new ones. The list is not read and not written again.
- The third turn fetches all 48 and prints what `ask` prints for the whole run.
- The first root is answered a second time with a different number. Both runs finish, and the second adds 3 pieces: the two runs share the list.
- With one piece file moved away the command exits 3 and writes nothing. With the file back, the same turn runs.
- A piece file with a byte added is refused by the kernel.

Storing by content also removes the duplication the state-store check had. The interpreter-twice state after 40 steps, cut at every value, is 168,796 saves and 774 distinct pieces.

## What is proved, and what is tested

Nothing new is proved. Already proved, and what this rests on (`kernel/StoreContract.lean`): where the cuts go cannot change what a program computes; a missing piece is a pause; a turn from a stored continuation is a turn of the machine. Those hold for every kind of reference, so they hold for hashes.

Assumed: two different pieces do not share a hash (D5). Given that, a reference names one piece for ever, which is the store's one assumption.

Tested (`kernel/KeepCheck.lean`, `host/check.sh`):

- Blake3 gives the 32-byte hash of each of the 22 official test vectors that ship in Zig's standard library, from 0 to 102,400 bytes.
- Eight programs are stopped at three points and saved, cut at 256 bytes and at every value. Every stored piece is named by its hash and reads back to the same bytes, and the lazy machine continues from the stored pieces to the plain machine's result.
- A number larger than the size is stored on its own, and cutting at 0 stores every part.
- A result that sits behind 70 references is found.
- Three turns, each a new session over the pieces the last one left, give what one run against both answers gives.
- The host scenarios above.

Not proved and worth saying: the session that joins the machine runs (`Surface.Keep.advance`) repeats the logic of `Reflect.driveRun` for one turn, on the lazy machine. `driveRun` has theorems; `advance` is tested against it.

## Design notes

- **The kernel owns every name.** A file name is text the kernel produced, and the kernel checks each piece it is given against the name it asked for. A host that supplies wrong bytes gets a refusal, not a wrong answer.
- **The session is a Lean value the host holds between calls.** Lean's exported functions use up their arguments, so the host calls `kernel_retain` before each call that must leave the session usable.
- **A missing piece is not an outcome.** It is exit 3 from the host, with nothing written. This is the pause of the state store, at a process boundary.
- **Copy-on-write is not a mechanism.** An unread part of the state is still a reference when the turn ends, so saving passes it by. A part that was read and not changed has the bytes it had, so it gets the name it had.
- **"wrote" counts pieces handed back, not new files.** The kernel does not know what the directory already holds. A turn run twice hands back the same pieces under the same names.
- **Pieces are written before the root is printed.** A crash between leaves extra files and no root, which is harmless. Files are not written atomically.
- **Nothing is deleted.** Every root ever printed stays answerable. Which pieces no kept root reaches is the substrate's question.

## Limits

- **A function's code is stored inside its piece.** Two functions with the same code store it twice, and such pieces are about 1.7 KB in the interpreter's state. Bead filed.
- **Saving walks a value as a tree.** A value held in two places is encoded twice before the store holds it once. Bead filed.
- **Fetching a whole value re-walks it after each piece arrives.**
- **Only a waiting program is saved.** A turn that runs out of steps is not kept; there is no byte form for a whole machine state yet.
- **`ask` is unchanged** and still replays from the start.
- **The hash is slow next to a native one.** No measurement yet. `homoiconic-q59.20` records the intention to let Zig supply it.

## Not in this change

Signatures and attestations, the event log (P13 as a fold, P14), the network, garbage collection, a store shared between machines.

## User journey & surfaces

Command line only.

```
mkdir store
host/out/keep store start examples/keep.hom      # asked: [1], root: a399…
echo 20 > a.hom
host/out/keep store answer a399… a.hom           # asked: [2, 20], root: 5664…
echo 22 > b.hom
host/out/keep store answer 5664… b.hom           # [2000, 42]
```

## Changelog

- 2026-11-12: opened and built.
- 2026-11-12: review (send-back, two fixes). A turn whose result sat behind a long chain of references ended with no text; references are now followed without a limit, and a turn that does not settle says so. Numbers and empty lists are now cut by size as everything else is. The sharing figure changed with that. Review in `reviews/`.
