# add-wire-bytes

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `add-state-store` (folded, `def0b92`). Vision: `add-verifiable-network-vision`, decisions D7 and D8, obligation P4 (assumed and tested, by decision). Bead: `homoiconic-q59.12`. Authority: the user's roadmap node, and "please continue" on 2026-11-11 after the state store folded.

## Why

A program exists as text and as a Lean value. A value and a waiting program exist only in memory. Nothing can be written to a file, sent, or hashed, because nothing has a byte form. The state store needs one to leave memory, and so does everything after it on the roadmap.

## What

- **One byte form for data.** `Wire.write : Data → ByteArray` and `Wire.read : ByteArray → Except String Data`, for the part of dCBOR that `Data` has: numbers and arrays. The writer is defined for every value whose lengths fit CBOR (below 2^64 items in an array, below 2^64 bytes in a number). The reader is strict: it accepts the bytes the writer produces and refuses every other spelling, so a value has one byte form.
- **A program's bytes are the bytes of its quoted form.** `reify` already gives a program as data (D8). `Wire.unreify` reads it back and refuses data that is no program's form. The identity function is the three bytes `82 01 00`.
- **A machine value has a byte form.** Data is `[0, d]`. A function is `[1, body, captured]`, where `body` is the quoted program of the function's code and `captured` is the array of the values it holds. A waiting program is a function value, so it has a byte form too. Code has one form on the wire: the program.
- **The host runs a program given as bytes.** `run --bytes <file>` prints what `run` prints for the source. A new command `bytes <program-file>` writes a program's byte form to standard output; the kernel makes the bytes.

## The format

| Value | Bytes |
|---|---|
| A number below 2^64 | A CBOR unsigned integer (major type 0) in the shortest form that holds it |
| A number of 2^64 or more | Tag 2, then a byte string of the number's bytes, most significant first, with no leading zero |
| An array | A definite-length CBOR array (major type 4), its length in the shortest form, then its items |

Refused by the reader: a number or length in a longer form than it needs; an indefinite length; bytes after the value; a value cut short; a bignum that has a leading zero or fits an unsigned integer; every other kind of CBOR value (negative numbers, byte strings on their own, text, maps, other tags, simple values, floats).

Numbers in the language have no upper limit, and the factorial example already prints one above 2^64. dCBOR's numeric rules (draft-mcnally-deterministic-cbor-18, §2.5) cover 64-bit numbers and leave tagged items outside them; they neither define nor forbid a larger integer. Tag 2 with a minimal byte string is CBOR's preferred serialization of a large positive integer (RFC 8949 §3.4.3), and requiring that it be used only when the plain form cannot hold the number keeps one form for each value. Which numbers are written with the tag is this project's rule, not dCBOR's. identikey-protocol has no value of this kind to compare with.

## What is proved, and what is tested

Proved: `unreify (reify t) = some t` for every program `t` (`Wire.unreify_reify`, Lean's standard axioms). Reading a program's data form gives the program back.

Tested, not proved, by decision D7 (`kernel/WireCheck.lean`, run by `host/check.sh`):

- The writer gives the RFC 8949 appendix A bytes for each example there that is a number or an array, and the reader gives the value back. Each width is tested at both edges.
- Twenty-six kinds of bytes that are not the one form are refused.
- Every string of one or two bytes is either refused or is exactly what the writer gives for the value read.
- Eleven programs are written, read back, and run from their bytes, with the result the source gives. Each result value is written and read back unchanged.
- A waiting run is written as bytes, read back, and continued to its result.
- Data that is no program's form is refused.
- A function whose code is not a compiled program has no byte form.
- A program whose byte form is larger than the host command's first buffer is written in full.

Not tested: that two different values never share a byte form. It follows from the round trip (`read (write d) = d`), which is tested on examples and not proved.

## The identikey fixtures

The roadmap node carried the hypothesis that a Lean reader and writer would reproduce the identikey-protocol fixtures byte for byte. It cannot be checked in this change. Those fixtures (`crates/identikey-log/tests/fixtures`) are Gordian envelopes: maps, text and byte strings, none of which `Data` has. The comparison used here is RFC 8949's own examples. The hypothesis stays open until `Data` gains byte strings and the log op is read (stage 5).

## Design notes

- **The wire format is outside the language.** `Wire` is its own library. No definition or theorem in `Reflect` mentions bytes.
- **A function's code travels as a program.** A function value holds compiled code. Its byte form holds the program that code was compiled from (`decompile`), and reading compiles it again. `decompile (compile t) = some t` is already proved. `decompile` also reads code that no compilation gives, by dropping its checks, so the writer compiles the program again and compares: a function whose code is not exactly the compilation of a program has no byte form. No compiled program makes such a value. The claims about function values are for values whose code, at every depth, is compiled.
- **The reader keeps arrays on a list, not the call stack,** and reserves nothing for a length before its items arrive, so a short input that claims a huge array is refused when the bytes run out.
- **`run --bytes` exits 0 on bad bytes,** as `run` does on a syntax error: the answer is the kernel's text. `bytes` exits 1 on a syntax error, because its standard output is for the byte form alone.

## Not in this change

- The byte form of a piece that holds references, and so the store on disk. A reference needs a hash, and the hash needs a decision about where it is computed.
- Hashing (P5), signatures, the event log, the network.
- Byte strings, maps or text in `Data`.
- The `ask` command keeping a waiting program between calls. The byte form it needs is here; the command is not changed.

## User journey & surfaces

Command line only. `host/out/bytes program.hom > program.bytes`, then `host/out/run --bytes program.bytes` prints what `host/out/run program.hom` prints.

## Changelog

- 2026-11-11: opened and built.
- 2026-11-11: review (send-back, two fixes). The writer now refuses a function whose code is not a compiled program; before, two such values could share a form. The length limit of CBOR is stated. dCBOR revision named. A large byte form added to the host check. Review in `reviews/`.
