# wire-bytes

What is built: one byte form for data, for the part of dCBOR that `Data` has, numbers and arrays. A program's bytes are the bytes of its quoted form, and a machine value, a waiting program among them, has a byte form too. The reader and writer are in `kernel/Wire/Cbor.lean`, the byte forms of a program and a machine value in `kernel/Wire/Form.lean`, and the tests in `kernel/WireCheck.lean`, which `host/check.sh` runs. `Wire` is its own library; no definition or theorem in `Reflect` mentions bytes. The reader and writer are tested, not proved, by decision D7 of `add-verifiable-network-vision`. One statement is proved: `Reflect.unreify_reify`. It and `unreify`, which reads a program back from its data form, are in `kernel/Reflect/Syntax.lean`, beside `reify`. Numbers of 2^64 and above are written with CBOR tag 2; that is this project's rule, not dCBOR's. A piece of stored state (`openspec/specs/state-store/spec.md`) has a byte form too, and a reference to it is the 32-byte Blake3 hash of those bytes. Blake3 is written in Lean in `kernel/Wire/Blake3.lean`; the byte form of a piece and saving by cutting are in `kernel/Wire/Piece.lean`. The reader and writer also handle byte strings, for references; reading data refuses one. `kernel/KeepCheck.lean`, which `host/check.sh` runs, tests the hash against the official vectors and saves real runs. The hash, the byte form of a piece and saving are tested, not proved. That two different pieces do not share a hash is assumed (D5).

## Purpose

State the byte form of a data value, of a program, of a machine value and of a piece of stored state, how a reference is made, how a value is cut for saving, what the reader refuses, and what is proved and what is tested about them. This spec does not cover the event log, signatures or the network. The host commands that use the byte form are in `openspec/specs/zig-host/spec.md`.

## Requirements

### Requirement: A data value has one byte form

The kernel SHALL provide a writer from data to bytes, for every data value in which each array has fewer than 2^64 items and each number fewer than 2^64 bytes, and a reader from bytes to data. A number below 2^64 SHALL be written as a CBOR unsigned integer in the shortest form that holds it. A number of 2^64 or more SHALL be written as CBOR tag 2 over a byte string of its bytes, most significant first, with no leading zero. An array SHALL be written as a definite-length CBOR array with its length in the shortest form. The reader SHALL refuse a number or length in a longer form than it needs, an indefinite length, bytes after the value, a value cut short, a bignum with a leading zero or one that fits an unsigned integer, and every kind of CBOR value other than these three. The reader and writer are tested, not proved.

#### Scenario: The standard's examples

- GIVEN each example in RFC 8949 appendix A that is an unsigned number or an array of them
- WHEN the value is written
- THEN the bytes are the standard's, and reading them gives the value

#### Scenario: Another spelling is refused

- GIVEN the bytes `18 17`, which spell 23 in two bytes
- WHEN they are read
- THEN the reader refuses them

#### Scenario: Short strings have one reading

- GIVEN every string of one or two bytes
- WHEN each is read
- THEN it is refused, or it is exactly the bytes the writer gives for the value read

### Requirement: A program's bytes are the bytes of its quoted form

The byte form of a program SHALL be the byte form of the data value `reify` gives it. The kernel SHALL read a program back from that data and SHALL refuse data that is the form of no program. Reading the data form of a program SHALL give that program; this is proved, with Lean's standard axioms only.

#### Scenario: The identity function

- GIVEN the program `fn x -> x`
- WHEN its byte form is written
- THEN it is the three bytes `82 01 00`

#### Scenario: A program run from its bytes

- GIVEN a program written as bytes and read back
- WHEN it is run
- THEN it gives what the program gives

#### Scenario: Data that is no program

- GIVEN the byte `80`, an empty array
- WHEN it is read as a program
- THEN it is refused

### Requirement: A machine value has a byte form

A machine value that is data `d` SHALL have the data form `[0, d]`. A function value SHALL have the data form `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from and `captured` is the array of the forms of the values it holds. Reading SHALL compile `body`. A function whose code is not exactly the compilation of a program SHALL have no byte form. A value written, read and written again SHALL give the same bytes.

#### Scenario: A waiting run is kept as bytes

- GIVEN a program that has asked twice and been answered once
- WHEN the waiting function is written as bytes, read back, and resumed with the second answer
- THEN it gives the result the uninterrupted run gives

#### Scenario: Code that no program compiles to

- GIVEN a function value whose code is a literal followed by a check that no compilation puts there
- WHEN its byte form is asked for
- THEN there is none

### Requirement: A reference is the Blake3 hash of a piece's bytes

The kernel SHALL define the 32-byte Blake3 hash in Lean. A reference to a stored piece SHALL be the hash of that piece's byte form. The definition is tested against the official test vectors and is not proved. That two different pieces do not share a hash is assumed.

#### Scenario: The official vectors

- GIVEN each official Blake3 test input, from 0 to 102,400 bytes
- WHEN it is hashed
- THEN the result is the first 32 bytes of the published output

### Requirement: A piece has a byte form

The reader and writer SHALL handle a definite-length CBOR byte string, with its length in the shortest form. Reading data SHALL refuse a byte string anywhere in it. A piece SHALL be written as follows: a number as itself; an empty list as an empty array; a pair as `[0, head, tail]`; a function as `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from; a reference as a byte string of 32 bytes. A function whose code is not exactly the compilation of a program SHALL have no byte form. A byte string of another length SHALL NOT be read as a piece.

#### Scenario: A stored piece reads back

- GIVEN a machine state saved into pieces
- WHEN each piece's bytes are read and written again
- THEN the bytes are the same, and the piece's name is the hash of them

### Requirement: Saving cuts a value by size

Saving SHALL cut a value from the leaves up, store each part whose byte form is larger than a given size under its hash, and replace it by its reference. It SHALL leave a part that is already a reference as it is. It SHALL store the top of the value whatever its size, and give its reference as the root.

#### Scenario: A run continues from saved pieces

- GIVEN a program stopped after some steps and saved, cut at 256 bytes or at every value
- WHEN the lazy machine continues from the stored pieces
- THEN it halts with what the plain machine halts with
