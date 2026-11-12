# wire-bytes

## ADDED Requirements

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
