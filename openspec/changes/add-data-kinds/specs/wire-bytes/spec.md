## MODIFIED Requirements

### Requirement: A data value has one byte form
<!-- base: d59ff8ab25b6f8c404b492bfeda0f8f4e85e3c1e openspec/specs/wire-bytes/spec.md -->

The kernel SHALL provide a writer from data to bytes, for every data value in which each array has fewer than 2^64 items, each number fewer than 2^64 bytes and each text fewer than 2^64 bytes, and a reader from bytes to data. A number below 2^64 SHALL be written as a CBOR unsigned integer in the shortest form that holds it. A number of 2^64 or more SHALL be written as CBOR tag 2 over a byte string of its bytes, most significant first, with no leading zero. An array SHALL be written as a definite-length CBOR array with its length in the shortest form. A text SHALL be written as a definite-length CBOR text string, its length in bytes in the shortest form, followed by its UTF-8. A name SHALL be written as CBOR tag 39 over its number in the form a number has. Text SHALL NOT be normalised: two different sequences of code points are two texts with two byte forms. Tag 2 for large numbers, tag 39 for names and text without normalisation are this project's rules, not dCBOR's. The reader SHALL refuse a number or length in a longer form than it needs, an indefinite length, bytes after the value, a value cut short, a bignum with a leading zero or one that fits an unsigned integer, a text that is not valid UTF-8, tag 39 over anything but a number, every other tag, and every kind of CBOR value other than these five. The reader and writer are tested, not proved.

#### Scenario: The standard's examples

- GIVEN each example in RFC 8949 appendix A that is an unsigned number, a definite-length text string, or an array of them
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

#### Scenario: A name

- GIVEN the name with number 3
- WHEN it is written
- THEN the bytes are `d8 27 03`, and reading them gives the name and not the number 3

#### Scenario: Text that is not UTF-8 is refused

- GIVEN the bytes `61 ff`, `62 c0 80` and `63 ed a0 80`
- WHEN each is read
- THEN the reader refuses it

#### Scenario: A tag over the wrong thing is refused

- GIVEN the bytes `d8 27 80`, tag 39 over an empty array, and `d8 28 03`, tag 40 over 3
- WHEN each is read
- THEN the reader refuses it

### Requirement: A piece has a byte form
<!-- base: d59ff8ab25b6f8c404b492bfeda0f8f4e85e3c1e openspec/specs/wire-bytes/spec.md -->

The reader and writer SHALL handle a definite-length CBOR byte string, with its length in the shortest form. Reading data SHALL refuse a byte string anywhere in it. A piece SHALL be written as follows: a number as itself; a text as the text; a name as the name; an empty list as an empty array; a pair as `[0, head, tail]`; a function as `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from; a reference as a byte string of 32 bytes. A function whose code is not exactly the compilation of a program SHALL have no byte form. A byte string of another length SHALL NOT be read as a piece. A text of any length, 32 bytes among them, SHALL NOT be read as a reference, and the byte string inside a large number SHALL NOT be read as one.

#### Scenario: A stored piece reads back

- GIVEN a machine state saved into pieces
- WHEN each piece's bytes are read and written again
- THEN the bytes are the same, and the piece's name is the hash of them

#### Scenario: A text of 32 bytes is not a reference

- GIVEN a piece that is a text of 32 ASCII characters
- WHEN its bytes are written and read as a piece
- THEN the bytes begin `78 20` and the piece read is that text

## ADDED Requirements

### Requirement: A text is stored whole

Saving SHALL treat a text as it treats a number: a text whose byte form is larger than the given size SHALL be stored under its hash as one piece and replaced by its reference, and a smaller one SHALL be left in place. Saving SHALL NOT cut a text into parts.

#### Scenario: A long text is one piece

- GIVEN a waiting program that holds a text of 1,000 characters, saved with cuts at 256 bytes
- WHEN the pieces are listed
- THEN exactly one of them is that text, and its next turn, which does not look at the text, is not supplied it
