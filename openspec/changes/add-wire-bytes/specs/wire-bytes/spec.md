# wire-bytes

## ADDED Requirements

### Requirement: A data value has one byte form

The kernel SHALL provide a writer from data to bytes that is defined for every data value, and a reader from bytes to data. A number below 2^64 SHALL be written as a CBOR unsigned integer in the shortest form that holds it. A number of 2^64 or more SHALL be written as CBOR tag 2 over a byte string of its bytes, most significant first, with no leading zero. An array SHALL be written as a definite-length CBOR array with its length in the shortest form. The reader SHALL refuse a number or length in a longer form than it needs, an indefinite length, bytes after the value, a value cut short, a bignum with a leading zero or one that fits an unsigned integer, and every kind of CBOR value other than these three. The reader and writer are tested, not proved.

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

A machine value that is data `d` SHALL have the data form `[0, d]`. A function value SHALL have the data form `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from and `captured` is the array of the forms of the values it holds. Reading SHALL compile `body`. A value written, read and written again SHALL give the same bytes.

#### Scenario: A waiting run is kept as bytes

- GIVEN a program that has asked twice and been answered once
- WHEN the waiting function is written as bytes, read back, and resumed with the second answer
- THEN it gives the result the uninterrupted run gives
