import Circular.Semantics

open Circular

def skip : List Char → List Char
  | ' ' :: cs => skip cs
  | '\n' :: cs => skip cs
  | '\t' :: cs => skip cs
  | cs => cs

def parseNat (acc : Nat) : List Char → Nat × List Char
  | c :: cs =>
    if c.isDigit then
      parseNat (acc * 10 + (c.toNat - '0'.toNat)) cs
    else
      (acc, c :: cs)
  | [] => (acc, [])

/-- `fuel` bounds term nesting. The text is the design grammar. -/
def parseTerm : Nat → List Char → Option (Term × List Char)
  | 0, _ => none
  | n + 1, raw =>
    let cs := skip raw
    match cs with
    | '[' :: rest =>
      match parseTerm n rest with
      | some (body, rest) =>
        match skip rest with
        | ']' :: rest => some (.lam body, rest)
        | _ => none
      | none => none
    | '(' :: rest =>
      match parseTerm n rest with
      | some (fn, rest) =>
        match parseTerm n rest with
        | some (arg, rest) =>
          match skip rest with
          | ')' :: rest => some (.app fn arg, rest)
          | _ => none
        | none => none
      | none => none
    | c :: _ =>
      if c.isDigit then
        let (k, rest) := parseNat 0 cs
        some (.var k, rest)
      else
        none
    | [] => none

def resultCode : Option Outcome → UInt32
  | some (.value _) => 0
  | some (.unbound i) => 2 * i.toUInt32 + 1
  | none => 4294967295

@[export kernel_run]
def kernelRun (program : String) : UInt32 :=
  match parseTerm 64 program.toList with
  | some (term, rest) =>
    match skip rest with
    | [] => resultCode (evalFuel 8 [] term)
    | _ => 4294967295
  | none => 4294967295
