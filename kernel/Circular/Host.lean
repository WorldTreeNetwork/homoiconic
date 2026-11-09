import Circular.Semantics

namespace Circular.Host

private def whitespace (c : UInt8) : Bool :=
  c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12

private def skipSpace : List UInt8 → List UInt8
  | c :: cs => if whitespace c then skipSpace cs else c :: cs
  | [] => []

private def digit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

private def decimal (acc : Nat) : List UInt8 → Nat × List UInt8
  | c :: cs =>
    if digit c then decimal (acc * 10 + (c.toNat - 48)) cs
    else (acc, c :: cs)
  | [] => (acc, [])

/-- The text grammar has variables, lambdas and binary applications, but no quote.
The input length bounds nesting, independently of evaluation fuel. -/
private def parseTerm : Nat → List UInt8 → Option (Term × List UInt8)
  | 0, _ => none
  | n + 1, raw =>
    match skipSpace raw with
    | 91 :: rest => do -- [term]
      let (body, rest) ← parseTerm n rest
      match skipSpace rest with
      | 93 :: rest => some (.lam body, rest)
      | _ => none
    | 40 :: rest => do -- (term term)
      let (fn, rest) ← parseTerm n rest
      let (arg, rest) ← parseTerm n rest
      match skipSpace rest with
      | 41 :: rest => some (.app fn arg, rest)
      | _ => none
    | c :: cs =>
      if digit c then
        let (i, rest) := decimal 0 (c :: cs)
        some (.var i, rest)
      else none
    | [] => none

def parseProgram (bytes : ByteArray) : Option Term := do
  let (term, rest) ← parseTerm (bytes.size + 1) bytes.data.toList
  if (skipSpace rest).isEmpty then some term else none

/-- One finite derivation-height budget for every host call. -/
def evaluationFuel : Nat := 64

def resultCode : Option Outcome → UInt32
  | some (.value _) => 0
  | some (.unbound i) => 2 * i.toUInt32 + 1
  | none => 4294967295

def runBytes (bytes : ByteArray) : UInt32 :=
  match parseProgram bytes with
  | some term => resultCode (evalFuel evaluationFuel [] term)
  | none => 4294967295

/-- Native-only byte copy. The caller lends `length` readable bytes for this call. -/
@[extern "kernel_copy_bytes"]
private unsafe def copyBytes (_address _length : USize) : ByteArray :=
  panic! "kernel_copy_bytes requires the native FFI bridge"

/-- C ABI: borrowed pointer and byte length in, one unboxed result code out. -/
@[export kernel_run]
unsafe def kernelRun (address length : USize) : UInt32 :=
  runBytes (copyBytes address length)

end Circular.Host
