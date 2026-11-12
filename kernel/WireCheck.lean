import Reflect.Arith
import Reflect
import Wire
open Reflect Wire

/-! Tests the byte form. The vectors are from RFC 8949, appendix A, for the
    kinds of value `Data` has. Each line that starts with FAIL fails the check. -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!
def hex (b : ByteArray) : String :=
  String.ofList (b.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def unhexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87
def unhex (s : String) : ByteArray :=
  let rec go : List Char → ByteArray → ByteArray
    | a :: b :: rest, out => go rest (out.push (unhexDigit a * 16 + unhexDigit b).toUInt8)
    | _, out => out
  go s.toList ByteArray.empty

def line (ok : Bool) (what : String) : String := s!"{if ok then "ok  " else "FAIL"} {what}"

def readsAs (b : ByteArray) (d : Data) : Bool :=
  match read b with
  | .ok d' => d' == d
  | .error _ => false

def nums (ns : List Nat) : Data := .arr (ns.map .nat)

def vectors : List (Data × String) :=
  [ (.nat 0, "00"), (.nat 1, "01"), (.nat 10, "0a"), (.nat 23, "17"), (.nat 24, "1818"),
    (.nat 25, "1819"), (.nat 100, "1864"), (.nat 1000, "1903e8"), (.nat 1000000, "1a000f4240"),
    (.nat 1000000000000, "1b000000e8d4a51000"),
    (.nat 18446744073709551615, "1bffffffffffffffff"),
    (.nat 18446744073709551616, "c249010000000000000000"),
    (.arr [], "80"), (nums [1, 2, 3], "83010203"),
    (.arr [.nat 1, nums [2, 3], nums [4, 5]], "8301820203820405"),
    (nums ((List.range 25).map (· + 1)),
      "98190102030405060708090a0b0c0d0e0f101112131415161718181819"),
    -- Each width at its edges.
    (.nat 255, "18ff"), (.nat 256, "190100"), (.nat 65535, "19ffff"), (.nat 65536, "1a00010000"),
    (.nat 4294967295, "1affffffff"), (.nat 4294967296, "1b0000000100000000"),
    -- A program: the identity function, and its application to itself.
    (reify identity, "820100"), (reify (.app identity identity), "8300820100820100") ]

#eval do
  for (d, h) in vectors do
    let wrote := hex (write d)
    IO.println (line (wrote == h && readsAs (unhex h) d) s!"vector {h}")

/-- Bytes that are well-formed CBOR, or nearly, and are not the one form. -/
def refused : List (String × String) :=
  [ ("empty input", ""),
    ("a small number in one extra byte", "1817"),
    ("a number in two bytes that fits one", "1900ff"),
    ("a number in four bytes that fits two", "1a0000ffff"),
    ("a number in eight bytes that fits four", "1b00000000ffffffff"),
    ("an array length in a longer form", "980100"),
    ("an indefinite-length array", "9f0102ff"),
    ("a break alone", "ff"),
    ("bytes after the value", "0000"),
    ("an array with an item missing", "830102"),
    ("an array length with no items", "9bffffffffffffffff"),
    ("a number cut short", "19ff"),
    ("a bignum that fits an unsigned integer", "c248ffffffffffffffff"),
    ("a bignum with a leading zero", "c24a00010000000000000000"),
    ("an empty bignum", "c240"),
    ("a bignum cut short", "c2490100"),
    ("a bignum over a number", "c201"),
    ("a negative bignum", "c349010000000000000000"),
    ("a negative number", "20"),
    ("a byte string", "4101"),
    ("a text string", "6161"),
    ("a map", "a0"),
    ("a date tag", "c100"),
    ("false", "f4"),
    ("null", "f6"),
    ("a float", "f93c00") ]

#eval do
  for (what, h) in refused do
    let ok := match read (unhex h) with
      | .ok _ => false
      | .error _ => true
    IO.println (line ok s!"refused: {what} ({h})")

/-- One form: every string of up to two bytes either is refused or is exactly
    what the writer gives for the value read. -/
def oneForm : String :=
  let one := (List.range 256).map fun a => ByteArray.empty.push a.toUInt8
  let two := (List.range 65536).map fun a =>
    (ByteArray.empty.push (a / 256).toUInt8).push (a % 256).toUInt8
  let all := one ++ two
  let read' := all.filter fun b => match read b with
    | .ok _ => true
    | .error _ => false
  let same := read'.all fun b => match read b with
    | .ok d => hex (write d) == hex b
    | .error _ => false
  line (same && read'.length > 0) s!"of {all.length} strings of one or two bytes, {read'.length} are read, each the writer's own form"

#eval IO.println oneForm

def n (k : Nat) : Term := .lit (.nat k)
def emptyArr : Term := .lit (.arr [])

/-- `ask [1] (fn x -> ask [2, x] (fn y -> add x y))` -/
def askTwice : Term :=
  .app (.app askTerm (.lit (.arr [.nat 1])))
    (.lam (.app (.app askTerm (.cons (n 2) (.cons (.var 0) emptyArr)))
      (.lam (.prim (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr))))))

def programs : List (String × Term) :=
  [ ("identity applied", level 1 (.app identity identity)),
    ("case on array", level 1 (.dcase (.lit (.arr [.nat 4, .nat 5])) (n 0) (n 0) (n 0) (.cons (.var 1) (.var 0)))),
    ("closure over case binder", level 1 (.app (.dcase (n 2) identity (.lam (.var 1)) identity identity) (n 0))),
    ("operation on built operands", level 1 (.prim (n 2) (.cons (.succ (n 5)) (.cons (n 7) emptyArr)))),
    ("function as operand is wrong", level 1 (.prim (n 0) identity)),
    ("unbound variable", level 1 (.app (.var 0) omega)),
    ("builds code and runs it", buildsAndRuns),
    ("a function is the result", .app (.lam (.lam (.cons (.var 1) emptyArr))) (n 7)),
    ("a large number", .prim (n 2) (.cons (n 18446744073709551616) (.cons (n 18446744073709551616) emptyArr))),
    ("asks twice", askTwice),
    ("interpreter twice", level 2 (.succ (.succ (n 5)))) ]

def budget : Nat := 4000000

def shown : State → String
  | .halted w => reprStr w
  | _ => "running"

/-- A value survives its byte form: written, read, and written again gives the
    same bytes, and the value read is the value written. -/
def valueKept (v : MValue) : Bool :=
  match valueBytes v with
  | none => false
  | some b =>
      match readValue b with
      | .error _ => false
      | .ok v' => reprStr v' == reprStr v && (valueBytes v').map hex == some (hex b)

#eval do
  for (name, p) in programs do
    let b := programBytes p
    let back := match readProgram b with
      | .ok q => hex (programBytes q) == hex b && reprStr q == reprStr p
      | .error _ => false
    let direct := runUntil budget (load (compile p))
    let fromBytes := match readProgram b with
      | .ok q => shown (runUntil budget (load (compile q)))
      | .error e => e
    let result := match direct with
      | .halted (.value v) => valueKept v
      | _ => true
    let ok := back && fromBytes == shown direct && shown direct != "running" && result
    IO.println (line ok s!"{name}: {b.size} bytes, read back {back}, run from bytes {fromBytes == shown direct}, result kept {result}")

/-- A waiting run is written as bytes, read back, and continued. -/
def keptRun : String :=
  match converse 100000 askTwice [.nat 20] with
  | (asked, .waiting k) =>
      match valueBytes k with
      | none => "FAIL the waiting program has no byte form"
      | some b =>
          match readValue b with
          | .error e => s!"FAIL the waiting program was not read back: {e}"
          | .ok k' =>
              let got := shown (runUntil 100000 (.running (compile (resumeTerm (.nat 22))) [k'] [] []))
              let ok := got == reprStr (MOutcome.value (.data (.nat 42))) && asked.length == 2 && valueKept k
              line ok s!"waiting run kept in {b.size} bytes, continued with 22: {got}"
  | _ => "FAIL the program did not wait"

#eval IO.println keptRun

/-- Data that is no program's form is refused, not guessed at. -/
def notPrograms : List (String × Data) :=
  [ ("an empty array", .arr []), ("an unknown tag", .arr [.nat 7, .nat 0]),
    ("an application with one part", .arr [.nat 0, .nat 0]),
    ("a tag that is an array", .arr [.arr [], .nat 0]) ]

#eval do
  for (what, d) in notPrograms do
    let ok := match readProgram (write d) with
      | .ok _ => false
      | .error _ => true
    IO.println (line ok s!"not a program: {what}")

/-- Proved, not tested: reading a program's data form gives the program. -/
example : ∀ t : Term, unreify (reify t) = some t := unreify_reify
#print axioms Wire.unreify_reify
