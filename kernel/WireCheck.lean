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
def txt (s : String) : Data := .text s.toList
def rep (k : Nat) (h : String) : String := String.join (List.replicate k h)

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
    (reify identity, "820100"), (reify (.app identity identity), "8300820100820100"),
    -- A name: tag 39 over its number, in the form the number has.
    (.name 3, "d82703"), (.name 0, "d82700"), (.name 23, "d82717"), (.name 24, "d8271818"),
    (.name 18446744073709551615, "d8271bffffffffffffffff"),
    (.name 18446744073709551616, "d827c249010000000000000000"),
    (.arr [.nat 1, .name 3], "8201d82703"), (.arr [.arr [.arr [.nat 2, .name 3]]], "81818202d82703"),
    -- The code of a literal of a name, and a send on it.
    (reify (.lit (.name 3)), "8202d82703"), (.arr [.nat 1, .name 0, .nat 7], "8301d8270007"),
    -- Text: the text strings of RFC 8949, appendix A. The length is in bytes.
    (txt "", "60"), (txt "a", "6161"), (txt "IETF", "6449455446"), (txt "\"\\", "62225c"),
    (txt "ü", "62c3bc"), (txt "水", "63e6b0b4"), (txt "𐅑", "64f0908591"),
    -- An array of them, and text beside the other kinds.
    (.arr [txt "a", txt "ü", txt ""], "83616162c3bc60"),
    (.arr [.nat 1, txt "a", .name 3, .arr [txt "水"]], "84016161d8270381" ++ "63e6b0b4"),
    -- The head at its edges: 23 and 24 bytes, and 256.
    (txt (String.ofList (List.replicate 23 'x')), "77" ++ rep 23 "78"),
    (txt (String.ofList (List.replicate 24 'x')), "7818" ++ rep 24 "78"),
    (txt (String.ofList (List.replicate 256 'x')), "790100" ++ rep 256 "78"),
    -- Not normalised: é as one scalar value and as e with a combining accent
    -- are two texts with two byte forms.
    (txt "\u00e9", "62c3a9"), (txt "e\u0301", "6365cc81"),
    -- The first and last scalar values, and the ones on each side of the surrogates.
    (.text [Char.ofNat 0], "6100"), (.text [Char.ofNat 0xd7ff], "63ed9fbf"),
    (.text [Char.ofNat 0xe000], "63ee8080"), (.text [Char.ofNat 0x10ffff], "64f48fbfbf"),
    -- The code of a string literal.
    (reify (.lit (txt "a")), "82026161") ]

#eval do
  for (d, h) in vectors do
    let wrote := hex (write d)
    IO.println (line (wrote == h && readsAs (unhex h) d) s!"vector {h}")

-- A name's bytes read as the name, and not as its number; the number's do not
-- read as the name.
#eval IO.println (line
  (readsAs (unhex "d82703") (.name 3) && !readsAs (unhex "d82703") (.nat 3)
    && readsAs (unhex "03") (.nat 3) && !readsAs (unhex "03") (.name 3))
  "d82703 reads as the name #3, not the number 3")

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
    ("a text of one byte that is not UTF-8", "61ff"),
    ("a text with an overlong form", "62c080"),
    ("a text with a surrogate", "63eda080"),
    ("a text with a low surrogate", "63edb080"),
    ("a text past U+10FFFF", "64f4908080"),
    ("a text that is a lone continuation byte", "6180"),
    ("a text whose last character is cut short", "6261c3"),
    ("a text with an overlong three-byte form", "63e08080"),
    ("an indefinite-length text", "7f6161ff"),
    ("an indefinite-length text, empty", "7fff"),
    ("a text length in a longer form", "780161"),
    ("a text cut short", "6261"),
    ("a text length with no bytes", "7bffffffffffffffff"),
    ("a text, then more bytes", "616100"),
    ("a map", "a0"),
    ("a date tag", "c100"),
    ("tag 39 over an empty array", "d82780"),
    ("tag 39 over an array of a number", "d8278103"),
    ("tag 39 over a text", "d8276161"),
    ("tag 39 over a byte string", "d8274103"),
    ("tag 39 over a number in a longer form", "d8271803"),
    ("tag 39 over a number in two bytes that fits one", "d8271900ff"),
    ("tag 39 over tag 39", "d827d82703"),
    ("tag 39 in a three-byte head", "d9002703"),
    ("tag 39 in a five-byte head", "da0000002703"),
    ("tag 39 over tag 2 of a number below 2^64", "d827c248ffffffffffffffff"),
    ("tag 39 over a bignum with a leading zero", "d827c24a00010000000000000000"),
    ("tag 39 over a bignum cut short", "d827c2490100"),
    ("tag 39 over tag 2 over a number", "d827c203"),
    ("tag 39 over a negative number", "d82720"),
    ("tag 39 over false", "d827f4"),
    ("tag 39 with nothing after it", "d827"),
    ("tag 39 over a number, then more bytes", "d8270300"),
    ("tag 40 over a number", "d82803"),
    ("tag 38 over a number", "d82603"),
    ("tag 2 in a two-byte head", "d80249010000000000000000"),
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

/-- What a reading gives, as text: the bytes it is written as again, or the
    refusal's words. -/
def outcome : Except String Item → String
  | .ok i => "ok " ++ hex (writeItem i)
  | .error e => "error " ++ e

/-- `readItem` scans before it builds. The scan refuses what the builder
    refuses, with the same words: for every string of up to two bytes, every
    refused vector, and arrays nested and cut short, `readItem` gives what
    the builder alone (`readGo`) gives. -/
def sameAsBuilder : String :=
  let one := (List.range 256).map fun a => ByteArray.empty.push a.toUInt8
  let two := (List.range 65536).map fun a =>
    (ByteArray.empty.push (a / 256).toUInt8).push (a % 256).toUInt8
  let more := (refused.map fun (_, h) => unhex h) ++
    [unhex (rep 5 "81" ++ "00"), unhex (rep 5 "81"), unhex (rep 3 "82" ++ "00"),
     unhex ("8301" ++ rep 3 "81" ++ "0200"), unhex ("820181" ++ "1817"),
     unhex (rep 4 "81" ++ "61ff"), unhex ("8200" ++ rep 3 "81" ++ "00" ++ "00")]
  let all := one ++ two ++ more
  let differ := all.filter fun b => outcome (readItem b) != outcome (readGo b (b.size + 1) 0 [])
  line differ.isEmpty s!"of {all.length} strings, the scan and the builder agree on every one, refusals word for word ({differ.length} differ)"

#eval IO.println sameAsBuilder

-- Arrays opened and never closed: each byte `81` opens an array of one. The
-- scan refuses them before a frame is made, in the words for bytes cut
-- short; closed by one number they are a value and are read.
#eval do
  let k := 200000
  let deep := ByteArray.mk (Array.replicate k 0x81)
  let cut := match read deep with
    | .error e => e == "the bytes end inside a value"
    | .ok _ => false
  let closed := match readItem (deep.push 0) with
    | .ok i => (writeItem i).size == k + 1
    | .error _ => false
  IO.println (line (cut && closed)
    s!"{k} arrays opened and not closed are refused as bytes cut short; closed by a number they are read")

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
    ("a name in the program and in the result", .cons (.lit (.name 3)) (.cons (.succ (.lit (.name 3))) emptyArr)),
    ("a function that captured a name", .app (.lam (.lam (.cons (.var 1) emptyArr))) (.lit (.name 18446744073709551616))),
    ("a string literal taken apart", .dcase (.lit (txt "hé")) (n 0) (n 0) (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr))),
    ("a string literal under the interpreter", level 1 (.dcase (.lit (txt "hé")) (n 0) (n 0) (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr)))),
    ("text made from code points", .prim (n 7) (.cons (n 104) (.prim (n 8) (.lit (txt "i 水"))))),
    ("a function that captured a text", .app (.lam (.lam (.cons (.var 1) emptyArr))) (.lit (txt "h\\i\n"))),
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

-- Code that is not the compilation of a program reads back as a program
-- (`decompile` drops its checks), so a function holding it has no byte form.
#eval IO.println (line
  ((valueBytes (.closure (.literal (.nat 0) (.checkFun .done)) [])).isNone
    && (valueBytes (.closure (.literal (.nat 0) .done) [])).isSome)
  "a function whose code is not a compiled program has no byte form")

-- The name piece: a name is written as the name, and read back as it.
#eval do
  let b := pieceBytes (.cons (.name 3) (.cons (.nat 3) .nil) : P Ref)
  let leaf := (pieceBytes (.name 3 : P Ref)).map hex
  let back := match b with
    | some b => (match readPiece b with
        | .ok (.cons (.name 3) (.cons (.nat 3) .nil)) => hex b == "8300d82703830003" ++ "80"
        | .ok _ => false
        | .error _ => false)
    | none => false
  IO.println (line (leaf == some "d82703" && back) s!"the name piece is {leaf.getD "none"}, and a pair that holds it reads back")

-- The text piece: a text is written as the text. One of 32 bytes is not read
-- as a reference, and a byte string of 32 bytes is.
#eval do
  let t32 : List Char := List.replicate 32 'r'
  let b := pieceBytes (.text t32 : P Ref)
  let leaf := (pieceBytes (.text "hé".toList : P Ref)).map hex
  let back := match b with
    | some b => (match readPiece b with
        | .ok (.text t) => t == t32 && (hex b).take 4 == "7820".toSlice && b.size == 34
        | _ => false)
    | none => false
  let asRef := match readPiece (unhex ("5820" ++ rep 32 "72")) with
    | .ok (.ref r) => r.size == 32
    | _ => false
  let pair := match pieceBytes (.cons (.text "a".toList) (.cons (.nat 97) .nil) : P Ref) with
    | some b => (match readPiece b with
        | .ok (.cons (.text ['a']) (.cons (.nat 97) .nil)) => hex b == "83006161830018618" ++ "0"
        | _ => false)
    | none => false
  IO.println (line (leaf == some "6368c3a9" && back && asRef && pair)
    s!"the text piece is {leaf.getD "none"}; a text of 32 bytes begins 7820 and reads back as the text, and 32 bytes in a byte string as a reference")

/-- Data that is no program's form is refused, not guessed at. -/
def notPrograms : List (String × Data) :=
  [ ("an empty array", .arr []), ("an unknown tag", .arr [.nat 7, .nat 0]),
    ("an application with one part", .arr [.nat 0, .nat 0]),
    ("a tag that is an array", .arr [.arr [], .nat 0]),
    ("a name", .name 0), ("a name where a variable's index goes", .arr [.name 0, .nat 0]),
    ("a name as a tag", .arr [.name 2, .nat 0]),
    ("a text", txt "a"), ("the empty text", txt ""),
    ("a text where a variable's index goes", .arr [txt "", .nat 0]),
    ("a text as a tag", .arr [txt "\u0002", .nat 0]) ]

#eval do
  for (what, d) in notPrograms do
    let ok := match readProgram (write d) with
      | .ok _ => false
      | .error _ => true
    IO.println (line ok s!"not a program: {what}")

/-- Proved, not tested: reading a program's data form gives the program. -/
example : ∀ t : Term, unreify (reify t) = some t := unreify_reify
#print axioms Reflect.unreify_reify
