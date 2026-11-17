import Reflect.Arith
import Reflect
import Wire
import Surface
open Reflect Wire

/-! Tests the hash, the byte form of a piece, saving, and a turn run from a
    store. Each line that starts with FAIL fails the check. -/

def line (ok : Bool) (what : String) : String := s!"{if ok then "ok  " else "FAIL"} {what}"
def hex := Surface.Keep.hex

/-- The official Blake3 test vectors: the input of length `n` is the bytes
    `i % 251`, and the hash is the first 32 bytes of the published output.
    Taken from the reference test in Zig's standard library. -/
def input (n : Nat) : ByteArray :=
  (List.range n).foldl (fun b i => b.push (i % 251).toUInt8) ByteArray.empty

def vectors : List (Nat × String) :=
  [ (0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
    (1, "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"),
    (1023, "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"),
    (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
    (1025, "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
    (2048, "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"),
    (2049, "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"),
    (3072, "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"),
    (3073, "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3"),
    (4096, "015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969"),
    (4097, "9b4052b38f1c5fc8b1f9ff7ac7b27cd242487b3d890d15c96a1c25b8aa0fb995"),
    (5120, "9cadc15fed8b5d854562b26a9536d9707cadeda9b143978f319ab34230535833"),
    (5121, "628bd2cb2004694adaab7bbd778a25df25c47b9d4155a55f8fbd79f2fe154cff"),
    (6144, "3e2e5b74e048f3add6d21faab3f83aa44d3b2278afb83b80b3c35164ebeca205"),
    (6145, "f1323a8631446cc50536a9f705ee5cb619424d46887f3c376c695b70e0f0507f"),
    (7168, "61da957ec2499a95d6b8023e2b0e604ec7f6b50e80a9678b89d2628e99ada77a"),
    (7169, "a003fc7a51754a9b3c7fae0367ab3d782dccf28855a03d435f8cfe74605e7817"),
    (8192, "aae792484c8efe4f19e2ca7d371d8c467ffb10748d8a5a1ae579948f718a2a63"),
    (8193, "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b"),
    (16384, "f875d6646de28985646f34ee13be9a576fd515f76b5b0a26bb324735041ddde4"),
    (31744, "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47"),
    (102400, "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085") ]

#eval do
  for (n, h) in vectors do
    IO.println (line (hex (Blake3.hash (input n)) == h) s!"blake3 of {n} bytes")

-- A number or an empty list is cut as anything else is.
#eval do
  let big : P Ref := .cons (.nat (2 ^ 2400)) .nil
  let isRef : P Ref → Bool
    | .ref _ => true
    | _ => false
  let ok := match (cut 256 big).run #[], (cut 0 (.cons (.nat 1) .nil : P Ref)).run #[] with
    | some (.cons h .nil, one), some (top, three) => isRef h && one.size == 1 && isRef top && three.size == 3
    | _, _ => false
  IO.println (line ok "a number over the size is stored on its own, and cutting at 0 stores every part")

/-- The host's part for one session, over a store of pieces by name. -/
def supply (m : Std.HashMap Ref ByteArray) : Nat → Surface.Keep.Session → String
  | 0, _ => "did not finish"
  | fuel + 1, s =>
      match s.need with
      | some r =>
          match m[r]? with
          | some b => supply m fuel (Surface.Keep.give s b)
          | none => "lacks a piece"
      | none => s.text

-- A value behind a long chain of references is still the value. A function
-- that forces the chain and then returns its reference is answered from a root.
#eval do
  let name (p : P Ref) : Ref × ByteArray :=
    match pieceBytes p with
    | some b => (Blake3.hash b, b)
    | none => (ByteArray.empty, ByteArray.empty)
  let first := name (.nat 42)
  let chain := (List.range 70).foldl (fun (acc : List (Ref × ByteArray)) _ =>
    name (.ref (acc.headD first).1) :: acc) [first]
  let top := (chain.headD first).1
  let k := name (.closure (compile (.app (.lam (.var 2)) (.succ (.var 1)))) (.cons (.ref top) .nil))
  let m : Std.HashMap Ref ByteArray := (k :: chain).foldl (fun m (rb : Ref × ByteArray) => m.insert rb.1 rb.2) {}
  let text := supply m 1000 (Surface.Keep.answer (hex k.1) "0".toUTF8 10000)
  IO.println (line (text.startsWith "42\n") s!"a result behind 70 references is found: {(text.splitOn "\n").headD ""}")

abbrev Pieces := Std.HashMap Ref ByteArray

/-- Save every value in a machine state, as `Wire.cut` does for one. -/
def cutState (size : Nat) : PState Ref → Saver (PState Ref)
  | .running c e stk frs => do
      let e' ← cut size e
      let stk' ← stk.mapM (cut size)
      let frs' ← frs.mapM fun f => do
        let fe ← cut size f.env
        pure (⟨f.code, fe⟩ : PFrame Ref)
      pure (.running c e' stk' frs')
  | .halted (.value v) => do
      let v' ← cut size v
      pure (.halted (.value v'))
  | s => pure s

/-- A store that reads each piece from its bytes when it is asked for. -/
def storeOf (m : Pieces) : Store Ref := fun r =>
  match m[r]? with
  | some b =>
      match readPiece b with
      | .ok p => some p
      | .error _ => none
  | none => none

def go (σ : Store Ref) : Nat → PState Ref → LRun Ref
  | 0, s => .at s
  | n + 1, s =>
      match s with
      | .halted _ => .at s
      | .fault => .at s
      | _ =>
          match lstep σ s with
          | .next s' => go σ n s'
          | .needs r => .paused r s

partial def resolve (σ : Store Ref) : P Ref → Option (P Ref)
  | .nat n => some (.nat n)
  | .name n => some (.name n)
  | .text t => some (.text t)
  | .nil => some .nil
  | .cons h t => do
      let h' ← resolve σ h
      let t' ← resolve σ t
      pure (.cons h' t')
  | .closure c e => do
      let e' ← resolve σ e
      pure (.closure c e')
  | .ref r => do
      let p ← σ r
      resolve σ p

def shown (σ : Store Ref) : PState Ref → String
  | .halted (.value v) =>
      match resolve σ v with
      | some p => (pieceBytes p).elim "no byte form" hex
      | none => "unresolved"
  | .halted (.unbound i) => s!"unbound {i}"
  | .halted .wrong => "wrong"
  | .fault => "fault"
  | _ => "running"

def budget : Nat := 4000000

/-- Stop `p` after `n` steps, save the state cut at `size` bytes, check every
    stored piece, and continue from the store. -/
def snapshot (name : String) (p : Term) (n size : Nat) : String :=
  let s := run n (load (compile p))
  let want := shown (fun _ => none) ((runUntil budget s).toP : PState Ref)
  match (cutState size s.toP).run #[] with
  | none => line false s!"{name} after {n} steps: no byte form"
  | some (ps, stored) =>
      let m : Pieces := stored.foldl (fun m rb => m.insert rb.1 rb.2) {}
      -- Each piece is named by its hash and reads back to the same bytes.
      let sound := stored.all fun rb =>
        hex (Blake3.hash rb.2) == hex rb.1 &&
          (match readPiece rb.2 with
           | .ok q => (pieceBytes q).map hex == some (hex rb.2)
           | .error _ => false)
      let got := match go (storeOf m) budget ps with
        | .at t => shown (storeOf m) t
        | .paused _ _ => "paused"
      let most := stored.foldl (fun a rb => max a rb.2.size) 0
      line (sound && got == want && want != "running")
        s!"{name} after {n} steps, cut at {size} bytes: {stored.size} saves, {m.size} pieces, largest {most} bytes"

def n (k : Nat) : Term := .lit (.nat k)
def emptyArr : Term := .lit (.arr [])

def programs : List (String × Term) :=
  [ ("identity applied", level 1 (.app identity identity)),
    ("case on array", level 1 (.dcase (.lit (.arr [.nat 4, .nat 5])) (n 0) (n 0) (n 0) (.cons (.var 1) (.var 0)))),
    ("closure over case binder", level 1 (.app (.dcase (n 2) identity (.lam (.var 1)) identity identity) (n 0))),
    ("operation on built operands", level 1 (.prim (n 2) (.cons (.succ (n 5)) (.cons (n 7) emptyArr)))),
    ("function as operand is wrong", level 1 (.prim (n 0) identity)),
    ("unbound variable", level 1 (.app (.var 0) omega)),
    ("builds code and runs it", buildsAndRuns),
    ("interpreter twice", level 2 (.succ (.succ (n 5)))) ]

#eval do
  for (name, p) in programs do
    for (k, size) in [(0, 256), (40, 0), (40, 256), (300, 256)] do
      IO.println (snapshot name p k size)

/-- The host's part, in memory: supply each piece a session asks for, then
    store what it hands back. `none` when the store lacks a piece. -/
def serve (m : Pieces) : Nat → Surface.Keep.Session → Option (Pieces × String)
  | 0, _ => none
  | fuel + 1, s =>
      match s.need with
      | some r =>
          match m[r]? with
          | some b => serve m fuel (Surface.Keep.give s b)
          | none => none
      | none => some (s.written.foldl (fun m rb => m.insert rb.1 rb.2) m, s.text)

def rootOf (text : String) : Option String :=
  (text.splitOn "\n").findSome? fun l =>
    if l.startsWith "root: " then some (l.drop 6).toString else none

def firstLine (text : String) : String := (text.splitOn "\n").headD ""

def source : String :=
  "def fill n =\n  case n\n    0 -> []\n    m + 1 -> [n, ...fill m]\n\n" ++
  "def count xs =\n  case xs\n    [] -> 0\n    [x, ...rest] -> add 1 (count rest)\n\n" ++
  "def main big =\n  ask [1] (fn a ->\n    ask [2, a] (fn b ->\n      [count big, add a b]))\n\n" ++
  "main (fill 300)\n"

/-- Three turns, each a new session over the pieces the last one left, give
    what one run against both answers gives. The middle turn reads few pieces. -/
def turns : String :=
  let whole := Surface.converseText source.toUTF8 "[20, 22]".toUTF8 1000000
  match serve {} 10000 (Surface.Keep.start source.toUTF8 1000000) with
  | none => "FAIL the first turn lacked a piece"
  | some (m1, t1) =>
      match rootOf t1 with
      | none => s!"FAIL the first turn did not wait: {t1}"
      | some r1 =>
          let second := Surface.Keep.answer r1 "20".toUTF8 1000000
          match serve m1 10000 second with
          | none => "FAIL the second turn lacked a piece"
          | some (m2, t2) =>
              match rootOf t2 with
              | none => s!"FAIL the second turn did not wait: {t2}"
              | some r2 =>
                  match serve m2 10000 (Surface.Keep.answer r2 "22".toUTF8 1000000) with
                  | none => "FAIL the third turn lacked a piece"
                  | some (m3, t3) =>
                      let joined := firstLine t1 ++ "\n" ++ firstLine t2 ++ "\n" ++ firstLine t3
                      let middle := (t2.splitOn "\n").getLastD ""
                      line (joined == whole && m3.size == m2.size && m2.size < m1.size + 8)
                        s!"three turns from the store give the whole run; {m1.size} pieces after the first, {m2.size} after the second; second turn: {middle}"

#eval IO.println turns

/-- `ask [1] (fn x -> ask [2, x] (fn y -> [x, y, x + 1]))` -/
def askName : Term :=
  .app (.app askTerm (.lit (.arr [.nat 1])))
    (.lam (.app (.app askTerm (.cons (n 2) (.cons (.var 0) emptyArr)))
      (.lam (.cons (.var 1) (.cons (.var 0) (.cons (.succ (.var 1)) emptyArr))))))

/-- A waiting process that holds a name value is saved and continued. It is
    answered with the name `#20`, which it keeps in the function it waits with.
    Saved with every part cut loose, one stored piece is exactly the name's
    bytes, `d8 27 14`; every piece is named by its hash and reads back to its
    bytes; and continued from the root with 22 it gives `[#20, 22, 21]`: the
    name came back a name, and its successor is a plain number. Saved at the
    session's own size the name stays in place, and the run gives the same. -/
def keptName (size : Nat) : String :=
  match converse 100000 askName [.name 20] with
  | (asked, .waiting k) =>
      match (cut size (k.toP : P Ref)).run #[] with
      | none => "FAIL the waiting process has no byte form"
      | some (root, stored) =>
          let m : Pieces := stored.foldl (fun m rb => m.insert rb.1 rb.2) {}
          let sound := stored.all fun rb =>
            hex (Blake3.hash rb.2) == hex rb.1 &&
              (match readPiece rb.2 with
               | .ok q => (pieceBytes q).map hex == some (hex rb.2)
               | .error _ => false)
          let leaf := stored.any fun rb => hex rb.2 == "d82714"
          -- Whole again, its bytes hold the name under tag 39.
          let tagged := match resolve (storeOf m) root with
            | some whole => (((pieceBytes whole).elim "" hex).splitOn "d82714").length > 1
            | none => false
          let start : PState Ref := .running (compile (resumeTerm (.nat 22))) (.cons root .nil) [] []
          let got := match go (storeOf m) 100000 start with
            | .at t => shown (storeOf m) t
            | .paused _ _ => "paused"
          let want := (pieceBytes ((Data.arr [.name 20, .nat 22, .nat 21]).toP : P Ref)).elim "none" hex
          let ok := sound && got == want && asked.length == 2 && tagged && (size != 0 || leaf)
          line ok s!"a waiting process that holds #20, cut at {size} bytes into {m.size} pieces (the name alone is a piece: {leaf}), continued with 22: {got}"
  | _ => "FAIL the program did not wait"

#eval IO.println (keptName 0)
#eval IO.println (keptName Surface.Keep.pieceSize)

/-! Text is one piece. Saving compares its whole byte form, the head and the
    UTF-8 together, with the size, and keeps it in place or stores it whole. -/

def isRef : P Ref → Bool
  | .ref _ => true
  | _ => false

-- 24 ASCII characters are 26 bytes: `78 18` and the 24. At 25 the text is
-- stored; at 26 it stays in place.
#eval do
  let t24 : List Char := List.replicate 24 'x'
  let bytes := (pieceBytes (.text t24 : P Ref)).elim 0 (·.size)
  let at25 := match (cut 25 (.text t24 : P Ref)).run #[] with
    | some (top, stored) => isRef top && stored.size == 1 && (stored.all fun rb => rb.2.size == 26 &&
        (hex rb.2).startsWith "7818" && hex (Blake3.hash rb.2) == hex rb.1 &&
        (match readPiece rb.2 with | .ok (.text t) => t == t24 | _ => false))
    | none => false
  let at26 := match (cut 26 (.text t24 : P Ref)).run #[] with
    | some (.text t, stored) => t == t24 && stored.size == 0
    | _ => false
  -- 23 characters are 24 bytes, a one-byte head: in place at 24, stored at 23.
  let t23 : List Char := List.replicate 23 'x'
  let at23 := match (cut 23 (.text t23 : P Ref)).run #[], (cut 24 (.text t23 : P Ref)).run #[] with
    | some (a, one), some (.text _, none') => isRef a && one.size == 1 && none'.size == 0
    | _, _ => false
  -- Characters of more than one byte count as their bytes: 12 of `é` are 24
  -- bytes of UTF-8, 26 with the head.
  let wide : List Char := List.replicate 12 'é'
  let atWide := match (cut 25 (.text wide : P Ref)).run #[], (cut 26 (.text wide : P Ref)).run #[] with
    | some (a, one), some (.text _, none') => isRef a && one.size == 1 && none'.size == 0
    | _, _ => false
  -- In a pair, the text is in place at 26 and the pair around it is stored.
  let inPair := match (cut 26 (.cons (.text t24) .nil : P Ref)).run #[] with
    | some (top, stored) => isRef top && stored.size == 1 && (stored.all fun rb =>
        match readPiece rb.2 with | .ok (.cons (.text t) .nil) => t == t24 | _ => false)
    | none => false
  IO.println (line (bytes == 26 && at25 && at26 && at23 && atWide && inPair)
    s!"a text of 24 characters is {bytes} bytes: stored when cut at 25 ({at25}), in place when cut at 26 ({at26})")

/-- A session's turn against a store, with the first piece it needs and the
    store lacks, if any. -/
def serveOr (m : Pieces) : Nat → Surface.Keep.Session → Except (Option Ref) (Pieces × String)
  | 0, _ => .error none
  | fuel + 1, s =>
      match s.need with
      | some r =>
          match m[r]? with
          | some b => serveOr m fuel (Surface.Keep.give s b)
          | none => .error (some r)
      | none => .ok (s.written.foldl (fun m rb => m.insert rb.1 rb.2) m, s.text)

def longText : List Char := (List.range 1000).map fun i => Char.ofNat (97 + i % 26)

def textSource : String :=
  "def main big =\n  ask [1] (fn a ->\n    ask [2, a] (fn b ->\n" ++
  "      case big\n        [] -> 0\n        [c, ...rest] -> [c, add a b, equal rest big]))\n\n" ++
  "main \"" ++ String.ofList longText ++ "\"\n"

/-- A waiting program that holds a text of 1,000 characters, saved at the
    session's size. Exactly one stored piece is that text, whole. The second
    turn does not look at the text and runs without its piece. The third takes
    the text apart by `case`: without the piece it stops needing exactly that
    reference, and with it gives what one run gives. -/
def keptText : String :=
  let whole := Surface.converseText textSource.toUTF8 "[20, 22]".toUTF8 1000000
  match serveOr {} 10000 (Surface.Keep.start textSource.toUTF8 1000000) with
  | .error _ => "FAIL the first turn lacked a piece"
  | .ok (m1, t1) =>
      let texts := m1.toList.filter fun rb =>
        match readPiece rb.2 with | .ok (.text _) => true | _ => false
      let isIt := texts.all fun rb =>
        (match readPiece rb.2 with | .ok (.text t) => t == longText | _ => false) &&
          rb.2.size == 1003 && (hex rb.2).startsWith "7903e8"
      match texts, rootOf t1 with
      | [(textRef, _)], some r1 =>
          let lacking := m1.erase textRef
          match serveOr lacking 10000 (Surface.Keep.answer r1 "20".toUTF8 1000000) with
          | .error _ => "FAIL the second turn, which does not look at the text, needed a piece it was not given"
          | .ok (m2, t2) =>
              match rootOf t2 with
              | none => s!"FAIL the second turn did not wait: {t2}"
              | some r2 =>
                  let third := Surface.Keep.answer r2 "22".toUTF8 1000000
                  let pausedOnIt := match serveOr m2 10000 third with
                    | .error (some r) => hex r == hex textRef
                    | _ => false
                  match serveOr (m2.insert textRef (m1.getD textRef ByteArray.empty)) 10000 third with
                  | .error _ => "FAIL the third turn lacked a piece with the whole store"
                  | .ok (_, t3) =>
                      let joined := firstLine t1 ++ "\n" ++ firstLine t2 ++ "\n" ++ firstLine t3
                      line (isIt && pausedOnIt && joined == whole && firstLine t3 == "[97, 42, 0]")
                        s!"a waiting program that holds a text of 1000 characters: one piece of {m1.size} is the text, the second turn runs without it, the third pauses on its reference ({pausedOnIt}) and with it gives {firstLine t3}"
      | _, _ => s!"FAIL {texts.length} stored pieces are text, or the first turn did not wait: {firstLine t1}"

#eval IO.println keptText
