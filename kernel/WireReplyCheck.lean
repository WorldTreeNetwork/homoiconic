import Reflect.Arith
import Surface.Bytes
import Wire.Reply
open Reflect Wire

def fact : Nat := 265252859812191058636308480000000

def check (ok : Bool) (what : String) : String :=
  s!"{if ok then "ok  " else "FAIL"} {what}"

def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)])

def bytesOf (src : String) : ByteArray :=
  let packed := Surface.sourceBytes src.toUTF8
  packed.extract 1 packed.size

def isSpace (b : ByteArray) : Bool :=
  match readRunReply b with
  | .ok .space => hex b == "8107"
  | _ => false

def isValue (b : ByteArray) (n : Nat) : Bool :=
  match readRunReply b with
  | .ok (.value (.data (.nat k))) => k == n
  | _ => false

#eval do
  let src ← IO.FS.readFile "../examples/factorial.hom"
  let packed := Surface.sourceBytes src.toUTF8
  let prog := packed.extract 1 packed.size
  let reply := Surface.replyBytes prog 100000000
  IO.println (check (packed.toList[0]! == 0 && isValue reply fact)
    "factorial reply is the known integer")
  let again := match readRunReply reply with
    | .ok r => runReplyBytes r == reply
    | _ => false
  IO.println (check again "factorial reply reads and writes the same bytes")
  let forever ← IO.FS.readFile "../examples/forever.hom"
  let fp := (Surface.sourceBytes forever.toUTF8)
  let fr := Surface.replyBytes (fp.extract 1 fp.size) 5000
  let budgetOk := match readRunReply fr with
    | .ok .budget => true
    | _ => false
  IO.println (check budgetOk "forever at 5000 steps is the budget reply")
  -- The two replies mjolnir's fixtures hold, byte for byte: a space limit
  -- changes neither.
  IO.println (check (hex reply == "82008200c24e0d13f6370f96865df5dd54000000")
    "factorial at 100000000 steps is 82008200c24e0d13f6370f96865df5dd54000000")
  IO.println (check (hex fr == "8101") "forever at 5000 steps is 8101")
  -- The space reply: tag 7, read back and written the same.
  let sr := runReplyBytes .space
  let spaceRound := match readRunReply sr with
    | .ok .space => true
    | _ => false
  IO.println (check (hex sr == "8107" && spaceRound) "the space reply is 8107 and reads back")
  let unknown := match readRunReply (write (.arr [.nat 8])) with
    | .error _ => true
    | _ => false
  IO.println (check unknown "a reply tag past 7 is refused")
  -- With no count the ledger alone decides, so these are Lean's own answers.
  let deep := bytesOf "def deep x = [x, ...deep x]\ndeep 0\n"
  IO.println (check (isSpace (Surface.replyBytes deep 10000000 (.ledger 100000)))
    "a recursion that waits is the space reply")
  let build := bytesOf "def build acc = build [0, ...acc]\nbuild []\n"
  IO.println (check (isSpace (Surface.replyBytes build 10000000 (.ledger 100000)))
    "a loop that builds is the space reply")
  let stepsFirst := match readRunReply (Surface.replyBytes deep 5000 (.ledger 100000)) with
    | .ok .budget => true
    | _ => false
  IO.println (check stepsFirst "out of steps before out of space is the budget reply")
  -- An answer larger written than held is refused before it is written.
  let double := bytesOf "def dbl x n =\n  case n\n    0 -> x\n    m + 1 -> dbl [x, ...x] m\n\ndbl [0] 40\n"
  IO.println (check (isSpace (Surface.replyBytes double 1000000))
    "an answer built by doubling is the space reply")
  let defs := String.join ((List.range 30).map fun i =>
    if i == 0 then "def f0 x = x\n" else s!"def f{i} x = f{i - 1} x\n")
  let many := bytesOf (defs ++ "fn x -> f29 x\n")
  IO.println (check (isSpace (Surface.replyBytes many 1000000))
    "a function from thirty definitions is the space reply")
  let few := bytesOf "def f0 x = x\ndef f1 x = f0 x\nfn x -> f1 x\n"
  let fewOk := match readRunReply (Surface.replyBytes few 1000000) with
    | .ok (.value (.closure _ _)) => true
    | _ => false
  IO.println (check fewOk "a function from two definitions is its value")
  -- The reply charges each operation its cost, as `runText` does: a budget of
  -- 200 stops a product of two 40-digit numbers before it is computed.
  let big := s!"mul {10^40 - 1} {10^40 - 1}\n"
  let bp := Surface.sourceBytes big.toUTF8
  let stopped := match readRunReply (Surface.replyBytes (bp.extract 1 bp.size) 200) with
    | .ok .budget => true
    | _ => false
  IO.println (check stopped "a 40-digit product at 200 steps is the budget reply")
  IO.println (check (isValue (Surface.replyBytes (bp.extract 1 bp.size) 200000) ((10^40 - 1) ^ 2))
    "a 40-digit product at 200000 steps is the product")
  let bad := Surface.replyBytes (ByteArray.empty.push 0xff) 10
  let refused := match readRunReply bad with
    | .ok .refused => true
    | _ => false
  IO.println (check refused "bytes that are not a program are refused")
  let idSrc := "fn x -> x\n"
  let ip := Surface.sourceBytes idSrc.toUTF8
  let ir := Surface.replyBytes (ip.extract 1 ip.size) 1000
  let round := match readRunReply ir with
    | .ok (.value v) =>
        match valueBytes v with
        | some b => match readValue b with
            | .ok _ => true
            | .error _ => false
        | none => false
    | _ => false
  IO.println (check round "a function value round-trips")
  let small := runReplyBytes .budget
  let trail := match readRunReply (small.push 0) with
    | .error _ => true
    | _ => false
  let budgetShape := match readRunReply small with
    | .ok .budget => true
    | _ => false
  IO.println (check (budgetShape && trail) "a trailing byte is refused")
