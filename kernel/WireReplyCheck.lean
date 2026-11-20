import Reflect.Arith
import Surface.Bytes
import Wire.Reply
open Reflect Wire

def fact : Nat := 265252859812191058636308480000000

def check (ok : Bool) (what : String) : String :=
  s!"{if ok then "ok  " else "FAIL"} {what}"

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
