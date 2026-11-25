import Wire.Form

/-! The byte form of one bounded run. It is not a network frame and it is not
    `Reflect.reifyOutcome`. -/

namespace Wire
open Reflect

inductive RunReply where
  | value : MValue → RunReply
  | budget
  | refused
  | unbound : Nat → RunReply
  | wrong
  | fault
  | unrepresentable
  /-- The run passed its space, or its answer is too large to write within it. -/
  | space
  deriving Repr

/-- Tag 6 is an absent machine-value encoding, including a `.value` whose
    `valueData` is missing. -/
def runReplyData : RunReply → Data
  | .value v =>
      match valueData v with
      | some d => .arr [.nat 0, d]
      | none => .arr [.nat 6]
  | .budget => .arr [.nat 1]
  | .refused => .arr [.nat 2]
  | .unbound i => .arr [.nat 3, .nat i]
  | .wrong => .arr [.nat 4]
  | .fault => .arr [.nat 5]
  | .unrepresentable => .arr [.nat 6]
  | .space => .arr [.nat 7]

def runReplyBytes (r : RunReply) : ByteArray := write (runReplyData r)

def readRunReply (b : ByteArray) : Except String RunReply := do
  match ← read b with
  | .arr [.nat 0, d] =>
      match dataValue d with
      | some v => .ok (.value v)
      | none => .error "the reply value is not a machine value"
  | .arr [.nat 1] => .ok .budget
  | .arr [.nat 2] => .ok .refused
  | .arr [.nat 3, .nat i] => .ok (.unbound i)
  | .arr [.nat 4] => .ok .wrong
  | .arr [.nat 5] => .ok .fault
  | .arr [.nat 6] => .ok .unrepresentable
  | .arr [.nat 7] => .ok .space
  | _ => .error "the reply is not a bounded run"

end Wire
