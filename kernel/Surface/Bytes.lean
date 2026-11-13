import Surface.Run
import Wire.Form

namespace Surface
open Reflect

def renderBytesError (msg : String) : String := "bytes error: " ++ msg

/-- Read a program from its byte form, compile, run the machine for `budget`
    steps, and render. The same run as `runText` gives the source. -/
def runBytes (bytes : ByteArray) (budget : Nat) : String :=
  match Wire.readProgram bytes with
  | .error msg => renderBytesError msg
  | .ok t => renderState budget (runUntil budget (load (compile t)))

/-- An outcome the interpreter gave as data, read back: `[0, [1, d]]` is the
    data `d`, `[0, [0, body, env]]` a function, `[1, i]` an unbound variable,
    and `[2]` a wrong one. This undoes `reifyOutcome` as far as rendering needs. -/
def unreifyOutcome : Data → Option MOutcome
  | .arr [.nat 0, .arr [.nat 1, d]] => some (.value (.data d))
  | .arr [.nat 0, .arr [.nat 0, _, _]] => some (.value (.closure .done []))
  | .arr [.nat 1, .nat i] => some (.unbound i)
  | .arr [.nat 2] => some .wrong
  | _ => none

/-- Read an outcome back through `k` interpreters: `lift k`, undone. -/
def unlift : Nat → MOutcome → Option MOutcome
  | 0, o => some o
  | k + 1, .value (.data d) => (unreifyOutcome d).bind (unlift k)
  | _ + 1, _ => none

/-- Run `t` through `k` interpreters, `level k t`, on the machine for `budget`
    steps, and render what the program itself gave. `Reflect.tower` and the
    machine theorems say the text is the text of the direct run when both
    finish. With `asText` a result that is an array of code points is written
    as the text it spells. An answer that is not an outcome's data form cannot happen and
    renders as an internal error. -/
def renderInterpreted (k budget : Nat) (asText : Bool) (t : Term) : String :=
  match runUntil budget (load (compile (level k t))) with
  | .halted o =>
    match unlift k o with
    | some o => if asText then renderMOutcomeText o else renderMOutcome o
    | none => "error: the interpreter answered something that is not an outcome"
  | s => renderState budget s

/-- `runBytes` through `k` interpreters. The program's bytes are already its
    data form; `level` quotes it once more for each level above the first. -/
def interpBytes (bytes : ByteArray) (k budget : Nat) (asText : Bool := false) : String :=
  match Wire.readProgram bytes with
  | .error msg => renderBytesError msg
  | .ok t => renderInterpreted k budget asText t

/-- `runText` through `k` interpreters. -/
def interpText (src : ByteArray) (k budget : Nat) (asText : Bool := false) : String :=
  match read src with
  | .error msg => renderSyntaxError msg
  | .ok t => renderInterpreted k budget asText t

/-- Read a program's source and give its byte form. The first byte answered is
    0 and the byte form follows, or it is 1 and the syntax error follows. -/
def sourceBytes (src : ByteArray) : ByteArray :=
  match read src with
  | .error msg => (ByteArray.empty.push 1) ++ (renderSyntaxError msg).toUTF8
  | .ok t => (ByteArray.empty.push 0) ++ Wire.programBytes t

end Surface
