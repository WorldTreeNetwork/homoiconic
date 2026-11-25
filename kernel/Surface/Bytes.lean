import Reflect.Arith
import Surface.Run
import Wire.Form
import Wire.Reply

namespace Surface
open Reflect

def renderBytesError (msg : String) : String := "bytes error: " ++ msg

/-- Read a program from its byte form, compile, run the machine for `budget`
    steps, and render. The same run as `runText` gives the source. -/
def runBytes (bytes : ByteArray) (budget : Nat) (sp : Space := .ledger defaultSpace) : String :=
  match Wire.readProgram bytes with
  | .error msg => renderBytesError msg
  | .ok t => renderEnded budget sp (runIn sp budget (load (compile t)))

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

/-- Run `t` through `k` interpreters, `level k t`, on the machine with a budget
    of `budget` charged as `runPriced` charges it, and render what the program
    itself gave. The interpreter performs each operation of the program as the
    machine's own primitive on the same operation number and argument
    (`Reflect.interp`, the `prim` case), so it pays the same charge the
    program pays for it, and at least one for each of its own steps on top. `Reflect.tower` and the
    machine theorems say the text is the text of the direct run when both
    finish. With `asText` a result that is a text is written raw, with no
    quotes and no escapes. An answer that is not an outcome's data form cannot happen and
    renders as an internal error. -/
def renderInterpreted (k budget : Nat) (asText : Bool) (t : Term)
    (sp : Space := .ledger defaultSpace) : String :=
  match runIn sp budget (load (compile (level k t))) with
  | .full _ => renderSpace sp.cells
  | .reached (.halted o) =>
    match unlift k o with
    | some (.value (.data d)) =>
      if d.writes (4 * sp.cells) then
        (if asText then renderMOutcomeText (.value (.data d)) else renderData d)
      else renderSpace sp.cells
    | some o => if asText then renderMOutcomeText o else renderMOutcome o
    | none => "error: the interpreter answered something that is not an outcome"
  | .reached s => renderState budget s

/-- The most interpreters a program is run through. The machine is given the
    whole tower, `level k t`, and `unlift k` reads the answer back by
    recursion on `k`, before the budget counts a step, so the number of levels
    is bounded here and not by the budget. Every caller has this bound; the
    hosts ask for it by `reflect_max_levels` to refuse on their own line. -/
def maxLevels : Nat := 8

/-- What `interpBytes` and `interpText` answer for more than `maxLevels`
    levels, without reading the program. -/
def levelsError : String :=
  s!"levels error: the interpreter levels must be at most {maxLevels}"

/-- `runBytes` through `k` interpreters. The program's bytes are already its
    data form; `level` quotes it once more for each level above the first. -/
def interpBytes (bytes : ByteArray) (k budget : Nat) (asText : Bool := false)
    (sp : Space := .ledger defaultSpace) : String :=
  if k > maxLevels then levelsError else
  match Wire.readProgram bytes with
  | .error msg => renderBytesError msg
  | .ok t => renderInterpreted k budget asText t sp

/-- `runText` through `k` interpreters. -/
def interpText (src : ByteArray) (k budget : Nat) (asText : Bool := false)
    (sp : Space := .ledger defaultSpace) : String :=
  if k > maxLevels then levelsError else
  match read src with
  | .error msg => renderSyntaxError msg
  | .ok t => renderInterpreted k budget asText t sp

/-- Program bytes in, the bounded-run reply bytes out. One evaluation, with
    the budget charged as `runText` charges it (`runPriced`): one a step, and
    an operation its cost before it runs, within the space `sp` (`runIn`). A
    run out of space is the space reply, and so is an answer whose data form
    would take more than four bytes for each cell of the space
    (`Wire.fitsValue`), which is found before the form is built. -/
def replyBytes (bytes : ByteArray) (budget : Nat) (sp : Space := .ledger defaultSpace) :
    ByteArray :=
  let reply := match Wire.readProgram bytes with
    | .error _ => Wire.RunReply.refused
    | .ok t =>
        match runIn sp budget (load (compile t)) with
        | .full _ => .space
        | .reached (.halted (.value v)) =>
            if Wire.fitsValue v (4 * sp.cells) then
              (if (Wire.valueData v).isSome then .value v else .unrepresentable)
            else .space
        | .reached (.halted (.unbound i)) => .unbound i
        | .reached (.halted .wrong) => .wrong
        | .reached .fault => .fault
        | .reached (.running _ _ _ _) => .budget
  Wire.runReplyBytes reply

/-- Read a program's source and give its byte form. The first byte answered is
    0 and the byte form follows, or it is 1 and the syntax error follows. -/
def sourceBytes (src : ByteArray) : ByteArray :=
  match read src with
  | .error msg => (ByteArray.empty.push 1) ++ (renderSyntaxError msg).toUTF8
  | .ok t => (ByteArray.empty.push 0) ++ Wire.programBytes t

end Surface
