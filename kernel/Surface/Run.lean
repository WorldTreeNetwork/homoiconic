import Reflect.Arith
import Surface.Read
import Surface.Render
import Reflect.RunUntil
import Reflect.Request

namespace Surface
open Reflect

/-- Read, compile, run the machine for `budget` steps, and render. This runs the
    machine, not `evalFuel`. Each step costs one, and a primitive costs what
    its table charges (`runPriced`). `runUntil` is `run` (`Reflect.runUntil_eq`). -/
def runText (src : ByteArray) (budget : Nat) : String :=
  match read src with
  | .error msg => renderSyntaxError msg
  | .ok t => renderState budget (runPriced budget (load (compile t)))

/-- One line for each request made, in order. -/
def renderAsked (asked : List Data) : String :=
  String.join (asked.map fun d => "asked: " ++ renderData d ++ "\n")

/-- Read a program and an answers text, run the program against the answers on
    the machine, and render: a line for each request, then how the run ended.
    The answers text is a program whose result is an array; its items are the
    answers. Each turn, and the answers program, gets `budget` steps. What is
    reported is a run of the program (`Reflect.converse_finished`,
    `Reflect.converse_waiting`). -/
def converseText (program answers : ByteArray) (budget : Nat) : String :=
  match read program with
  | .error msg => renderSyntaxError msg
  | .ok t =>
    match read answers with
    | .error msg => "answers: " ++ renderSyntaxError msg
    | .ok answersTerm =>
      match runUntil budget (load (compile answersTerm)) with
      | .halted (.value (.data (.arr as))) =>
        let r := converse budget t as
        renderAsked r.1 ++
          (match r.2 with
           | .finished w => renderMOutcome w
           | .waiting _ => "waiting"
           | .unfinished => s!"no result within {budget} steps of a turn")
      | _ => "answers: not an array"

end Surface
