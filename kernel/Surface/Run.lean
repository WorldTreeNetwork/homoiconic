import Reflect.Arith
import Surface.Read
import Surface.Render
import Reflect.RunUntil
import Reflect.Space
import Reflect.Request

namespace Surface
open Reflect

/-- How a space-limited run is written. A run out of space is its own line.
    A data answer is written only when that takes at most four bytes for each
    cell of the space (`Data.writes`): a value is written as the tree it is,
    which can be far more than the cells it holds. -/
def renderEnded (budget : Nat) (sp : Space) : Ended → String
  | .full _ => renderSpace sp.cells
  | .reached (.halted (.value (.data d))) =>
      if d.writes (4 * sp.cells) then renderData d else renderSpace sp.cells
  | .reached s => renderState budget s

/-- Read, compile, run the machine for `budget` steps within the space `sp`,
    and render. This runs the machine, not `evalFuel`. Each step costs one,
    and a primitive costs what its table charges, as `runPriced` charges; the
    cells each step makes are counted against the space (`runIn`). A run stops
    where `run` does after some number of steps (`Reflect.runSpace_run`). With
    no space given the run has the default with no count, so its outcome
    depends on the program and the budget alone. -/
def runText (src : ByteArray) (budget : Nat) (sp : Space := .ledger defaultSpace) : String :=
  match read src with
  | .error msg => renderSyntaxError msg
  | .ok t => renderEnded budget sp (runIn sp budget (load (compile t)))

/-- One line for each request made, in order. -/
def renderAsked (asked : List Data) : String :=
  String.join (asked.map fun d => "asked: " ++ renderData d ++ "\n")

/-- Read a program and an answers text, run the program against the answers on
    the machine, and render: a line for each request, then how the run ended.
    The answers text is a program whose result is an array; its items are the
    answers. Each turn, and the answers program, gets a budget of `budget`, charged
    as `runPriced` charges it, and is a turn (`runTurn`). What is
    reported is a run of the program (`Reflect.converse_finished`,
    `Reflect.converse_waiting`). -/
def converseText (program answers : ByteArray) (budget : Nat) : String :=
  match read program with
  | .error msg => renderSyntaxError msg
  | .ok t =>
    match read answers with
    | .error msg => "answers: " ++ renderSyntaxError msg
    | .ok answersTerm =>
      match runTurn budget (load (compile answersTerm)) with
      | .halted (.value (.data (.arr as))) =>
        let r := converse budget t as
        renderAsked r.1 ++
          (match r.2 with
           | .finished w => renderMOutcome w
           | .waiting _ => "waiting"
           | .unfinished => s!"no result within {budget} steps of a turn")
      | _ => "answers: not an array"

end Surface
