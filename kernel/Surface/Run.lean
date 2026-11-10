import Reflect.Arith
import Surface.Read
import Surface.Render
import Reflect.RunUntil

namespace Surface
open Reflect

/-- Read, compile, run the machine for `budget` steps, and render. This runs the
    machine, not `evalFuel`. `runUntil` is `run` (`Reflect.runUntil_eq`). -/
def runText (src : ByteArray) (budget : Nat) : String :=
  match read src with
  | .error msg => renderSyntaxError msg
  | .ok t => renderState budget (runUntil budget (load (compile t)))

end Surface
