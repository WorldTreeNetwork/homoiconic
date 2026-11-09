import Circular
open Circular
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def decodedRun (fuel : Nat) (t : Term) : Option (Option Outcome) :=
  (evalFuel fuel [] t).map fun o => match o with
    | .value v => decodeOutcome (readback v)
    | .unbound _ => none

#eval evalFuel 3 [] identityApplication
#eval evalFuel 1 [] (.var 0)

#eval decodedRun 300 (interpreterApplication (.var 0) (.var 0))
#eval decodedRun 300 (interpreterApplication identityApplication (.app (.lam (.var 0)) (.lam (.var 0))))
#eval decodedRun 300 (interpreterApplication (.app (.var 0) omega) (.app (.var 0) omega_pure))
#eval decodedRun 300 (interpreterApplication (.lam (.var 1)) (.lam (.var 1)))
-- A bounded execution check only; this does not prove interpreter divergence.
#eval (evalFuel 300 [] (interpreterApplication omega omega_pure)).isNone
