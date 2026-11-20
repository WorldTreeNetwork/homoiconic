import Reflect.Machine

namespace Reflect
variable [Ops]

/-- `run`, stopping as soon as the machine stops. It is the same function. -/
def runUntil : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | n + 1, .running c e stk frs => runUntil n (step (.running c e stk frs))

/-- The charge for the next step. A primitive costs what its table says; every
    other step costs one. -/
def stepCost : State → Nat
  | .running (.prim _) _ (.data d :: .data (.nat n) :: _) _ => Ops.cost n d
  | .running (.prim _) _ (.data d :: .data (.name n) :: _) _ => Ops.cost n d
  | _ => 1

/-- `run`, charging `stepCost` for each step and stopping before a step the
    fuel cannot pay for. A primitive whose charge is above the fuel left does
    not run. When every charge is one, this is `runUntil`. -/
def runPriced : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | fuel + 1, s =>
      match stepCost s with
      | 0 => runPriced fuel (step s)
      | c + 1 =>
        if c + 1 ≤ fuel + 1 then runPriced (fuel - c) (step s) else s
termination_by fuel => fuel
decreasing_by all_goals omega

end Reflect
