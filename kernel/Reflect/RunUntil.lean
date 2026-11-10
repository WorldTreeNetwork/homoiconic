import Reflect.Machine

namespace Reflect
variable [Ops]

/-- `run`, stopping as soon as the machine stops. It is the same function. -/
def runUntil : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | n + 1, .running c e stk frs => runUntil n (step (.running c e stk frs))

end Reflect
