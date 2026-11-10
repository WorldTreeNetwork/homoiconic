import Reflect.Semantics

namespace Reflect

/-- The first set of operations: exact arithmetic and comparison on natural
    numbers of any size. An operation takes its operands as one array. A number
    that is not an operation, or operands of the wrong shape, give `[]`, which
    no operation here gives otherwise.

    Division by zero is 0 and the remainder by zero is the dividend. Subtraction
    stops at 0. Comparison answers 1 or 0. `equal` compares any two data values. -/
def arith : Nat → Data → Data
  | 0, .arr [.nat a, .nat b] => .nat (a + b)
  | 1, .arr [.nat a, .nat b] => .nat (a - b)
  | 2, .arr [.nat a, .nat b] => .nat (a * b)
  | 3, .arr [.nat a, .nat b] => .nat (a / b)
  | 4, .arr [.nat a, .nat b] => .nat (a % b)
  | 5, .arr [x, y] => .nat (if x == y then 1 else 0)
  | 6, .arr [.nat a, .nat b] => .nat (if a < b then 1 else 0)
  | _, _ => .arr []

/-- The names the surface syntax gives these operations, with their numbers. -/
def arithNames : List (String × Nat) :=
  [("add", 0), ("sub", 1), ("mul", 2), ("div", 3), ("mod", 4), ("equal", 5), ("less", 6)]

/-- The table the host runs with. The theorems do not mention it: they hold
    for every table. -/
instance arithOps : Ops := ⟨arith⟩

end Reflect
