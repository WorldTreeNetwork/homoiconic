import Reflect.Semantics

namespace Reflect

/-- The text an array of code points spells, or `none` if an item is not a
    number or is not a Unicode scalar value. -/
def scalars? (xs : List Data) : Option (List Char) :=
  (xs.mapM fun | Data.nat n => some n | _ => none).bind Text.ofCodes?

/-- The first set of operations: exact arithmetic and comparison on natural
    numbers of any size. An operation takes its operands as one array. A number
    that is not an operation, or operands of the wrong shape, give `[]`. Of the
    operations here only `codes` gives `[]` otherwise, for the empty text and
    for `[]`.

    Division by zero is 0 and the remainder by zero is the dividend. Subtraction
    stops at 0. Comparison answers 1 or 0. `equal` compares any two data values,
    and tells a text from an array and a name from a number.

    `text` (7) and `codes` (8) take their operand itself, not an array of
    operands. They go between a text and the array of its code points, and each
    leaves its own kind as it is. An array with an item that is not the number
    of a Unicode scalar value is neither, and gives `[]`. -/
def arith : Nat → Data → Data
  | 0, .arr [.nat a, .nat b] => .nat (a + b)
  | 1, .arr [.nat a, .nat b] => .nat (a - b)
  | 2, .arr [.nat a, .nat b] => .nat (a * b)
  | 3, .arr [.nat a, .nat b] => .nat (a / b)
  | 4, .arr [.nat a, .nat b] => .nat (a % b)
  | 5, .arr [x, y] => .nat (if x == y then 1 else 0)
  | 6, .arr [.nat a, .nat b] => .nat (if a < b then 1 else 0)
  | 7, .text t => .text t
  | 7, .arr xs =>
      match scalars? xs with
      | some t => .text t
      | none => .arr []
  | 8, .text t => .arr ((Text.codes t).map .nat)
  | 8, .arr xs =>
      match scalars? xs with
      | some _ => .arr xs
      | none => .arr []
  | _, _ => .arr []

/-- The names the surface syntax gives these operations: the name, the
    operation's number, and how many arguments the named function takes. With
    two it hands the operation the array of both; with one, the argument itself. -/
def arithNames : List (String × Nat × Nat) :=
  [("add", 0, 2), ("sub", 1, 2), ("mul", 2, 2), ("div", 3, 2), ("mod", 4, 2), ("equal", 5, 2),
   ("less", 6, 2), ("text", 7, 1), ("codes", 8, 1)]

/-- Bits of a number. Zero costs one, the same as one. -/
def bits (n : Nat) : Nat := Nat.log2 n + 1

/-- What a step budget charges for an operation. Addition and subtraction cost
    the bits of the operands. Multiplication, division and remainder cost the
    product of those bits. Comparison, `text` and `codes` cost one, or one more
    than the length of a text or an array of code points. Anything else costs
    one. The charge is read off the argument; it does not run the operation. -/
def arithCost : Nat → Data → Nat
  | 0, .arr [.nat a, .nat b] => bits a + bits b
  | 1, .arr [.nat a, .nat b] => bits a + bits b
  | 2, .arr [.nat a, .nat b] => bits a * bits b
  | 3, .arr [.nat a, .nat b] => bits a * bits b
  | 4, .arr [.nat a, .nat b] => bits a * bits b
  | 6, .arr [.nat a, .nat b] => bits a + bits b
  | 7, .text t => t.length + 1
  | 7, .arr xs => xs.length + 1
  | 8, .text t => t.length + 1
  | 8, .arr xs => xs.length + 1
  | _, _ => 1

/-- The table the host runs with. The theorems do not mention it: they hold
    for every table. -/
instance arithOps : Ops where
  op := arith
  cost := arithCost

end Reflect
