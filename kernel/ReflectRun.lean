import Reflect.Arith
import Reflect
open Reflect

/-- Both routes and the machine on one program, at one and two interpreter levels.
    The sliced run cuts the interpreted program at steps 50 and 150, while it is live. -/
def check (name : String) (p : Term) (fuel : Nat := 20000) (steps : Nat := 2000000) : String :=
  let same (a : Option Outcome) (d : Option Outcome) : Bool :=
    match a, d with
    | some o, some (.value (.data x)) => x == reifyOutcome o
    | _, _ => false
  let direct := evalFuel fuel [] p
  let one := same direct (evalFuel fuel [] (level 1 p))
  let two := same (evalFuel fuel [] (level 1 p)) (evalFuel fuel [] (level 2 p))
  let machine :=
    match direct, run steps (load (compile p)) with
    | some o, .halted w => (readOutcome w).map reifyOutcome == some (reifyOutcome o)
    | _, _ => false
  let sliced :=
    match run steps (load (compile (level 1 p))),
          run (steps - 150) (run 100 (run 50 (load (compile (level 1 p))))) with
    | .halted a, .halted b => (readOutcome a).map reifyOutcome == (readOutcome b).map reifyOutcome
    | _, _ => false
  let back := match decompile (compile p) with
    | some t => reify t == reify p
    | none => false
  let all := one && two && machine && sliced && back
  s!"{if all then "ok  " else "FAIL"} {name}: interp {one}, twice {two}, machine {machine}, sliced {sliced}, decompile {back}"

def n (k : Nat) : Term := .lit (.nat k)
def emptyArr : Term := .lit (.arr [])

#eval IO.println (check "identity applied" (.app identity identity))
#eval IO.println (check "open variable" (.var 0))
#eval IO.println (check "open lambda" (.lam (.var 1)))
#eval IO.println (check "unbound function skips omega" (.app (.var 0) omega))
#eval IO.println (check "literal" (n 7))
#eval IO.println (check "successor" (.succ (.succ (n 5))))
#eval IO.println (check "construct array" (.cons (n 1) (.cons (.succ (n 1)) emptyArr)))
#eval IO.println (check "case on successor" (.dcase (n 3) (n 0) (.var 0) (n 9) (n 9)))
#eval IO.println (check "case on array" (.dcase (.lit (.arr [.nat 4, .nat 5])) (n 0) (n 0) (n 0) (.cons (.var 1) (.var 0))))
#eval IO.println (check "closure over case binder" (.app (.dcase (n 2) identity (.lam (.var 1)) identity identity) (n 0)))
#eval IO.println (check "apply data is wrong" (.app (n 1) omega))
#eval IO.println (check "successor of function is wrong" (.succ identity))
#eval IO.println (check "cons onto number is wrong" (.cons (n 1) (n 2)))
#eval IO.println (check "cons of function is wrong before tail" (.cons identity omega))
#eval IO.println (check "case on function is wrong" (.dcase identity (n 0) (n 0) (n 0) (n 0)))
#eval IO.println (check "case on unbound scrutinee" (.dcase (.var 3) (n 0) (n 0) (n 0) (n 0)))
#eval IO.println (check "case on wrong scrutinee" (.dcase (.succ identity) (n 0) (n 0) (n 0) (n 0)))
#eval IO.println (check "operation: add" (.prim (n 0) (.lit (.arr [.nat 2, .nat 3]))))
#eval IO.println (check "operation on built operands" (.prim (n 2) (.cons (.succ (n 5)) (.cons (n 7) emptyArr))))
#eval IO.println (check "operation number is computed" (.prim (.succ (n 0)) (.lit (.arr [.nat 9, .nat 4]))))
#eval IO.println (check "unknown operation answers []" (.prim (n 99) (n 1)))
#eval IO.println (check "operation number that is an array is wrong before the argument" (.prim emptyArr omega))
#eval IO.println (check "operation number that is a function is wrong before the argument" (.prim identity omega))
#eval IO.println (check "unbound operation number skips the argument" (.prim (.var 4) omega))
#eval IO.println (check "function as operand is wrong" (.prim (n 0) identity))
#eval IO.println (check "unbound operand" (.prim (n 0) (.var 2)))
#eval IO.println (check "wrong operand" (.prim (n 0) (.succ identity)))
#eval IO.println (check "quoted program is data" (.lit (reify (.app identity identity))))
#eval IO.println (check "quoted omega is data" (.lit (reify omega)))
#eval IO.println (check "program builds code and runs it" buildsAndRuns)
#eval IO.println s!"omega: direct none {(evalFuel 2000 [] omega).isNone}, interpreter none {(evalFuel 2000 [] (level 1 omega)).isNone}, machine still running {match run 100000 (load (compile omega)) with | .running .. => true | _ => false}"
