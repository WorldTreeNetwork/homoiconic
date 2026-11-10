import Reflect
open Reflect

/-- Both routes and the machine on one program, at one and two interpreter levels. -/
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
          run (steps - 700) (run 400 (run 300 (load (compile (level 1 p))))) with
    | .halted a, .halted b => (readOutcome a).map reifyOutcome == (readOutcome b).map reifyOutcome
    | _, _ => false
  let back := match decompile (compile p) with
    | some t => reify t == reify p
    | none => false
  let all := one && two && machine && sliced && back
  s!"{if all then "ok  " else "FAIL"} {name}: interp {one}, twice {two}, machine {machine}, sliced {sliced}, decompile {back}"

def identity : Term := .lam (.var 0)
def delta : Term := .lam (.app (.var 0) (.var 0))
def omega : Term := .app delta delta
def n (k : Nat) : Term := .lit (.nat k)
def emptyArr : Term := .lit (.arr [])
/-- Builds the identity function's code `[1, 0]` at run time and runs it. -/
def buildsAndRuns : Term := .app interp (.cons (n 1) (.cons (n 0) emptyArr))

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
#eval IO.println (check "quoted program is data" (.lit (reify (.app identity identity))))
#eval IO.println (check "quoted omega is data" (.lit (reify omega)))
#eval IO.println (check "program builds code and runs it" buildsAndRuns)
#eval IO.println s!"omega: direct none {(evalFuel 2000 [] omega).isNone}, interpreter none {(evalFuel 2000 [] (level 1 omega)).isNone}, machine still running {match run 100000 (load (compile omega)) with | .running .. => true | _ => false}"
