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

/-! Names. A name is seen by `succ`, `case` and the operation number of `prim`
    as its number, and consing onto one is wrong. Each scenario states its
    outcome: direct evaluation gives it, the machine halts with it (and so does
    not fault), and `check` compares the interpreter at levels 1 and 2, the
    machine whole and the interpreted run in three slices. -/

def nm (k : Nat) : Term := .lit (.name k)

/-- `check`, and the outcome said outright for direct evaluation and the machine. -/
def checkIs (name : String) (p : Term) (want : Outcome) : String :=
  let direct := match evalFuel 20000 [] p with
    | some o => reifyOutcome o == reifyOutcome want
    | none => false
  let halts := match run 2000000 (load (compile p)) with
    | .halted w => (readOutcome w).map reifyOutcome == some (reifyOutcome want)
    | _ => false
  let line := check name p
  if direct && halts then line
  else s!"FAIL {name}: direct is the stated outcome {direct}, machine halts with it {halts}; {line}"

def nameScenarios : List (String × Term × Outcome) :=
  [ ("name: successor of #3 is the number 4", .succ (nm 3), .value (.data (.nat 4))),
    ("name: cons onto #3 is wrong", .cons (n 1) (nm 3), .wrong),
    ("name: case on #0 takes the zero branch",
      .dcase (nm 0) (n 7) (n 8) (n 9) (n 9), .value (.data (.nat 7))),
    ("name: case on #3 binds the plain number 2",
      .dcase (nm 3) (n 7) (.var 0) (n 9) (n 9), .value (.data (.nat 2))),
    ("name: operation #0 with an unbound argument is that unbound",
      .prim (nm 0) (.var 2), .unbound 2),
    ("name: operation #0 on a function is wrong", .prim (nm 0) identity, .wrong),
    ("name: operation #0 on [2, 3] is 5",
      .prim (nm 0) (.lit (.arr [.nat 2, .nat 3])), .value (.data (.nat 5))),
    -- Arithmetic operands stay plain numbers; equality tells a name from its number.
    ("name: add of [#3, 0] is []",
      .prim (n 0) (.lit (.arr [.name 3, .nat 0])), .value (.data (.arr []))),
    ("name: add of [3, 0] is 3",
      .prim (n 0) (.lit (.arr [.nat 3, .nat 0])), .value (.data (.nat 3))),
    ("name: equal of [#3, 3] is 0",
      .prim (n 5) (.lit (.arr [.name 3, .nat 3])), .value (.data (.nat 0))),
    ("name: equal of [#3, #3] is 1",
      .prim (n 5) (.lit (.arr [.name 3, .name 3])), .value (.data (.nat 1))),
    -- A name is data wherever a rule does not look into it.
    ("name: a literal name is itself", nm 3, .value (.data (.name 3))),
    ("name: a name as the head of an array",
      .cons (nm 3) emptyArr, .value (.data (.arr [.name 3]))),
    ("name: case on an array binds a name head",
      .dcase (.lit (.arr [.name 3, .nat 1])) (n 0) (n 0) (n 0) (.var 1), .value (.data (.name 3))),
    ("name: applying a name is wrong", .app (nm 3) omega, .wrong),
    ("name: successor of the successor of #0", .succ (.succ (nm 0)), .value (.data (.nat 2))),
    ("name: operation number computed from a name",
      .prim (.succ (nm 0)) (.lit (.arr [.nat 9, .nat 4])), .value (.data (.nat 5))) ]

#eval do
  for (name, p, want) in nameScenarios do
    IO.println (checkIs name p want)

/-! Text. A text is seen by `case` and `cons` as the list of its code points;
    `succ` of one and one as an operation number are wrong. Equality tells a
    text from the array of its code points, and `text` (7) and `codes` (8) go
    between the two. Each scenario states its outcome, as the name scenarios do. -/

def tx (s : String) : Term := .lit (.text s.toList)
def txd (s : String) : Data := .text s.toList
def arrOf (ks : List Nat) : Data := .arr (ks.map .nat)
def dataIs (d : Data) : Outcome := .value (.data d)

/-- The code points of a text by `case` alone: a recursive walk that conses
    each head, a number, onto the walk of the rest, a text. -/
def caseWalk : Term :=
  .app fixT (.lam (.lam
    (.dcase (.var 0) (n 0) (n 0) emptyArr (.cons (.var 1) (.app (.var 3) (.var 0))))))

def textScenarios : List (String × Term × Outcome) :=
  [ ("text: case on \"\" takes the empty branch",
      .dcase (tx "") (n 7) (n 8) (n 9) (n 10), dataIs (.nat 9)),
    ("text: case on \"hé\" binds the number 104 and the text \"é\"",
      .dcase (tx "hé") (n 0) (n 0) (n 0) (.cons (.var 1) (.cons (.var 0) emptyArr)),
      dataIs (.arr [.nat 104, txd "é"])),
    ("text: the rest of a text of one character is the empty text",
      .dcase (tx "a") (n 0) (n 0) (n 0) (.var 0), dataIs (txd "")),
    ("text: cons 1 \"a\" is the array [1, 97]", .cons (n 1) (tx "a"), dataIs (arrOf [1, 97])),
    ("text: cons 1 \"\" is the array [1]", .cons (n 1) (tx ""), dataIs (arrOf [1])),
    ("text: cons of head and rest is an array, not the text",
      .dcase (tx "hé") (n 0) (n 0) (n 0) (.cons (.var 1) (.var 0)), dataIs (arrOf [104, 233])),
    ("text: successor of \"a\" is wrong", .succ (tx "a"), .wrong),
    ("text: successor of \"\" is wrong", .succ (tx ""), .wrong),
    ("text: a text as an operation number is wrong before the argument",
      .prim (tx "a") omega, .wrong),
    ("text: the empty text as an operation number is wrong before the argument",
      .prim (tx "") omega, .wrong),
    ("text: applying a text is wrong", .app (tx "a") omega, .wrong),
    ("text: a literal text is itself", tx "hé →", dataIs (txd "hé →")),
    ("text: a text as the head of an array", .cons (tx "a") emptyArr, dataIs (.arr [txd "a"])),
    ("text: equal of \"a\" and [97] is 0",
      .prim (n 5) (.lit (.arr [txd "a", arrOf [97]])), dataIs (.nat 0)),
    ("text: equal of \"\" and [] is 0",
      .prim (n 5) (.lit (.arr [txd "", .arr []])), dataIs (.nat 0)),
    ("text: equal of \"hé\" and \"hé\" is 1",
      .prim (n 5) (.lit (.arr [txd "hé", txd "hé"])), dataIs (.nat 1)),
    ("text: equal of \"a\" and \"b\" is 0",
      .prim (n 5) (.lit (.arr [txd "a", txd "b"])), dataIs (.nat 0)),
    ("text: add of [\"a\", 0] is []",
      .prim (n 0) (.lit (.arr [txd "a", .nat 0])), dataIs (.arr [])),
    ("text: text of [104, 233] is \"hé\"", .prim (n 7) (.lit (arrOf [104, 233])), dataIs (txd "hé")),
    ("text: text of a text is that text", .prim (n 7) (tx "hé"), dataIs (txd "hé")),
    ("text: text of [] is the empty text", .prim (n 7) emptyArr, dataIs (txd "")),
    ("text: text of a surrogate is []", .prim (n 7) (.lit (arrOf [55296])), dataIs (.arr [])),
    ("text: text of a number past U+10FFFF is []",
      .prim (n 7) (.lit (arrOf [104, 1114112])), dataIs (.arr [])),
    ("text: text of an array with an array in it is []",
      .prim (n 7) (.lit (.arr [.nat 104, .arr [.nat 105]])), dataIs (.arr [])),
    ("text: text of an array with a text in it is []",
      .prim (n 7) (.lit (.arr [.nat 104, txd "i"])), dataIs (.arr [])),
    ("text: text of a number is []", .prim (n 7) (n 104), dataIs (.arr [])),
    ("text: text of a name is []", .prim (n 7) (.lit (.name 104)), dataIs (.arr [])),
    ("text: codes of \"hé\" is [104, 233]", .prim (n 8) (tx "hé"), dataIs (arrOf [104, 233])),
    ("text: codes of \"\" is []", .prim (n 8) (tx ""), dataIs (.arr [])),
    ("text: codes of an array of code points is that array",
      .prim (n 8) (.lit (arrOf [104, 233])), dataIs (arrOf [104, 233])),
    ("text: codes of a surrogate is []", .prim (n 8) (.lit (arrOf [55296])), dataIs (.arr [])),
    ("text: codes of a number is []", .prim (n 8) (n 104), dataIs (.arr [])),
    ("text: text of codes of a text is the text",
      .prim (n 7) (.prim (n 8) (tx "h𐅑水")), dataIs (txd "h𐅑水")),
    ("text: a case walk gives the code points",
      .app caseWalk (tx "hé𐅑"), dataIs (arrOf [104, 233, 65873])),
    ("text: codes agrees with a case walk",
      .prim (n 5) (.cons (.app caseWalk (tx "h\\i\n é水𐅑")) (.cons (.prim (n 8) (tx "h\\i\n é水𐅑")) emptyArr)),
      dataIs (.nat 1)) ]

#eval do
  for (name, p, want) in textScenarios do
    IO.println (checkIs name p want)

/-- The three functions of `Reflect.Text` agree: taking a text apart with
    `uncons?` gives the list `codes` gives, and `ofCodes?` of it is the text. -/
def unconsWalk : Nat → List Char → List Nat
  | 0, _ => []
  | f + 1, t =>
    match Text.uncons? t with
    | none => []
    | some (c, r) => c :: unconsWalk f r

#eval do
  let texts : List String := ["", "a", "hé", "h\\i\n", "水𐅑 →", String.ofList (List.replicate 1000 'x')]
  for s in texts do
    let t : List Char := String.toList s
    let ok := unconsWalk (t.length + 1) t == Text.codes t && Text.ofCodes? (Text.codes t) == some t
    IO.println s!"{if ok then "ok  " else "FAIL"} text: uncons?, codes and ofCodes? agree on a text of {t.length} characters"
  let bad := [[55296], [57343], [1114112], [97, 55296]].all fun ks => Text.ofCodes? ks == none
  let good := Text.ofCodes? [55295, 57344, 1114111] |>.isSome
  IO.println s!"{if bad && good then "ok  " else "FAIL"} text: ofCodes? refuses surrogates and numbers past U+10FFFF, and takes their neighbours"
