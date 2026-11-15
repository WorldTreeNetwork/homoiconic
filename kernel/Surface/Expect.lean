import Reflect.Interpreter
import Reflect.Request

/-!
What the reader must produce. Each entry pairs program text with the exact
`Reflect` term it reads as. This file is the reader's specification by
example; `openspec/changes/move-host-to-reflect/design.md` has the prose.

Translation, as fixed by these examples:
- `fn x y -> b` is `lam (lam b)`.
- `let x = v` followed by the rest of the block `r` is `app (lam r) v`.
- `def f x = b` followed by `r` is `app (lam r) (lam b)` when `b` does not
  mention `f`, and `app (lam r) (app recur (lam (lam b)))` when it does,
  with `f` the outermost binder.
- A run is the `def`s of a block with no `let` between them. A name bound
  nowhere else that a later `def` of the run defines is that definition. The
  definitions are bound so that each follows the ones it mentions; a run in
  which none mentions a later one keeps its order and reads as above. `r`
  definitions that mention one another in a ring are one function of a
  number, `app recur (lam (lam select))`, with the ring's function the outer
  binder and the number the inner: `select` takes member 0 at `0` and counts
  down to the others, and inside it member `q` is `app self (lit q)`. After
  it each member is bound in order, member `q` to `app ring (lit q)`.
- A number is `lit (nat n)`. `[]` is `lit (arr [])`. `[a, b, ...t]` is
  `cons a (cons b t)`; without `...t` the chain ends in `lit (arr [])`.
  Arrays are never folded into one literal.
- `e + 1` is `succ e`. Application binds tighter than `+`, and `+` tighter
  than `|>`. `x |> f` is `app f x`.
- `case e` with arms is `dcase e zero succ empty cons`. The successor arm
  binds its name at index 0. The non-empty arm binds the head at 1 and the
  tail at 0. A missing arm is `wrongT`.
- `[a, b]` takes an array of exactly two items and `[a, b, ...rest]` one of
  two or more. The array arms are tried in the order written. The non-empty
  arm reads one item at a time, each a `dcase` on the tail in the arm before
  it, until the length settles which arm is taken; a length no arm takes is
  `wrongT`, or the catch-all's body.
- A catch-all arm `x -> b` (or `_ -> b`) binds the scrutinee:
  `app (lam (dcase (var 0) ...)) e`, and `b` fills every arm not given.
- `quote e` with no splice is `lit (reify e)`. With splices, every largest
  subterm without a splice is `lit (reify subterm)`, a splice `~e` is `e`
  read outside the quotation, and each node on the way is the `cons` chain
  that builds that node's data form.
- `interpret` is the term `interp`.
- `ask` is the term `askTerm`: `ask payload next` is a function that hands
  `payload` and `next` to its caller. A driver outside the program reads it as
  a request.
-/
namespace Surface
open Reflect

/-- The fixed point `def` uses for a self-call. -/
def recur : Term := B.compile [] B.fix

/-- What a missing `case` arm reads as: applying a number, which is `wrong`. -/
def wrongT : Term := .app (.lit (.nat 0)) (.lit (.nat 0))

def num (k : Nat) : Term := .lit (.nat k)
def nil : Term := .lit (.arr [])
def arr2 (a b : Term) : Term := .cons a (.cons b nil)

def countdownText : String :=
"def countdown n =
  case n
    0 -> 0
    m + 1 -> countdown m

countdown 1000"

def appendText : String :=
"def append xs ys =
  case xs
    [] -> ys
    [head, ...tail] -> [head, ...append tail ys]

append [1, 2] [3, 4]"

def factorialText : String :=
"def factorial n =
  case n
    0 -> 1
    m + 1 -> mul n (factorial m)

factorial 20"

def powerText : String :=
"def power b n =
  case n
    0 -> 1
    m + 1 -> mul b (power b m)

power 2 100"

def addText : String :=
"def add a b =
  case a
    0 -> b
    m + 1 -> add m b + 1

add 2 3"

def evenOddText : String :=
"def even n =
  case n
    0 -> 1
    m + 1 -> odd m
def odd n =
  case n
    0 -> 0
    m + 1 -> even m
"

/-- Three definitions in a ring, with one outside it between them. -/
def ringText : String :=
"def a x = b x
def twice x = [x, x]
def b x = c x
def c x =
  case x
    0 -> twice 7
    m + 1 -> a m
[a 5, b 4, c 3]"

def lengthsText : String :=
"def f xs =
  case xs
    [] -> 0
    [a] -> [1, a]
    [a, b] -> [2, b, a]
    [_, _, c, ...rest] -> [3, c, rest]
[f [], f [5], f [5, 6], f [5, 6, 7], f [5, 6, 7, 8]]"

def spliceText : String :=
"; code with a hole in it
let inner = quote 41
interpret (quote (~inner + 1))"

/-- Program text and the term it must read as. -/
def reads : List (String × Term) := [
  ("ask", askTerm),
  ("42", num 42),
  ("fn x -> x", .lam (.var 0)),
  ("fn x y -> x", .lam (.lam (.var 1))),
  ("let id = fn x -> x\nid id", .app (.lam (.app (.var 0) (.var 0))) (.lam (.var 0))),
  ("[]", nil),
  ("[1, 2]", arr2 (num 1) (num 2)),
  ("[1, [2, 3]]", arr2 (num 1) (arr2 (num 2) (num 3))),
  ("fn x -> [x, ...x]", .lam (.cons (.var 0) (.var 0))),
  ("fn f x -> f x + 1", .lam (.lam (.succ (.app (.var 1) (.var 0))))),
  ("fn x f -> x |> f", .lam (.lam (.app (.var 0) (.var 1)))),
  ("(fn x -> x) 5", .app (.lam (.var 0)) (num 5)),
  ("; hello\n\n7 ; seven\n", num 7),
  (countdownText,
    .app (.lam (.app (.var 0) (num 1000)))
      (.app recur (.lam (.lam
        (.dcase (.var 0) (num 0) (.app (.var 2) (.var 0)) wrongT wrongT))))),
  (appendText,
    .app (.lam (.app (.app (.var 0) (arr2 (num 1) (num 2))) (arr2 (num 3) (num 4))))
      (.app recur (.lam (.lam (.lam
        (.dcase (.var 1) wrongT wrongT (.var 0)
          (.cons (.var 1) (.app (.app (.var 4) (.var 0)) (.var 2))))))))),
  (addText,
    .app (.lam (.app (.app (.var 0) (num 2)) (num 3)))
      (.app recur (.lam (.lam (.lam
        (.dcase (.var 1) (.var 0) (.succ (.app (.app (.var 3) (.var 0)) (.var 1)))
          wrongT wrongT)))))),
  ("def twice f x = f (f x)\ntwice",
    .app (.lam (.var 0)) (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0)))))),
  ("def f x =\n  let y = x + 1\n  [x, y]\nf 1",
    .app (.lam (.app (.var 0) (num 1)))
      (.lam (.app (.lam (arr2 (.var 1) (.var 0))) (.succ (.var 0))))),
  ("fn x ->\n  case x\n    0 -> 1\n    other -> other",
    .lam (.app (.lam (.dcase (.var 0) (num 1) (.var 1) (.var 0) (.var 2))) (.var 0))),
  ("fn x ->\n  case x\n    [_, ...rest] -> rest\n    _ -> []",
    .lam (.app (.lam (.dcase (.var 0) nil nil nil (.var 0))) (.var 0))),
  -- A catch-all's name is visible only in the catch-all's own body.
  ("let x = 99\ncase 0\n  0 -> x\n  x -> x",
    .app (.lam (.app (.lam (.dcase (.var 0) (.var 1) (.var 1) (.var 0) (.var 2))) (num 0)))
      (num 99)),
  ("let x = 99\ncase 3\n  m + 1 -> x\n  x -> 0",
    .app (.lam (.app (.lam (.dcase (.var 0) (num 0) (.var 2) (num 0) (num 0))) (num 3)))
      (num 99)),
  ("let x = 99\ncase [1]\n  [h, ...t] -> x\n  x -> 0",
    .app (.lam (.app (.lam (.dcase (.var 0) (num 0) (num 0) (num 0) (.var 3)))
        (.cons (num 1) nil)))
      (num 99)),
  ("let x = 99\ncase []\n  [] ->\n    let y = x\n    y\n  x -> 0",
    .app (.lam (.app (.lam (.dcase (.var 0) (num 0) (num 0)
        (.app (.lam (.var 0)) (.var 1)) (num 0))) nil))
      (num 99)),
  -- An indented line continues `+`; a line at the statement's column does not.
  ("let x = 0 +\n  1\nx", .app (.lam (.var 0)) (.succ (num 0))),
  -- A header may continue on an indented line, and brackets turn layout off.
  ("let x = fn\n  y -> y\nx 7", .app (.lam (.app (.var 0) (num 7))) (.lam (.var 0))),
  ("def f\n  x = x\nf 7", .app (.lam (.app (.var 0) (num 7))) (.lam (.var 0))),
  ("let x\n  = 7\nx", .app (.lam (.var 0)) (num 7)),
  ("case 3\n  m +\n    1 -> m", .dcase (num 3) wrongT (.var 0) wrongT wrongT),
  ("let x = [1,\n2]\nx", .app (.lam (.var 0)) (arr2 (num 1) (num 2))),
  ("case [1]\n  [h,\n...t] -> h", .dcase (.cons (num 1) nil) wrongT wrongT wrongT (.var 1)),
  ("case [1]\n  [h, ...t\n] -> h", .dcase (.cons (num 1) nil) wrongT wrongT wrongT (.var 1)),
  ("case []\n  [\n] -> 7", .dcase nil wrongT wrongT (num 7) wrongT),
  -- Array patterns of a fixed length, and of a least length.
  ("case [1, 2]\n  [a, b] -> a",
    .dcase (arr2 (num 1) (num 2)) wrongT wrongT wrongT
      (.dcase (.var 0) wrongT wrongT wrongT
        (.dcase (.var 0) wrongT wrongT (.var 3) wrongT))),
  ("case [1, 2]\n  [a, b, ...r] -> [a, b, r]",
    .dcase (arr2 (num 1) (num 2)) wrongT wrongT wrongT
      (.dcase (.var 0) wrongT wrongT wrongT
        (.cons (.var 3) (.cons (.var 1) (.cons (.var 0) nil))))),
  -- A length no arm takes is the catch-all's.
  ("fn x ->\n  case x\n    [a] -> a\n    y -> y",
    .lam (.app (.lam (.dcase (.var 0) (.var 0) (.var 1) (.var 0)
        (.dcase (.var 0) wrongT wrongT (.var 1) (.var 4)))) (.var 0))),
  -- Two definitions that name one another are one function of a number.
  (evenOddText ++ "even 3",
    .app (.lam (.app (.lam (.app (.lam (.app (.var 1) (num 3)))
          (.app (.var 1) (num 1))))
        (.app (.var 0) (num 0))))
      (.app recur (.lam (.lam (.dcase (.var 0)
        (.lam (.dcase (.var 0) (num 1) (.app (.app (.var 3) (num 1)) (.var 0)) wrongT wrongT))
        (.lam (.dcase (.var 0) (num 0) (.app (.app (.var 4) (num 0)) (.var 0)) wrongT wrongT))
        wrongT wrongT))))),
  -- A later definition that is used, with no ring, is bound first.
  ("def a = [1, ...b]\ndef b = [2]\na",
    .app (.lam (.app (.lam (.var 0)) (.cons (num 1) (.var 0)))) (.cons (num 2) nil)),
  ("quote (fn x -> x)", .lit (reify (.lam (.var 0)))),
  ("quote (interpret 1)", .lit (reify (.app interp (num 1)))),
  (spliceText,
    .app (.lam (.app interp (.cons (num 3) (.cons (.var 0) nil))))
      (.lit (reify (num 41)))),
  ("let f = quote (fn x -> x)\nlet a = quote 7\nquote (~f ~a)",
    .app (.lam (.app (.lam (.cons (num 0) (.cons (.var 1) (.cons (.var 0) nil))))
        (.lit (reify (num 7)))))
      (.lit (reify (.lam (.var 0))))),
  ("let a = quote 7\nquote ((fn x -> x) ~a)",
    .app (.lam (.cons (num 0) (.cons (.lit (reify (.lam (.var 0)))) (.cons (.var 0) nil))))
      (.lit (reify (num 7))))
]

/-- Text the reader must refuse, with a word the message must contain. -/
def refused : List (String × String) := [
  ("f 1", "f"),
  ("", "empty"),
  ("let x = 1", "value"),
  ("(1", ")"),
  ("1 + 2", "+"),
  ("fn x ->\n\tx", "tab"),
  ("let y = quote 1\nquote (fn x -> ~y)", "splice"),
  ("let y = 1\nquote y", "y"),
  ("case 1\n  0 -> 1\n  0 -> 2", "arm"),
  ("case 0\n  0 -> ghost\n  ghost -> 2", "ghost"),
  ("let x = 0 +\n1\nx", "+"),
  ("let x = 0 +\n1\n  + 1\nx", "+"),
  ("let x = fn\ny -> y\nx 7", "indented"),
  ("def f\nx = x\nf 7", "indented"),
  ("let x\n= 7\nx", "indented"),
  ("case 3\n  m +\n1 -> m", "indented"),
  ("case 0\n  x\n-> x", "indented"),
  ("case [1]\n  [h, ...t]\n-> h", "indented"),
  ("case []\n  []\n-> 7", "indented"),
  ("case 3\n  m + 1 -> ghost\n  ghost -> 2", "ghost"),
  ("case []\n  [] -> ghost\n  ghost -> 2", "ghost"),
  ("case [1]\n  [h, ...t] -> ghost\n  ghost -> 2", "ghost"),
  ("case [1]\n  [a, 0] -> a", "an item of an array pattern"),
  ("case [1]\n  [a, [b]] -> a", "an item of an array pattern"),
  ("case [1]\n  [...r] -> r", "at least one item"),
  ("case [1]\n  [a, ...r, b] -> r", "last part"),
  ("case [1]\n  [a, b -> a", "expected `,` or `]`"),
  ("case [1]\n  [a, b] -> a\n  [c, d] -> c", "duplicate arm"),
  ("case [1]\n  [a, ...r] -> a\n  [a, b] -> b", "never taken"),
  ("case [1]\n  [a, b]\n-> a", "indented"),
  -- A `let` ends a run, and a quotation does not see a later definition.
  ("def f x = g x\nlet y = 1\ndef g x = 8\nf 1", "unbound name `g`"),
  ("def f x = quote (g 1)\ndef g x = x\nf 1", "quotation")
]

/-- Program text, step budget, and the text the host must print. -/
def prints : List (String × Nat × String) := [
  ("42", 1000, "42"),
  ("add 2 3", 1000, "5"),
  ("mul (add 2 3) (sub 9 5)", 1000, "20"),
  ("sub 2 5", 1000, "0"),
  ("div 7 2", 1000, "3"),
  ("div 7 0", 1000, "0"),
  ("mod 7 0", 1000, "7"),
  ("equal [1, [2]] [1, [2]]", 1000, "1"),
  ("equal 1 [1]", 1000, "0"),
  ("less 2 3", 1000, "1"),
  ("less 3 3", 1000, "0"),
  ("add 1 [2]", 1000, "[]"),
  ("op 0 [20, 22]", 1000, "42"),
  ("op 99 [1, 2]", 1000, "[]"),
  ("op (fn x -> x) 1", 1000, "error: wrong"),
  ("op 0 (fn x -> x)", 1000, "error: wrong"),
  ("let add = fn a b -> a\nadd 7 8", 1000, "7"),
  (factorialText, 1000000, "2432902008176640000"),
  (powerText, 1000000, "1267650600228229401496703205376"),
  ("interpret (quote (add 2 3))", 10000000, "[0, [1, 5]]"),
  ("let id = fn x -> x\nid id", 1000, "<function>"),
  (countdownText, 1000000, "0"),
  (appendText, 1000000, "[1, 2, 3, 4]"),
  (addText, 1000000, "5"),
  ("quote (fn x -> x)", 1000, "[1, 0]"),
  (spliceText, 1000000, "[0, [1, 42]]"),
  ("[1, [2, 3], []]", 1000, "[1, [2, 3], []]"),
  ("1 2", 1000, "error: wrong"),
  ("interpret (quote 5) 6", 1000000, "error: wrong"),
  ("interpret [9]", 1000000, "[2]"),
  ("def loop x = loop x\nloop 0", 10000, "no result within 10000 steps"),
  ("let w = fn x -> x x\nw w", 10000, "no result within 10000 steps"),
  ("let x = 99\ncase 0\n  0 -> x\n  x -> x", 1000, "99"),
  ("let x = 99\ncase 3\n  m + 1 -> x\n  x -> 0", 1000, "99"),
  ("let x = 99\ncase [1]\n  [h, ...t] -> x\n  x -> 0", 1000, "99"),
  ("fn f -> case f\n  _ -> 1", 1000, "<function>"),
  ("let x = 99\ncase []\n  [] ->\n    let y = x\n    y\n  x -> 0", 1000, "99"),
  ("[1, 2, [3, 4]]", 1000, "[1, 2, [3, 4]]"),
  ("case [1]\n  [h,\n...t] -> h", 1000, "1"),
  ("case []\n  [\n] -> 7", 1000, "7"),
  (evenOddText ++ "[even 10, odd 10, even 7, odd 7]", 100000, "[1, 0, 0, 1]"),
  (ringText, 100000, "[[7, 7], [7, 7], [7, 7]]"),
  ("def a = [1, ...b]\ndef b = [2]\na", 1000, "[1, 2]"),
  -- A name that is bound where it is used is not a later definition.
  ("def f x = add x 1\ndef add a b = 99\n[f 1, add 1 1]", 1000, "[2, 99]"),
  ("let g = fn x -> 7\ndef f x = g x\ndef g x = 8\n[f 1, g 1]", 1000, "[7, 8]"),
  -- Of two later definitions of one name, the nearer.
  ("def f x = g x\ndef g x = 1\ndef g x = 2\n[f 0, g 0]", 1000, "[1, 2]"),
  -- A run inside a definition of a run.
  ("def f x = h x\ndef h x =\n  def p y = q y\n  def q y = [y, x, r 1]\n  p 3\ndef r x = [x]\nf 9",
    10000, "[3, 9, [1]]"),
  ("def f x = quote (~(g x))\ndef g x = quote 5\nf 1", 10000, "[2, 5]"),
  ("def a = b\ndef b = a\na", 10000, "no result within 10000 steps"),
  ("case [1, 2, 3]\n  [a, b, c] -> [c, b, a]", 1000, "[3, 2, 1]"),
  ("case [1, 2]\n  [a, b, c] -> [c, b, a]", 1000, "error: wrong"),
  ("case [1, 2]\n  [a, b, c] -> [c, b, a]\n  _ -> 9", 1000, "9"),
  ("case [1]\n  [a, b, ...rest] -> rest\n  other -> [other]", 1000, "[[1]]"),
  ("case [1, 2, 3, 4]\n  [a, b, ...rest] -> [b, a, rest]", 1000, "[2, 1, [3, 4]]"),
  ("case 5\n  [a, b] -> a\n  n -> [n]", 1000, "[5]"),
  (lengthsText, 10000, "[0, [1, 5], [2, 6, 5], [3, 7, []], [3, 7, [8]]]"),
  -- An arm of a fixed length above one of a least length takes its length.
  ("def f xs =\n  case xs\n    [a, b] -> 2\n    [x, ...r] -> [x, r]\n    y -> [y]\n[f [], f [5], f [5, 6], f [5, 6, 7], f 3]",
    10000, "[[[]], [5, []], 2, [5, [6, 7]], [3]]"),
  -- A name written twice is the later one, as in `fn x x -> x`.
  ("case [1, 2]\n  [a, a] -> a", 1000, "2")
]

def askTwiceText : String :=
"ask [1] (fn a ->
  ask [2, a] (fn b ->
    add a b))"

def askLoopText : String :=
"def sum n acc =
  case n
    0 -> acc
    m + 1 -> ask n (fn a -> sum m (add acc a))

sum 3 0"

/-- Program text, answers text, step budget for each turn, and the text the
    host must print: one `asked:` line for each request, then how the run ended. -/
def converses : List (String × String × Nat × String) := [
  (askTwiceText, "[]", 100000, "asked: [1]\nwaiting"),
  (askTwiceText, "[20]", 100000, "asked: [1]\nasked: [2, 20]\nwaiting"),
  (askTwiceText, "[20, 22]", 100000, "asked: [1]\nasked: [2, 20]\n42"),
  -- answers left over are not used
  (askTwiceText, "[20, 22, 5]", 100000, "asked: [1]\nasked: [2, 20]\n42"),
  -- the answers text is a program
  (askTwiceText, "[add 10 10, mul 2 11]", 100000, "asked: [1]\nasked: [2, 20]\n42"),
  (askLoopText, "[10, 20, 30]", 100000, "asked: 3\nasked: 2\nasked: 1\n60"),
  (askLoopText, "[10]", 100000, "asked: 3\nasked: 2\nwaiting"),
  -- a program that asks nothing
  ("add 1 2", "[]", 1000, "3"),
  ("add 1 2", "[9]", 1000, "3"),
  ("1 2", "[]", 1000, "error: wrong"),
  -- a function whose payload is a function, and a request built with one
  ("fn x -> x", "[]", 1000, "error: wrong"),
  ("ask (fn x -> x) (fn a -> a)", "[1]", 1000, "error: wrong"),
  -- a request carries no mark: any function a turn ends in is read as one
  ("fn x -> 42", "[]", 1000, "asked: 42\nwaiting"),
  ("fn x -> 42", "[7]", 1000, "asked: 42\n42"),
  -- an error after an answer keeps the requests made before it
  ("ask 1 (fn a -> a a)", "[1]", 1000, "asked: 1\nerror: wrong"),
  -- an answer can be code
  ("ask 0 (fn code -> interpret code)", "[quote (add 2 3)]", 100000, "asked: 0\n[0, [1, 5]]"),
  -- a turn that does not finish
  ("def loop x = loop x\nask 1 (fn a -> loop a)", "[1]", 1000,
    "asked: 1\nno result within 1000 steps of a turn"),
  ("def loop x = loop x\nloop 0", "[]", 1000, "no result within 1000 steps of a turn"),
  -- answers that are not an array, and answers that do not read
  ("ask 1 (fn a -> a)", "7", 1000, "answers: not an array"),
  ("ask 1 (fn a -> a)", "fn x -> x", 1000, "answers: not an array"),
  ("ask 1 (fn a -> a)", "[", 1000, "answers: syntax error: line 1, column 2: expected an expression"),
  ("f 1", "[]", 1000, "syntax error: line 1, column 1: unbound name `f`")
]

/-- Terms no surface text reads as, run on the machine: term, budget, text. -/
def runs : List (Term × Nat × String) := [
  (.var 2147483647, 100, "error: unbound 2147483647"),
  (.app (.var 4294967296) (num 1), 100, "error: unbound 4294967296"),
  (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))), 100,
    "no result within 100 steps")
]

/-- Outcomes that no surface program reaches directly, and their text. -/
def renders : List (Outcome × String) := [
  (.unbound 2147483647, "error: unbound 2147483647"),
  (.unbound 0, "error: unbound 0"),
  (.wrong, "error: wrong"),
  (.value (.data (.arr [.nat 1, .arr []])), "[1, []]"),
  (.value (.closure (.var 0) []), "<function>")
]

end Surface
