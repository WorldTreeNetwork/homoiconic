import Reflect.Semantics

namespace Reflect

/- A named construction language. Compilation erases names and produces only
   object-language terms. Neither it nor its output mentions `Direct` or
   `evalFuel`. -/
namespace B
inductive Expr where
  | ref : String → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | lit : Data → Expr
  | succ : Expr → Expr
  | cons : Expr → Expr → Expr
  | dcase : Expr → Expr → String → Expr → Expr → String → String → Expr → Expr
  | prim : Expr → Expr → Expr

def compile (ctx : List String) : Expr → Term
  | .ref x => .var (ctx.idxOf x)
  | .lam x b => .lam (compile (x :: ctx) b)
  | .app f a => .app (compile ctx f) (compile ctx a)
  | .lit d => .lit d
  | .succ t => .succ (compile ctx t)
  | .cons a b => .cons (compile ctx a) (compile ctx b)
  | .dcase s z p sc n h t c =>
      .dcase (compile ctx s) (compile ctx z) (compile (p :: ctx) sc)
        (compile ctx n) (compile (t :: h :: ctx) c)
  | .prim c x => .prim (compile ctx c) (compile ctx x)

abbrev v := Expr.ref
def lams (xs : List String) (b : Expr) : Expr := xs.foldr Expr.lam b
def apps (f : Expr) (xs : List Expr) : Expr := xs.foldl Expr.app f
def letE (x : String) (e body : Expr) : Expr := .app (.lam x body) e
def num (k : Nat) : Expr := .lit (.nat k)
def nil : Expr := .lit (.arr [])
def list (xs : List Expr) : Expr := xs.foldr Expr.cons nil
/-- The `wrong` outcome as data. -/
def W : Expr := .lit (.arr [.nat 2])
def ok (x : Expr) : Expr := list [num 0, x]
def bad (i : Expr) : Expr := list [num 1, i]
def vclos (b e : Expr) : Expr := list [num 0, b, e]
def vdata (d : Expr) : Expr := list [num 1, d]

/-- Take an array apart, or answer `wrong`. -/
def uncons (e : Expr) (h t : String) (body : Expr) : Expr :=
  .dcase e W "_" W W h t body
/-- Zero or non-zero. -/
def ifZero (e z nz : Expr) : Expr := .dcase e z "_" nz W "_" "_" W
/-- Dispatch on a small tag. -/
def tagcase (tag : Expr) : List Expr → Expr
  | [] => W
  | b :: bs => .dcase tag b "tag'" (tagcase (v "tag'") bs) W "_" "_" W
/-- Continue with the payload of an `ok` result; pass any other result on. -/
def bind (r : String) (x : String) (k : Expr) : Expr :=
  uncons (v r) "bind.tag" "bind.rest"
    (ifZero (v "bind.tag") (uncons (v "bind.rest") x "_" k) (v r))

/-- The call-by-value fixed-point combinator. -/
def fix : Expr :=
  let arm := lams ["x"] (.app (v "f") (lams ["arg"] (apps (v "x") [v "x", v "arg"])))
  lams ["f"] (.app arm arm)

/-- Environment lookup. `orig` is the index reported when the lookup fails. -/
def lookBody : Expr :=
  .dcase (v "env") W "_" W (bad (v "orig")) "h" "t"
    (.dcase (v "n") (ok (v "h")) "m" (apps (v "go") [v "m", v "t", v "orig"]) W "_" "_" W)
def look : Expr := .app fix (lams ["go", "n", "env", "orig"] lookBody)

def self (c e : Expr) : Expr := apps (v "self") [c, e]

def evalBody : Expr :=
  let lookupE := apps look [v "code", v "env", v "code"]
  let application :=
    uncons (v "rest") "f" "r1" <| uncons (v "r1") "a" "_" <|
    letE "rf" (self (v "f") (v "env")) <| bind "rf" "vf" <|
    uncons (v "vf") "vt" "vr" <|
    ifZero (v "vt")
      (uncons (v "vr") "b" "r2" <| uncons (v "r2") "cap" "_" <|
        letE "ra" (self (v "a") (v "env")) <| bind "ra" "va" <|
        self (v "b") (.cons (v "va") (v "cap")))
      W
  let abstraction := uncons (v "rest") "b" "_" (ok (vclos (v "b") (v "env")))
  let literal := uncons (v "rest") "d" "_" (ok (vdata (v "d")))
  let successor :=
    uncons (v "rest") "t" "_" <|
    letE "r" (self (v "t") (v "env")) <| bind "r" "x" <|
    uncons (v "x") "xt" "xr" <|
    ifZero (v "xt") W
      (uncons (v "xr") "d" "_" <|
        .dcase (v "d") (ok (vdata (.succ (v "d")))) "_" (ok (vdata (.succ (v "d")))) W "_" "_" W)
  let construction :=
    uncons (v "rest") "a" "r1" <| uncons (v "r1") "b" "_" <|
    letE "ra" (self (v "a") (v "env")) <| bind "ra" "va" <|
    uncons (v "va") "at" "ar" <|
    ifZero (v "at") W
      (uncons (v "ar") "da" "_" <|
        letE "rb" (self (v "b") (v "env")) <| bind "rb" "vb" <|
        uncons (v "vb") "bt" "br" <|
        ifZero (v "bt") W
          (uncons (v "br") "db" "_" <|
            let built := ok (vdata (.cons (v "da") (v "db")))
            .dcase (v "db") W "_" W built "_" "_" built))
  let analysis :=
    uncons (v "rest") "s" "r1" <| uncons (v "r1") "z" "r2" <|
    uncons (v "r2") "sc" "r3" <| uncons (v "r3") "ni" "r4" <|
    uncons (v "r4") "c" "_" <|
    letE "rs" (self (v "s") (v "env")) <| bind "rs" "vs" <|
    uncons (v "vs") "st" "sr" <|
    ifZero (v "st") W
      (uncons (v "sr") "d" "_" <|
        .dcase (v "d")
          (self (v "z") (v "env"))
          "m" (self (v "sc") (.cons (vdata (v "m")) (v "env")))
          (self (v "ni") (v "env"))
          "hd" "tl" (self (v "c")
            (.cons (vdata (v "tl")) (.cons (vdata (v "hd")) (v "env")))))
  let operation :=
    uncons (v "rest") "c" "r1" <| uncons (v "r1") "x" "_" <|
    letE "rc" (self (v "c") (v "env")) <| bind "rc" "vc" <|
    uncons (v "vc") "ct" "cr" <|
    ifZero (v "ct") W
      (uncons (v "cr") "dc" "_" <|
        let argument :=
          letE "rx" (self (v "x") (v "env")) <| bind "rx" "vx" <|
          uncons (v "vx") "xt" "xr" <|
          ifZero (v "xt") W
            (uncons (v "xr") "dx" "_" <| ok (vdata (.prim (v "dc") (v "dx"))))
        .dcase (v "dc") argument "_" argument W "_" "_" W)
  .dcase (v "code") lookupE "_" lookupE W "tag" "rest"
    (tagcase (v "tag")
      [application, abstraction, literal, successor, construction, analysis, operation])

def eval : Expr := .app fix (lams ["self", "code", "env"] evalBody)
def interpreter : Expr := lams ["input"] (apps eval [v "input", nil])
end B

/-- The evaluator as a term: it takes a program as data, then an environment
    as data, and answers with the outcome as data. -/
def evalTerm : Term := B.compile [] B.eval

/-- One closed term. It takes a program as data at the empty environment. -/
def interp : Term := B.compile [] B.interpreter

/-- Interpreter depth: `level (k + 1) p` interprets `level k p`. -/
def level : Nat → Term → Term
  | 0, p => p
  | k + 1, p => .app interp (.lit (reify (level k p)))

/-- The outcome seen through `k` interpreters. -/
def lift : Nat → Outcome → Outcome
  | 0, o => o
  | k + 1, o => .value (.data (reifyOutcome (lift k o)))

end Reflect
