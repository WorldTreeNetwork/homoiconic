import Circular.Encoding

namespace Circular

/- A construction language for readable binding; it adds no object primitive.
    Compilation erases names and produces only var, lam, and app. -/
namespace Builder
inductive Expr where
  | ref : String → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  deriving Repr

abbrev v := Expr.ref
abbrev ap := Expr.app

def lams (xs : List String) (body : Expr) : Expr := xs.foldr Expr.lam body
def apps (f : Expr) (xs : List Expr) : Expr := xs.foldl Expr.app f

def compile (ctx : List String) : Expr → Term
  | .ref x => .var (ctx.idxOf x)
  | .lam x b => .lam (compile (x :: ctx) b)
  | .app f a => .app (compile ctx f) (compile ctx a)

theorem compile_pure (e : Expr) : Pure (compile ctx e) := by
  induction e generalizing ctx with
  | ref => exact .var _
  | lam _ _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha

-- Scott data constructors. Each binding site uses a distinct name within
-- its helper. Inlining helpers preserves their lexical scopes.
def nil : Expr := lams ["n", "c"] (v "n")
def cons : Expr := lams ["h", "t", "n", "c"] (apps (v "c") [v "h", v "t"])
def ok : Expr := lams ["payload", "ok", "bad"] (ap (v "ok") (v "payload"))
def bad : Expr := lams ["index", "ok", "bad"] (ap (v "bad") (v "index"))
/-- The abstraction tag has two fields: encoded body and encoded environment. -/
def closure : Expr := lams ["body", "env", "v", "l", "a"]
  (apps (v "l") [v "body", v "env"])

def tail : Expr := lams ["xs"] (apps (v "xs") [nil, lams ["h", "t"] (v "t")])
def lookup : Expr := lams ["index", "env"]
  (apps (apps (v "index") [tail, v "env"])
    [ap bad (v "index"), lams ["h", "t"] (v "h")])

/-- The call-by-value fixed-point combinator; recursion is delayed by a lambda. -/
def fix : Expr :=
  let arm := lams ["x"] (ap (v "f")
    (lams ["arg"] (apps (v "x") [v "x", v "arg"])))
  lams ["f"] (ap arm arm)

/-- Recursion takes encoded program, then encoded environment. -/
def functional : Expr := lams ["self", "program", "env"]
  (apps (v "program")
    [ lams ["index"] (apps lookup [v "index", v "env"]),
      lams ["body"] (ap ok (apps closure [v "body", v "env"])),
      lams ["fun", "arg"]
        (apps (apps (v "self") [v "fun", v "env"])
          [ lams ["funValue"]
              (apps (v "funValue")
                [ nil,
                  lams ["body", "captured"]
                    (apps (apps (v "self") [v "arg", v "env"])
                      [ lams ["argValue"]
                          (apps (v "self")
                            [ v "body",
                              apps cons [ap ok (v "argValue"), v "captured"] ]),
                        lams ["index"] (ap bad (v "index")) ]),
                  nil ]),
            lams ["index"] (ap bad (v "index")) ]) ])

def interpreter : Expr := lams ["input"]
  (apps (ap fix functional) [v "input", nil])
end Builder

/-- One finite closed pure object-language term. No semantic relation or
    evaluator occurs in this construction or in the generated syntax. -/
def interpreterBody : Term := Builder.compile [] Builder.interpreter

theorem interpreterBody_pure : Pure interpreterBody := Builder.compile_pure _
theorem interpreterBody_closed : Closed interpreterBody := by decide +kernel

/-- Quotation and payload projection are syntax operations, not evaluation. -/
def interpreterTerm : Term := .quote interpreterBody

def quotePayload : Term → Option Term
  | .quote t => some t
  | _ => none

@[simp] theorem interpreter_payload : quotePayload interpreterTerm = some interpreterBody := rfl

/-- Projecting the quote constructor does not invoke either evaluation relation. -/
def interpreterPayload : Term :=
  match interpreterTerm with
  | .quote payload => payload
  | _ => .var 0

@[simp] theorem interpreterPayload_eq : interpreterPayload = interpreterBody := rfl

/-- Execution uses the projected pure payload, and never quotes the input. -/
def interpreterApplication (p : Term) (h : Pure p) : Term :=
  .app interpreterPayload (encode p h)

theorem interpreterApplication_pure (h : Pure p) : Pure (interpreterApplication p h) :=
  .app interpreterBody_pure (encode_pure h)

end Circular
