import Reflect.Interpreter
import Reflect.Space

/-!
Requests. A program that needs something from outside finishes its turn with a
*request*: a function that holds a payload and the rest of the program. Nothing
is added to the language for this. `ask payload next` is an ordinary term, and
a request is an ordinary function value. The driver cannot tell a function built by `ask`
from any other, and treats every function a turn ends in as a request.

A *driver* outside the program reads the payload, and, given an answer, runs
the rest. The driver is defined once, over any way of evaluating (`Sys`), and
used three times: on direct evaluation, through the interpreter on data, and on
the machine.
-/
namespace Reflect

/-- `ask payload next`: a function that hands both parts to its caller. -/
def askTerm : Term := .lam (.lam (.lam (.app (.app (.var 0) (.var 2)) (.var 1))))

/-- With a request at index 0: its payload. -/
def payloadTerm : Term := .app (.var 0) (.lam (.lam (.var 1)))

/-- With a request at index 0: the rest of the program, given the answer `a`. -/
def resumeTerm (a : Data) : Term :=
  .app (.var 0) (.lam (.lam (.app (.var 0) (.lit a))))

/-- A way of evaluating, as the driver sees it. `C` is what a function result
    is held as, `R` what a result is held as. -/
structure Sys (C R : Type) where
  /-- Evaluate a term with the function `c` bound at index 0. -/
  eval : C → Term → R → Prop
  /-- The result is a function. -/
  fn : R → Option C
  /-- The result is data. -/
  dat : R → Option Data
  wrong : R

/-- How a driven run ends: with a result, or waiting on a request for which
    there is no answer yet. -/
inductive Ending (C R : Type) where
  | finished : R → Ending C R
  | waiting : C → Ending C R

def Ending.map {C R C' R' : Type} (f : R → R') (g : C → C') : Ending C R → Ending C' R'
  | .finished r => .finished (f r)
  | .waiting c => .waiting (g c)

/-- `Drive S r answers asked ending`: starting from the result `r` of a turn,
    with `answers` available, the program makes the requests `asked`, in order,
    and ends in `ending`.

    A result that is not a function ends the run. Every function is read as a
    request, whether or not `ask` built it: a request carries no mark. Its
    payload is what `payloadTerm` gives, and must be data. With no answer left the run waits, and the pending
    payload is the last entry of `asked`. Otherwise the rest of the program
    runs on the next answer. Answers left over when the run ends are unused. -/
inductive Drive {C R : Type} (S : Sys C R) : R → List Data → List Data → Ending C R → Prop where
  | stop {r as} (h : S.fn r = none) : Drive S r as [] (.finished r)
  | payloadFails {r c r' as} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hf : S.fn r' = none) (hd : S.dat r' = none) : Drive S r as [] (.finished r')
  | payloadFunction {r c r' c' as} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hf : S.fn r' = some c') : Drive S r as [] (.finished S.wrong)
  | wait {r c r' p} (h : S.fn r = some c) (hp : S.eval c payloadTerm r')
      (hd : S.dat r' = some p) : Drive S r [] [p] (.waiting c)
  | answer {r c r' p a r'' as asked e} (h : S.fn r = some c)
      (hp : S.eval c payloadTerm r') (hd : S.dat r' = some p)
      (hr : S.eval c (resumeTerm a) r'') (hrest : Drive S r'' as asked e) :
      Drive S r (a :: as) (p :: asked) e

variable [Ops]

/-- Direct evaluation. -/
def source : Sys Value Outcome where
  eval c t o := Direct [c] t o
  fn
    | .value (.closure b cap) => some (.closure b cap)
    | _ => none
  dat
    | .value (.data d) => some d
    | _ => none
  wrong := .wrong

/-- The interpreter, on data: results are outcomes as data, and a function is
    a closure as data. -/
def interpreted : Sys Data Data where
  eval c t w :=
    Direct [] (.app (.app evalTerm (.lit (reify t))) (.lit (.arr [c]))) (.value (.data w))
  fn
    | .arr [.nat 0, .arr [.nat 0, b, e]] => some (.arr [.nat 0, b, e])
    | _ => none
  dat
    | .arr [.nat 0, .arr [.nat 1, d]] => some d
    | _ => none
  wrong := .arr [.nat 2]

/-- The machine. -/
def machine : Sys MValue MOutcome where
  eval c t w := ∃ n, run n (.running (compile t) [c] [] []) = .halted w
  fn
    | .value (.closure k e) => some (.closure k e)
    | _ => none
  dat
    | .value (.data d) => some d
    | _ => none
  wrong := .wrong

/-- A program run against a list of answers, by direct evaluation. -/
def Interact (p : Term) (answers asked : List Data) (e : Ending Value Outcome) : Prop :=
  ∃ o, Direct [] p o ∧ Drive source o answers asked e

/-- The same, with every evaluation done by the interpreter on data. -/
def InteractI (p : Term) (answers asked : List Data) (e : Ending Data Data) : Prop :=
  ∃ w, Direct [] (.app interp (.lit (reify p))) (.value (.data w)) ∧
    Drive interpreted w answers asked e

/-- The same, on the machine. -/
def InteractM (p : Term) (answers asked : List Data) (e : Ending MValue MOutcome) : Prop :=
  ∃ n w, run n (load (compile p)) = .halted w ∧ Drive machine w answers asked e

/-- How the executable driver stops. `unfinished`: a turn did not halt within
    its budget, or within the cells a turn may make (`runTurn`): the two are
    not told apart here. -/
inductive Stop where
  | finished : MOutcome → Stop
  | waiting : MValue → Stop
  | unfinished : Stop

/-- The executable driver, on the machine. Each turn gets a budget of `budget`,
    charged as `runPriced` charges it: one a step, and an operation its cost.
    A turn is `runTurn`: it may make `turnSpace` cells and no more. -/
def driveRun (budget : Nat) : List Data → MOutcome → List Data × Stop
  | as, .value (.closure k e) =>
    match runTurn budget (.running (compile payloadTerm) [.closure k e] [] []) with
    | .halted (.value (.data p)) =>
      match as with
      | [] => ([p], .waiting (.closure k e))
      | a :: rest =>
        match runTurn budget (.running (compile (resumeTerm a)) [.closure k e] [] []) with
        | .halted w =>
          let r := driveRun budget rest w
          (p :: r.1, r.2)
        | _ => ([p], .unfinished)
    | .halted (.value (.closure _ _)) => ([], .finished .wrong)
    | .halted w => ([], .finished w)
    | _ => ([], .unfinished)
  | _, w => ([], .finished w)

/-- `driveRun` with the payloads asked so far in `acc`, newest first: a loop,
    not a call for each answer (`homoiconic-q59.78`). -/
def driveGo (budget : Nat) (acc : List Data) : List Data → MOutcome → List Data × Stop
  | as, .value (.closure k e) =>
    match runTurn budget (.running (compile payloadTerm) [.closure k e] [] []) with
    | .halted (.value (.data p)) =>
      match as with
      | [] => ((p :: acc).reverse, .waiting (.closure k e))
      | a :: rest =>
        match runTurn budget (.running (compile (resumeTerm a)) [.closure k e] [] []) with
        | .halted w => driveGo budget (p :: acc) rest w
        | _ => ((p :: acc).reverse, .unfinished)
    | .halted (.value (.closure _ _)) => (acc.reverse, .finished .wrong)
    | .halted w => (acc.reverse, .finished w)
    | _ => (acc.reverse, .unfinished)
  | _, w => (acc.reverse, .finished w)

theorem driveGo_eq (budget : Nat) : ∀ (as : List Data) (w : MOutcome) (acc : List Data),
    driveGo budget acc as w = (acc.reverse ++ (driveRun budget as w).1, (driveRun budget as w).2) := by
  intro as
  induction as with
  | nil =>
    intro w acc
    by_cases hw : ∃ k e, w = .value (.closure k e)
    · obtain ⟨k, e, rfl⟩ := hw
      rw [driveGo, driveRun]
      split <;> simp_all
    · have h' : ∀ k e, w = .value (.closure k e) → False := fun k e x => hw ⟨k, e, x⟩
      rw [driveGo.eq_2 _ _ _ _ h', driveRun.eq_2 _ _ _ h']; simp
  | cons a rest ih =>
    intro w acc
    by_cases hw : ∃ k e, w = .value (.closure k e)
    · obtain ⟨k, e, rfl⟩ := hw
      rw [driveGo, driveRun]
      split
      · simp only []
        split
        · rw [ih]; simp
        · simp
      · simp
      · simp
      · simp
    · have h' : ∀ k e, w = .value (.closure k e) → False := fun k e x => hw ⟨k, e, x⟩
      rw [driveGo.eq_2 _ _ _ _ h', driveRun.eq_2 _ _ _ h']; simp

def driveRunWalk (budget : Nat) (as : List Data) (w : MOutcome) : List Data × Stop :=
  driveGo budget [] as w

omit [Ops] in
@[csimp] theorem driveRun_eq_walk : @driveRun = @driveRunWalk := by
  funext inst budget as w
  simp [driveRunWalk, driveGo_eq]

/-- Run a program against a list of answers on the machine. -/
def converse (budget : Nat) (p : Term) (answers : List Data) : List Data × Stop :=
  match runTurn budget (load (compile p)) with
  | .halted w => driveRun budget answers w
  | _ => ([], .unfinished)

end Reflect
