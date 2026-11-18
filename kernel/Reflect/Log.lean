import Reflect.Channel

/-!
The log of one machine. A *VM* is a program that makes requests
(`Reflect.Request`) together with the identifiers of the entries it has acted
on. A *log* is a list of entries, each an identifier and an answer. Handling an
entry answers the request the VM is waiting on, unless the VM has acted on that
identifier before or has finished; then the entry changes nothing. The state of
a VM is what handling its log, entry by entry from the start, leads to.

Nothing is added to the language. An identifier is data, and two entries are
the same delivery when their identifiers are equal. The theorems on handling a
log hold whatever the identifiers are.

A log that is read is *sealed*: an entry arrives as a mark and an answer, and
its identifier is the name `key` gives to the two together. When `key` gives
different names to different data, two sealed entries with one identifier are
one entry (`sealed_same`). The `key` the kernel uses is the Blake3 hash of the
entry's bytes (`Surface.Keep.entryName`); that it gives different names to
different data is assumed, as it is for every stored piece.
-/
namespace Reflect

mutual
  def Data.decEq : (a b : Data) → Decidable (a = b)
    | .nat m, .nat n =>
      if h : m = n then isTrue (h ▸ rfl) else isFalse (fun e => h (Data.nat.inj e))
    | .name m, .name n =>
      if h : m = n then isTrue (h ▸ rfl) else isFalse (fun e => h (Data.name.inj e))
    | .nat _, .arr _ => isFalse nofun
    | .nat _, .name _ => isFalse nofun
    | .arr _, .nat _ => isFalse nofun
    | .arr _, .name _ => isFalse nofun
    | .name _, .nat _ => isFalse nofun
    | .name _, .arr _ => isFalse nofun
    | .text s, .text t =>
      if h : s = t then isTrue (h ▸ rfl) else isFalse (fun e => h (Data.text.inj e))
    | .nat _, .text _ => isFalse nofun
    | .arr _, .text _ => isFalse nofun
    | .name _, .text _ => isFalse nofun
    | .text _, .nat _ => isFalse nofun
    | .text _, .arr _ => isFalse nofun
    | .text _, .name _ => isFalse nofun
    | .arr xs, .arr ys =>
      match Data.decEqList xs ys with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun e => h (Data.arr.inj e))
  def Data.decEqList : (xs ys : List Data) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse nofun
    | _ :: _, [] => isFalse nofun
    | x :: xs, y :: ys =>
      match Data.decEq x y, Data.decEqList xs ys with
      | isTrue h, isTrue h' => isTrue (by rw [h, h'])
      | isFalse h, _ => isFalse (fun e => h (List.cons.inj e).1)
      | _, isFalse h => isFalse (fun e => h (List.cons.inj e).2)
end

instance : DecidableEq Data := Data.decEq

/-- Membership by equality. The derived `==` on data is not used: nothing is
    proved about it. -/
instance (a : Data) (l : List Data) : Decidable (a ∈ l) :=
  decidable_of_iff (∃ x, x ∈ l ∧ a = x) ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨a, h, rfl⟩⟩

/-- One entry of a log. -/
structure Entry where
  /-- What makes two deliveries the same delivery. -/
  id : Data
  /-- The answer to the request the VM is waiting on. -/
  answer : Data

/-- The entry made of a mark and an answer: its identifier is the name `key`
    gives to the pair. The mark is not read; it tells apart two entries with
    one answer. -/
def Entry.seal (key : Data → Data) (mark answer : Data) : Entry :=
  ⟨key (.arr [mark, answer]), answer⟩

/-- `e` is the seal of some mark and its answer. -/
def Entry.Sealed (key : Data → Data) (e : Entry) : Prop :=
  ∃ mark, e = Entry.seal key mark e.answer

/-- A VM between entries: where its program stands, and the identifiers of the
    entries it has acted on, newest first. -/
structure Vm (C R : Type) where
  status : Status C R
  seen : List Data

/-- What an entry does. Every entry can be handled; evaluation that never
    finishes gives no next state. -/
inductive Handle {C R : Type} (S : Sys C R) : Vm C R → Entry → Vm C R → Prop where
  /-- The VM has acted on this identifier. -/
  | repeated {v e} (h : e.id ∈ v.seen) : Handle S v e v
  /-- The program has finished. The identifier is not recorded. -/
  | over {v e r} (hs : v.status = .finished r) : Handle S v e v
  /-- The request is answered and the program runs to its next request or its
      end. -/
  | answer {v e c p st} (h : e.id ∉ v.seen) (hs : v.status = .waiting c p)
      (ht : Turn S c e.answer st) : Handle S v e ⟨st, e.id :: v.seen⟩

/-- A log handled entry by entry. -/
inductive Replay {C R : Type} (S : Sys C R) : Vm C R → List Entry → Vm C R → Prop where
  | nil {v} : Replay S v [] v
  | cons {v e mid es v'} (h : Handle S v e mid) (rest : Replay S mid es v') :
      Replay S v (e :: es) v'

/-- A program before any entry: run to its first request or its end. -/
def Boot {C R : Type} (S : PSys C R) (p : Term) (v : Vm C R) : Prop :=
  ∃ r st, S.start p r ∧ Settle S.toSys r st ∧ v = ⟨st, []⟩

/-- The state of the VM of program `p` whose log is `log`. -/
def Logged {C R : Type} (S : PSys C R) (p : Term) (log : List Entry) (v : Vm C R) : Prop :=
  ∃ v₀, Boot S p v₀ ∧ Replay S.toSys v₀ log v

/-- The entries of a log that are the first with their identifier, given the
    identifiers `seen` before it. -/
def firsts (seen : List Data) : List Entry → List Entry
  | [] => []
  | e :: es => if e.id ∈ seen then firsts seen es else e :: firsts (e.id :: seen) es

/-- `v` does not act on `e`. -/
def Vm.Ignores {C R : Type} (v : Vm C R) (e : Entry) : Prop :=
  e.id ∈ v.seen ∨ ∃ r, v.status = .finished r

def Status.ending {C R : Type} : Status C R → Ending C R
  | .waiting c _ => .waiting c
  | .finished r => .finished r

def Vm.map {C R C' R' : Type} (f : R → R') (g : C → C') (v : Vm C R) : Vm C' R' :=
  ⟨v.status.map f g, v.seen⟩

variable [Ops]

/-! The executable VM, on the machine. Every machine run gets `budget` steps.
    `none` is a VM one of whose runs did not halt within the budget; it stays
    `none`, and says nothing about the program. -/

abbrev MVm := Vm MValue MOutcome

def handleRun (budget : Nat) : Option MVm → Entry → Option MVm
  | none, _ => none
  | some v, e =>
    if e.id ∈ v.seen then some v else
    match v.status with
    | .finished _ => some v
    | .waiting c _ =>
      match turnRun budget c e.answer with
      | some st => some ⟨st, e.id :: v.seen⟩
      | none => none

def bootRun (budget : Nat) (p : Term) : Option MVm :=
  match runUntil budget (load (compile p)) with
  | .halted w =>
    match settleRun budget w with
    | some st => some ⟨st, []⟩
    | none => none
  | _ => none

/-- The state of a VM is a fold over its log. -/
def vmRun (budget : Nat) (p : Term) (log : List Entry) : Option MVm :=
  log.foldl (handleRun budget) (bootRun budget p)

end Reflect
