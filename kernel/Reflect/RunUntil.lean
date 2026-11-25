import Reflect.Machine

namespace Reflect
variable [Ops]

/-- `run`, stopping as soon as the machine stops. It is the same function. -/
def runUntil : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | n + 1, .running c e stk frs => runUntil n (step (.running c e stk frs))

/-- How far reaching the variable `i` walks `env`: `i` places, or to its end
    when it is shorter. Found in that many places. -/
def reachIn {α : Type} : Nat → List α → Nat → Nat
  | 0, _, acc => acc
  | _, [], acc => acc
  | i + 1, _ :: env, acc => reachIn i env (acc + 1)

/-- The charge for the next step. A primitive costs what its table says. A
    step of the machine's own whose time grows with data costs what the table
    says for that data: reaching a variable (`Ops.reach` of how far it walks
    the environment), `succ` or
    `case` of a number and `cons` onto a text (`Ops.work`). Every other step
    costs one (`homoiconic-q59.73`). -/
def stepCost : State → Nat
  | .running (.prim _) _ (.data d :: .data (.nat n) :: _) _ => Ops.cost n d
  | .running (.prim _) _ (.data d :: .data (.name n) :: _) _ => Ops.cost n d
  | .running (.access i _) env _ _ => Ops.reach (reachIn i env 0)
  | .running (.succ _) _ (.data (.nat n) :: _) _ => Ops.work (.nat n)
  | .running (.succ _) _ (.data (.name n) :: _) _ => Ops.work (.name n)
  | .running (.dcase _ _ _ _ _) _ (.data (.nat n) :: _) _ => Ops.work (.nat n)
  | .running (.dcase _ _ _ _ _) _ (.data (.name n) :: _) _ => Ops.work (.name n)
  | .running (.cons _) _ (.data (.text cs) :: _) _ => Ops.work (.text cs)
  | _ => 1

/-- `stepCost s` when it is at most `cap`, and `cap + 1` when it is more
    (`stepCostWithin_eq`). An operation's charge is found by `Ops.costWithin`,
    which need not look at more of its argument than `cap` pays for. -/
def stepCostWithin (s : State) (cap : Nat) : Nat :=
  match s with
  | .running (.prim _) _ (.data d :: .data (.nat n) :: _) _ => Ops.costWithin n d cap
  | .running (.prim _) _ (.data d :: .data (.name n) :: _) _ => Ops.costWithin n d cap
  | s => min (stepCost s) (cap + 1)

theorem stepCostWithin_eq (s : State) (cap : Nat) :
    stepCostWithin s cap = min (stepCost s) (cap + 1) := by
  unfold stepCostWithin
  split
  · rw [Ops.costWithin_eq]; rfl
  · rw [Ops.costWithin_eq]; rfl
  · rfl

/-- `run`, charging `stepCost` for each step and stopping before a step the
    fuel cannot pay for. A primitive whose charge is above the fuel left does
    not run. When every charge is one, this is `runUntil`. -/
def runPriced : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | fuel + 1, s =>
      match stepCost s with
      | 0 => runPriced fuel (step s)
      | c + 1 =>
        if c + 1 ≤ fuel + 1 then runPriced (fuel - c) (step s) else s
termination_by fuel => fuel
decreasing_by all_goals omega

/-- `runPriced` as it runs: the charge is asked with the fuel as its cap, so a
    step the fuel cannot pay for is found out in no more time than the fuel
    pays for (`homoiconic-q59.73`). Proved equal (`runPriced_eq_within`). -/
def runPricedWithin : Nat → State → State
  | 0, s => s
  | _ + 1, .halted o => .halted o
  | _ + 1, .fault => .fault
  | fuel + 1, s =>
      match stepCostWithin s (fuel + 1) with
      | 0 => runPricedWithin fuel (step s)
      | c + 1 =>
        if c + 1 ≤ fuel + 1 then runPricedWithin (fuel - c) (step s) else s
termination_by fuel => fuel
decreasing_by all_goals omega

omit [Ops] in
@[csimp] theorem runPriced_eq_within : @runPriced = @runPricedWithin := by
  funext inst fuel s
  induction fuel using Nat.strongRecOn generalizing s with
  | _ fuel ih =>
    cases fuel with
    | zero => rw [runPriced, runPricedWithin]
    | succ fuel =>
      cases s with
      | halted o => rw [runPriced, runPricedWithin]
      | fault => rw [runPriced, runPricedWithin]
      | running c e stk frs =>
        rw [runPriced, runPricedWithin, stepCostWithin_eq]
        case x_2 => intro o h; cases h
        case x_3 => intro h; cases h
        case x_2 => intro o h; cases h
        case x_3 => intro h; cases h
        generalize hk : stepCost (.running c e stk frs) = k
        rcases k with _ | k
        · simp only [Nat.zero_min]; exact ih fuel (by omega) _
        · by_cases hle : k + 1 ≤ fuel + 1
          · rw [Nat.min_eq_left (by omega)]; simp only [hle, ite_true]
            exact ih _ (by omega) _
          · rw [Nat.min_eq_right (by omega)]; simp only [hle, ite_false]
            split <;> first | rfl | omega

end Reflect
