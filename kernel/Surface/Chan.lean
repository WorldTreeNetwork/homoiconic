import Surface.Run
import Reflect.Channel

/-!
Processes and channels as text. A schedule is written as data: an array of
events, each `[0, i, n]` (process `i` is given the new name `n`), `[1, i]`
(process `i` starts a process), `[2, i, j]` (process `i` sends to process `j`)
or `[3, i, a]` (process `i` is answered `a` from outside). The schedule a run
went through is printed in the same form, so it can be given back.
Tested against examples; what the text reports is `Reflect.replay_true` and
`Reflect.auto_true`.
-/
namespace Surface
open Reflect

def eventData : Event → Data
  | .fresh i n => .arr [.nat 0, .nat i, .nat n]
  | .spawn i => .arr [.nat 1, .nat i]
  | .comm i j => .arr [.nat 2, .nat i, .nat j]
  | .answer i a => .arr [.nat 3, .nat i, a]

def dataEvent : Data → Option Event
  | .arr [.nat 0, .nat i, .nat n] => some (.fresh i n)
  | .arr [.nat 1, .nat i] => some (.spawn i)
  | .arr [.nat 2, .nat i, .nat j] => some (.comm i j)
  | .arr [.nat 3, .nat i, a] => some (.answer i a)
  | _ => none

/-- The events of a schedule, or the place of the first entry that is not one. -/
def dataEvents : Nat → List Data → Except Nat (List Event)
  | _, [] => .ok []
  | k, d :: ds =>
    match dataEvent d with
    | some ev => (dataEvents (k + 1) ds).map (ev :: ·)
    | none => .error k

def renderProcs : Nat → List (Proc MValue MOutcome) → String
  | _, [] => ""
  | i, q :: qs =>
    s!"process {i}: " ++
      (match q.status with
       | .waiting _ p => "waiting on " ++ renderData p
       | .finished w => renderMOutcome w) ++
      "; holds " ++ renderData (.arr (q.held.map .nat)) ++ "\n" ++ renderProcs (i + 1) qs

/-- The schedule that happened, each process, and how the run stopped. `more`:
    an event could still be chosen. -/
def renderRun (budget : Nat) (done : List Event) (cfg : MConfig) (stop : Stopped)
    (more : Bool) : String :=
  "schedule: " ++ renderData (.arr (done.map eventData)) ++ "\n" ++
    renderProcs 0 cfg.procs ++
    (match stop with
     | .ran => if more then "more can happen" else "nothing more can happen"
     | .refused ev => "refused: " ++ renderData (eventData ev) ++ " cannot happen"
     | .unfinished ev =>
       s!"no result within {budget} steps of a turn, at " ++ renderData (eventData ev))

/-- Read a program and run it as the first process. With an empty schedule
    text, events are chosen (`Reflect.pick`) until nothing can happen or
    `limit` events have. Otherwise the schedule text is a program whose result
    is an array of events, and exactly those are run, stopping at the first
    that cannot happen. Each machine run gets `budget` steps. -/
def channelsText (program schedule : ByteArray) (budget limit : Nat) : String :=
  match read program with
  | .error msg => renderSyntaxError msg
  | .ok t =>
    match beginRun budget t with
    | none => s!"no result within {budget} steps of a turn"
    | some c₀ =>
      if schedule.size == 0 then
        let r := autoRun budget limit c₀
        renderRun budget r.1 r.2.1 r.2.2.1 r.2.2.2
      else
        match read schedule with
        | .error msg => "schedule: " ++ renderSyntaxError msg
        | .ok scheduleTerm =>
          match runUntil budget (load (compile scheduleTerm)) with
          | .halted (.value (.data (.arr ds))) =>
            match dataEvents 0 ds with
            | .error k => s!"schedule: entry {k} is not an event"
            | .ok evs =>
              let r := schedRun budget c₀ evs
              renderRun budget r.1 r.2.1 r.2.2 (pick r.2.1).isSome
          | _ => "schedule: not an array"

end Surface
