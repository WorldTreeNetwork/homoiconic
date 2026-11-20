import Surface.Read
import Surface.Chan
import Reflect.Channel
import Wire.Form

/-! A channel whose other end is another machine.

    The message that leaves is the wire form of `[closure, reply name]`.
    The other machine runs that closure and the message it sends on the reply
    name comes back. The schedule of the same program on one machine is the
    delivery order. Replaying it reaches the same result. A name is still a
    number; that a remote party cannot forge one is the host's hypothesis. -/

namespace Surface.Remote
open Reflect

def program : String :=
  "let worker = quote (fn reply -> ask [1, reply, 42] (fn sent -> []))\n" ++
  "let peer = quote (fn remote ->\n" ++
  "  ask [2, remote] (fn msg ->\n" ++
  "    let code =\n" ++
  "      case msg\n" ++
  "        [] -> 0\n" ++
  "        [h, ...rest] -> h\n" ++
  "    let reply =\n" ++
  "      case msg\n" ++
  "        [] -> 0\n" ++
  "        [h, ...rest] ->\n" ++
  "          case rest\n" ++
  "            [] -> 0\n" ++
  "            [k, ...more] -> k\n" ++
  "    ask [3, code, reply] (fn started -> [])))\n" ++
  "ask [0] (fn remote ->\n" ++
  "  ask [3, peer, remote] (fn started ->\n" ++
  "    ask [0] (fn reply ->\n" ++
  "      ask [1, remote, [worker, reply]] (fn sent ->\n" ++
  "        ask [2, reply] (fn n -> n)))))\n"

def budget : Nat := 100000
def limit : Nat := 40

def run : Option (List Event × MConfig × Stopped) :=
  match readString program with
  | .ok t =>
    match beginRun budget t with
    | some cfg =>
      let r := autoRun budget limit cfg
      some (r.1, r.2.1, r.2.2.1)
    | none => none
  | .error _ => none

/-- The first message a process sends: the closure and the reply name. -/
def offerOf : Option Data :=
  match readString program with
  | .error _ => none
  | .ok t =>
    match beginRun budget t with
    | none => none
    | some cfg => walk limit cfg
where
  walk : Nat → MConfig → Option Data
    | 0, _ => none
    | n + 1, cfg =>
      match pick cfg with
      | none => none
      | some ev =>
        match ev with
        | .comm i _ =>
          match cfg.procs[i]? with
          | some ⟨.waiting _ p, _⟩ =>
            match classify p with
            | .send _ v => some v
            | _ => none
          | _ => none
        | _ =>
          match stepRun budget cfg ev with
          | .ok mid => walk n mid
          | _ => none

def offerBytes : ByteArray :=
  match offerOf with
  | some v => Wire.write v
  | none => ByteArray.empty

/-- Run the closure carried in an offer. The bytes are the message it sends
    on the reply name. -/
def takeBytes (offer : ByteArray) : ByteArray :=
  match Wire.read offer with
  | .ok (.arr [body, .name n]) =>
    match unreify body with
    | some t =>
      match beginRun budget (.app t (.lit (.name n))) with
      | some ⟨⟨.waiting _ p, _⟩ :: _, _⟩ =>
        match classify p with
        | .send ch v => if ch == n then Wire.write v else ByteArray.empty
        | _ => ByteArray.empty
      | _ => ByteArray.empty
    | none => ByteArray.empty
  | _ => ByteArray.empty

def answerBytes : ByteArray := takeBytes offerBytes

def logText : String :=
  match run with
  | some (evs, _, _) => renderData (.arr (evs.map eventData))
  | none => ""

def finished (cfg : MConfig) : Option Nat :=
  match cfg.procs with
  | ⟨.finished (.value (.data (.nat n))), _⟩ :: _ => some n
  | _ => none

def same : Bool :=
  match run, offerOf, Wire.read answerBytes with
  | some (_, cfg, .ran), some _, .ok (.nat 42) => finished cfg == some 42
  | _, _, _ => false

def report : String :=
  if same then "ok   a remote closure replays to 42" else "FAIL a remote closure replays to 42"

end Surface.Remote
