import Surface.Run
import Surface.Bytes
import Surface.Keep
import Surface.Chan
import Surface.Cross

namespace Surface.Host

/-- Native-only byte copy. The caller lends `length`
    readable bytes for this call. -/
@[extern "kernel_copy_bytes"]
private unsafe def copyBytes (_address _length : USize) : ByteArray :=
  panic! "kernel_copy_bytes requires the native FFI bridge"

/-- Native-only: store `bytes` at `out` when they fit in `capacity`, and answer
    how many bytes there are. Nothing is written when they do not fit. -/
@[extern "reflect_store_bytes"]
private unsafe opaque storeBytes (out capacity : USize) (bytes : @& ByteArray) : USize

/-- C ABI: program pointer and length, output pointer and capacity, step budget.
    Returns the number of bytes the rendering needs. If that is more than
    `capacity`, nothing was written and the caller calls again with more room. -/
@[export reflect_run]
unsafe def reflectRun (program length out capacity : USize) (budget : UInt64) : USize :=
  let text := Surface.runText (copyBytes program length) budget.toNat
  storeBytes out capacity text.toUTF8

/-- C ABI: program pointer and length, answers pointer and length, output
    pointer and capacity, step budget for each turn. Returns the number of
    bytes the rendering needs, as `reflect_run` does. -/
@[export reflect_converse]
unsafe def reflectConverse (program length answers answersLength out capacity : USize)
    (budget : UInt64) : USize :=
  let text := Surface.converseText (copyBytes program length)
    (copyBytes answers answersLength) budget.toNat
  storeBytes out capacity text.toUTF8

/-- C ABI: program pointer and length, schedule pointer and length, output
    pointer and capacity, step budget for each machine run, and the most events
    to choose when the schedule is empty. Returns the number of bytes the
    rendering needs, as `reflect_run` does. -/
@[export reflect_channels]
unsafe def reflectChannels (program length schedule scheduleLength out capacity : USize)
    (budget limit : UInt64) : USize :=
  let text := Surface.channelsText (copyBytes program length)
    (copyBytes schedule scheduleLength) budget.toNat limit.toNat
  storeBytes out capacity text.toUTF8

/-- C ABI: program wire bytes in, bounded-run reply bytes out. Returns how many
    bytes the reply needs. Writes nothing when they do not fit. -/
@[export reflect_reply_bytes]
unsafe def reflectReplyBytes (program length out capacity : USize) (budget : UInt64) : USize :=
  storeBytes out capacity (Surface.replyBytes (copyBytes program length) budget.toNat)

/-! A guest of a run on two machines (`Surface.Cross`). The guest is a Lean
    value the image holds between calls and cannot look inside, as a kept
    session is; a call that takes it uses it up. -/

/-- C ABI: begin a guest. `flags` bit 0: this guest has the program, given in
    its byte form, and starts it as its first process. Bit 1: its start
    requests go to the peer. Bit 2: of the peer's sends it can take, it takes
    the newest first. `me` and `peer` are the two guests' names, as text. -/
@[export reflect_cross_start]
unsafe def crossStart (program length me meLength peer peerLength : USize) (budget : UInt64)
    (flags : UInt8) : Cross.Guest :=
  Cross.start (copyBytes program length)
    ((String.fromUTF8? (copyBytes me meLength)).getD "")
    ((String.fromUTF8? (copyBytes peer peerLength)).getD "")
    budget.toNat (flags &&& 1 == 1) (flags &&& 2 == 2) (flags &&& 4 == 4)

/-- C ABI: work until nothing is possible, or `Cross.workLimit` steps. -/
@[export reflect_cross_work]
def crossWork (g : Cross.Guest) : Cross.Guest := g.work Cross.workLimit

/-- C ABI: take a batch from the peer. -/
@[export reflect_cross_take]
unsafe def crossTake (g : Cross.Guest) (batch length : USize) : Cross.Guest :=
  g.take (copyBytes batch length)

/-- C ABI: the batch for the peer, of at most `capacity` bytes. -/
@[export reflect_cross_batch]
unsafe def crossBatch (g : Cross.Guest) (out capacity : USize) : USize :=
  storeBytes out capacity (g.batch (capacity.toNat - 256))

/-- C ABI: 0 there is work, 1 resting, 2 closed, 3 failed. -/
@[export reflect_cross_state]
def crossState (g : Cross.Guest) : UInt8 := g.state

/-- C ABI: the guest's record, as text. -/
@[export reflect_cross_record]
unsafe def crossRecord (g : Cross.Guest) (out capacity : USize) : USize :=
  storeBytes out capacity g.record.toUTF8

/-- C ABI: check two guests' records against a program's bytes. `a` is the
    record of the guest that had the program. Answers `accepted` and the
    replay, or `refused` and the reason. -/
@[export reflect_cross_check]
unsafe def crossCheck (program length a aLength b bLength out capacity : USize) : USize :=
  storeBytes out capacity
    (Cross.check (copyBytes program length) (copyBytes a aLength) (copyBytes b bLength)).toUTF8

/-- Check-only hook: a record with its chain and head made again from its
    entries, as a guest that lies would hand it over. -/
@[export reflect_cross_reseal]
unsafe def crossReseal (record length out capacity : USize) : USize :=
  storeBytes out capacity (Cross.reseal (copyBytes record length)).toUTF8

/-- Build-only hook: a Lean abort the network check can ask for. -/
@[export reflect_abort_alloc]
unsafe def reflectAbortAlloc (_: USize) : USize :=
  panic! "allocation failure"

/-- C ABI: as `reflect_run`, for a program given in its byte form. -/
@[export reflect_run_bytes]
unsafe def reflectRunBytes (program length out capacity : USize) (budget : UInt64) : USize :=
  let text := Surface.runBytes (copyBytes program length) budget.toNat
  storeBytes out capacity text.toUTF8

/-- C ABI: as `reflect_run`, but the program runs through `levels`
    interpreters: the closed term `interp` on the program as data, on the
    machine. Level 0 runs the program itself. `flags` bit 0 is set when the
    program is given in its byte form, not as source. Bit 1 is set to write a
    result that is a text raw, with no quotes and no escapes. -/
@[export reflect_interp]
unsafe def reflectInterp (program length out capacity : USize) (budget : UInt64)
    (levels : UInt32) (flags : UInt8) : USize :=
  let input := copyBytes program length
  let asText := flags &&& 2 == 2
  let text := if flags &&& 1 == 1 then
      Surface.interpBytes input levels.toNat budget.toNat asText
    else Surface.interpText input levels.toNat budget.toNat asText
  storeBytes out capacity text.toUTF8

/-- C ABI: the most levels `reflect_interp` runs a program through
    (`Surface.maxLevels`). The argument is ignored. A host asks for it to
    refuse more levels on its own line before calling `reflect_interp`, which
    answers `Surface.levelsError` for them itself. -/
@[export reflect_max_levels]
def reflectMaxLevels (_ : UInt32) : UInt32 := Surface.maxLevels.toUInt32

/-- C ABI: program source pointer and length, output pointer and capacity.
    Answers one status byte, then the program's byte form (status 0) or the
    syntax error (status 1). Returns the number of bytes needed. -/
@[export reflect_source_bytes]
unsafe def reflectSourceBytes (program length out capacity : USize) : USize :=
  storeBytes out capacity (Surface.sourceBytes (copyBytes program length))

/-! A turn against a store. The session is a Lean value the host holds between
    calls and cannot look inside. Every call that takes a session uses it up,
    as Lean's exported functions do; a caller that will use the session again
    calls `kernel_retain` on it first (`ffi.c`). -/

/-- C ABI: begin a program from its source. -/
@[export reflect_keep_start]
unsafe def keepStart (program length : USize) (budget : UInt64) : Keep.Session :=
  Keep.start (copyBytes program length) budget.toNat

/-- C ABI: answer the waiting program stored under the root named by the text
    at `root`, with the result of the program at `answer`. -/
@[export reflect_keep_answer]
unsafe def keepAnswer (root rootLength answer answerLength : USize) (budget : UInt64) :
    Keep.Session :=
  Keep.answer ((String.fromUTF8? (copyBytes root rootLength)).getD "")
    (copyBytes answer answerLength) budget.toNat

/-- C ABI: a VM from the start: the program at `program` handles the log at
    `log`, a program whose result is an array of `[identifier, answer]`. -/
@[export reflect_vm_start]
unsafe def vmStart (program length log logLength : USize) (budget : UInt64) : Keep.Session :=
  Keep.vmStart (copyBytes program length) (copyBytes log logLength) budget.toNat

/-- C ABI: a VM from the state kept under the root named by the text at
    `root`: it handles the log at `log` from there. -/
@[export reflect_vm_from]
unsafe def vmFrom (root rootLength log logLength : USize) (budget : UInt64) : Keep.Session :=
  Keep.vmFrom ((String.fromUTF8? (copyBytes root rootLength)).getD "")
    (copyBytes log logLength) budget.toNat

/-- C ABI: a node from the start: the program at `program` is the first
    process, and the log at `log`, a program whose result is an array of
    `[identifier, event]`, is applied. -/
@[export reflect_node_start]
unsafe def nodeStart (program length log logLength : USize) (budget : UInt64) : Keep.Session :=
  Keep.nodeStart (copyBytes program length) (copyBytes log logLength) budget.toNat

/-- C ABI: a node from the one kept under the root named by the text at
    `root`: the log at `log` is applied from there. -/
@[export reflect_node_from]
unsafe def nodeFrom (root rootLength log logLength : USize) (budget : UInt64) : Keep.Session :=
  Keep.nodeFrom ((String.fromUTF8? (copyBytes root rootLength)).getD "")
    (copyBytes log logLength) budget.toNat

/-- C ABI: the name of the piece the session needs, as 64 hex digits; no bytes
    when it needs none. Returns the number of bytes. -/
@[export reflect_keep_need]
unsafe def keepNeed (s : Keep.Session) (out capacity : USize) : USize :=
  storeBytes out capacity (match s.need with
    | some r => (Keep.hex r).toUTF8
    | none => ByteArray.empty)

/-- C ABI: supply the needed piece. The session passed in is used up. -/
@[export reflect_keep_give]
unsafe def keepGive (s : Keep.Session) (piece length : USize) : Keep.Session :=
  Keep.give s (copyBytes piece length)

/-- C ABI: how many pieces the session has to be stored. -/
@[export reflect_keep_count]
def keepCount (s : Keep.Session) : USize := s.written.size.toUSize

/-- C ABI: the name of piece `index` to be stored, as 64 hex digits. -/
@[export reflect_keep_name]
unsafe def keepName (s : Keep.Session) (index out capacity : USize) : USize :=
  storeBytes out capacity (Keep.hex (s.written[index.toNat]!).1).toUTF8

/-- C ABI: the bytes of piece `index` to be stored. -/
@[export reflect_keep_piece]
unsafe def keepPiece (s : Keep.Session) (index out capacity : USize) : USize :=
  storeBytes out capacity (s.written[index.toNat]!).2

/-- C ABI: what the turn says. Empty while a piece is needed. -/
@[export reflect_keep_text]
unsafe def keepText (s : Keep.Session) (out capacity : USize) : USize :=
  storeBytes out capacity s.text.toUTF8

end Surface.Host
