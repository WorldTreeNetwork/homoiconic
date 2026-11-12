import Surface.Run
import Wire.Form

namespace Surface
open Reflect

def renderBytesError (msg : String) : String := "bytes error: " ++ msg

/-- Read a program from its byte form, compile, run the machine for `budget`
    steps, and render. The same run as `runText` gives the source. -/
def runBytes (bytes : ByteArray) (budget : Nat) : String :=
  match Wire.readProgram bytes with
  | .error msg => renderBytesError msg
  | .ok t => renderState budget (runUntil budget (load (compile t)))

/-- Read a program's source and give its byte form. The first byte answered is
    0 and the byte form follows, or it is 1 and the syntax error follows. -/
def sourceBytes (src : ByteArray) : ByteArray :=
  match read src with
  | .error msg => (ByteArray.empty.push 1) ++ (renderSyntaxError msg).toUTF8
  | .ok t => (ByteArray.empty.push 0) ++ Wire.programBytes t

end Surface
