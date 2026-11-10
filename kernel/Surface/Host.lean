import Surface.Run

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

end Surface.Host
