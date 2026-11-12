/-! Blake3, the 32-byte hash, written from the specification. This definition
    is what a reference to a stored piece means. It is tested against the
    official vectors (`KeepCheck.lean`) and nothing about it is proved; that
    two different inputs do not share a hash is assumed (D5).

    No keyed mode, no key derivation, no longer output. -/

namespace Wire.Blake3

def iv : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def perm : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

def chunkStart : UInt32 := 1
def chunkEnd : UInt32 := 2
def parent : UInt32 := 4
def root : UInt32 := 8

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def g (s : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := s[a]! + s[b]! + mx
  let vd := rotr (s[d]! ^^^ va) 16
  let vc := s[c]! + vd
  let vb := rotr (s[b]! ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((s.set! a va).set! b vb).set! c vc).set! d vd

def round (s m : Array UInt32) : Array UInt32 :=
  let s := g s 0 4 8 12 m[0]! m[1]!
  let s := g s 1 5 9 13 m[2]! m[3]!
  let s := g s 2 6 10 14 m[4]! m[5]!
  let s := g s 3 7 11 15 m[6]! m[7]!
  let s := g s 0 5 10 15 m[8]! m[9]!
  let s := g s 1 6 11 12 m[10]! m[11]!
  let s := g s 2 7 8 13 m[12]! m[13]!
  g s 3 4 9 14 m[14]! m[15]!

def permute (m : Array UInt32) : Array UInt32 := perm.map (m[·]!)

/-- `n` rounds, permuting the message between them. -/
def rounds : Nat → Array UInt32 → Array UInt32 → Array UInt32
  | 0, s, _ => s
  | 1, s, m => round s m
  | n + 1, s, m => rounds n (round s m) (permute m)

/-- The compression function, for its first eight words: the chaining value. -/
def compress (cv block : Array UInt32) (counter : Nat) (blockLen flags : UInt32) :
    Array UInt32 :=
  let s := cv ++ iv.extract 0 4 ++
    #[counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let s := rounds 7 s block
  (Array.range 8).map fun i => s[i]! ^^^ s[i + 8]!

/-- Sixteen little-endian words from `len` bytes at `off`, padded with zeros. -/
def blockWords (b : ByteArray) (off len : Nat) : Array UInt32 :=
  (Array.range 16).map fun i =>
    (List.range 4).foldl (fun w j =>
      let k := 4 * i + j
      if k < len then w ||| ((b.get! (off + k)).toUInt32 <<< (8 * j).toUInt32) else w) 0

/-- Blocks `i` and after of a chunk of `len` bytes at `off`. -/
def chunkBlocks (b : ByteArray) (off len counter : Nat) (last : Nat) (isRoot : Bool) :
    Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, cv => cv
  | fuel + 1, i, cv =>
      let blockLen := min 64 (len - 64 * i)
      let flags := (if i == 0 then chunkStart else 0) |||
        (if i == last then chunkEnd ||| (if isRoot then root else 0) else 0)
      let cv := compress cv (blockWords b (off + 64 * i) blockLen) counter blockLen.toUInt32 flags
      if i == last then cv else chunkBlocks b off len counter last isRoot fuel (i + 1) cv

/-- The chaining value of one chunk: at most 1024 bytes. -/
def chunkCv (b : ByteArray) (off len counter : Nat) (isRoot : Bool) : Array UInt32 :=
  let blocks := if len == 0 then 1 else (len + 63) / 64
  chunkBlocks b off len counter (blocks - 1) isRoot blocks 0 iv

/-- The chaining value of `len` bytes at `off`, whose first chunk is number
    `counter`. More than one chunk splits at the largest power of two chunks
    that leaves something on the right. The depth is at most 64. -/
def subtree (b : ByteArray) : Nat → Nat → Nat → Nat → Bool → Array UInt32
  | 0, _, _, _, _ => iv
  | fuel + 1, off, len, counter, isRoot =>
      if len ≤ 1024 then chunkCv b off len counter isRoot
      else
        let left := 1024 * 2 ^ Nat.log2 ((len - 1) / 1024)
        let l := subtree b fuel off left counter false
        let r := subtree b fuel (off + left) (len - left) (counter + left / 1024) false
        compress iv (l ++ r) 0 64 (parent ||| (if isRoot then root else 0))

/-- The 32-byte Blake3 hash. -/
def hash (b : ByteArray) : ByteArray :=
  (subtree b 64 0 b.size 0 true).foldl (fun (out : ByteArray) (w : UInt32) =>
    (((out.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8)
    ByteArray.empty

end Wire.Blake3
