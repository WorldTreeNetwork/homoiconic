import Reflect.Syntax

/-! The byte form of a data value: the part of dCBOR that `Data` needs.

    A number below 2^64 is a CBOR unsigned integer in its shortest form. A
    larger number is tag 2 (a positive bignum) over its big-endian bytes with
    no leading zero. An array is a definite-length CBOR array. A name is tag 39
    (registered as "Identifier") over its number, in the form a number has. A
    byte string, which is not data, is a definite-length CBOR byte string.
    Tag 2 for large numbers and tag 39 for names are this project's rules, not
    dCBOR's.

    The reader is strict: it accepts exactly the bytes the writer produces, so
    a value has one byte form. Nothing here is proved. It is tested
    (`WireCheck.lean`). -/

namespace Wire
open Reflect

/-- What the reader and writer handle: data, and byte strings. A byte string
    is not data. It is how a reference to a stored piece is written
    (`Wire.Piece`); a program cannot hold one. -/
inductive Item where
  | nat : Nat → Item
  | arr : List Item → Item
  | name : Nat → Item
  | bytes : ByteArray → Item

mutual
  def Item.ofData : Data → Item
    | .nat n => .nat n
    | .name n => .name n
    | .arr xs => .arr (Item.ofDatas xs)
  def Item.ofDatas : List Data → List Item
    | [] => []
    | x :: xs => Item.ofData x :: Item.ofDatas xs
end

mutual
  /-- `none` when there is a byte string anywhere in it. -/
  def Item.toData : Item → Option Data
    | .nat n => some (.nat n)
    | .name n => some (.name n)
    | .arr xs => (Item.toDatas xs).map .arr
    | .bytes _ => none
  def Item.toDatas : List Item → Option (List Data)
    | [] => some []
    | x :: xs =>
        match Item.toData x, Item.toDatas xs with
        | some d, some ds => some (d :: ds)
        | _, _ => none
end

/-- The low `k` bytes of `n`, most significant first, appended to `out`. -/
def pushBE : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | k + 1, n, out => pushBE k n (out.push (n >>> (8 * k)).toUInt8)

/-- How many bytes `n` needs with no leading zero; zero needs none. -/
def byteLength (n : Nat) : Nat := (Nat.log2 n + 8) / 8 * (if n == 0 then 0 else 1)

/-- A CBOR head: the major type and its argument, in the shortest form. -/
def pushHead (major : UInt8) (n : Nat) (out : ByteArray) : ByteArray :=
  let m := major <<< 5
  if n < 24 then out.push (m ||| n.toUInt8)
  else if n < 0x100 then pushBE 1 n (out.push (m ||| 24))
  else if n < 0x10000 then pushBE 2 n (out.push (m ||| 25))
  else if n < 0x100000000 then pushBE 4 n (out.push (m ||| 26))
  else pushBE 8 n (out.push (m ||| 27))

def limit : Nat := 0x10000000000000000

/-- A number: an unsigned integer below 2^64, tag 2 over its bytes from there. -/
def writeNat (n : Nat) (out : ByteArray) : ByteArray :=
  if n < limit then pushHead 0 n out
  else
    let k := byteLength n
    pushBE k n (pushHead 2 k (out.push 0xc2))

mutual
  def writeTo : Item → ByteArray → ByteArray
    | .nat n, out => writeNat n out
    | .name n, out => writeNat n (pushHead 6 39 out)
    | .arr xs, out => writeAll xs (pushHead 4 xs.length out)
    | .bytes b, out => pushHead 2 b.size out ++ b
  def writeAll : List Item → ByteArray → ByteArray
    | [], out => out
    | x :: xs, out => writeAll xs (writeTo x out)
end

def writeItem (i : Item) : ByteArray := writeTo i ByteArray.empty

/-- The byte form of a data value. A CBOR length is below 2^64, so an array of
    2^64 items or more, or a number (a name's number among them) of 2^64 bytes
    or more, has no byte form;
    for those the bytes written are not read back. No such value fits in a
    machine. -/
def write (d : Data) : ByteArray := writeItem (.ofData d)

/-- `k` bytes at `pos` as a number, most significant first. -/
def takeBE (b : ByteArray) (pos : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => takeBE b (pos + 1) k (acc * 256 + (b.get! pos).toNat)

/-- Read a head at `pos`: major type, argument, and the position after it.
    A longer form than the argument needs is refused. -/
def readHead (b : ByteArray) (pos : Nat) : Except String (UInt8 × Nat × Nat) :=
  if pos ≥ b.size then .error "the bytes end inside a value"
  else
    let byte := b.get! pos
    let major := byte >>> 5
    let info := (byte &&& 31).toNat
    let wide (k least : Nat) : Except String (UInt8 × Nat × Nat) :=
      if pos + 1 + k > b.size then .error "the bytes end inside a value"
      else
        let n := takeBE b (pos + 1) k 0
        if n < least then .error "a number or length is not in its shortest form"
        else .ok (major, n, pos + 1 + k)
    if info < 24 then .ok (major, info, pos + 1)
    else if info == 24 then wide 1 24
    else if info == 25 then wide 2 0x100
    else if info == 26 then wide 4 0x10000
    else if info == 27 then wide 8 0x100000000
    else .error "an indefinite length or a reserved form"

/-- An array being read: how many items are still to come, and those read so
    far, last first. -/
structure Frame where
  left : Nat
  items : List Item

/-- Hand a finished value to the array being read, closing every array it
    completes. `some` is the whole value. -/
def deliver (d : Item) : List Frame → Option Item × List Frame
  | [] => (some d, [])
  | f :: rest =>
      if f.left ≤ 1 then deliver (.arr (d :: f.items).reverse) rest
      else (none, { left := f.left - 1, items := d :: f.items } :: rest)

/-- The byte string of a bignum, after its tag 2: the number and the position
    after it. A leading zero, and a number that fits an unsigned integer, are
    refused. -/
def readBig (b : ByteArray) (pos : Nat) : Except String (Nat × Nat) := do
  let (major, k, pos) ← readHead b pos
  if major != 2 then .error "a bignum that is not a byte string"
  else if pos + k > b.size then .error "the bytes end inside a value"
  else if k == 0 || b.get! pos == 0 then .error "a bignum with a leading zero"
  else
    let v := takeBE b pos k 0
    if v < limit then .error "a bignum that fits an unsigned integer"
    else .ok (v, pos + k)

def notData : String := "a kind of value that is not a number or an array"

/-- One value is read each turn and each turn takes at least one byte, so
    `fuel` above the number of bytes is never used up. Arrays are kept on a
    list, not on the call stack, and nothing is reserved for a length before
    its items arrive. -/
def readGo (b : ByteArray) : Nat → Nat → List Frame → Except String Item
  | 0, _, _ => .error "the bytes end inside a value"
  | fuel + 1, pos, stack => do
      let (major, n, pos) ← readHead b pos
      let next (d : Item) (pos : Nat) : Except String Item :=
        match deliver d stack with
        | (some whole, _) =>
            if pos == b.size then .ok whole else .error "there are bytes after the value"
        | (none, stack) => readGo b fuel pos stack
      if major == 0 then next (.nat n) pos
      else if major == 4 then
        if n == 0 then next (.arr []) pos
        else readGo b fuel pos ({ left := n, items := [] } :: stack)
      else if major == 2 then
        if pos + n > b.size then .error "the bytes end inside a value"
        else next (.bytes (b.extract pos (pos + n))) (pos + n)
      else if major == 6 then
        if n == 2 then do
          let (v, pos) ← readBig b pos
          next (.nat v) pos
        else if n == 39 then do
          -- A name: the tag over a number in the number's own form, and
          -- nothing else. A name's number is not a name.
          let (major, k, pos) ← readHead b pos
          if major == 0 then next (.name k) pos
          else if major == 6 && k == 2 then do
            let (v, pos) ← readBig b pos
            next (.name v) pos
          else .error "a name that is not over a number"
        else .error "a tag other than a positive bignum or a name"
      else .error notData

/-- Read one item from exactly these bytes. Bytes the writer would not have
    produced are refused. -/
def readItem (b : ByteArray) : Except String Item := readGo b (b.size + 1) 0 []

/-- Read one data value from exactly these bytes. A byte string is refused. -/
def read (b : ByteArray) : Except String Data := do
  match (← readItem b).toData with
  | some d => .ok d
  | none => .error notData

end Wire
