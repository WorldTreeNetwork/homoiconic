import Reflect.Syntax

/-! The byte form of a data value: the part of dCBOR that `Data` needs.

    A number below 2^64 is a CBOR unsigned integer in its shortest form. A
    larger number is tag 2 (a positive bignum) over its big-endian bytes with
    no leading zero. An array is a definite-length CBOR array. A name is tag 39
    (registered as "Identifier") over its number, in the form a number has. A
    text is a definite-length CBOR text string: its length in bytes, then its
    UTF-8. It is not normalised. A byte string, which is not data, is a
    definite-length CBOR byte string. Tag 2 for large numbers, tag 39 for names
    and text without normalisation are this project's rules, not dCBOR's.

    A text is a list of characters everywhere but here. The writer makes its
    bytes with `String.ofList` and `String.toUTF8`; the reader takes bytes that
    are UTF-8 with `String.fromUTF8?` and keeps `String.toList` of them.

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
  | text : List Char → Item
  | bytes : ByteArray → Item

/-- One array frame: items already converted, last first, and the data still
    to convert. Nested arrays are frames, not calls. `arriving` is the data
    still to enter; `none` means `made` is finished and goes to the frame. -/
private partial def ofDataGo (frames : List (List Item × List Data))
    (arriving : Option Data) (made : Item) : Item :=
  match arriving with
  | some (.nat n) => ofDataGo frames none (.nat n)
  | some (.name n) => ofDataGo frames none (.name n)
  | some (.text t) => ofDataGo frames none (.text t)
  | some (.arr []) => ofDataGo frames none (.arr [])
  | some (.arr (h :: t)) => ofDataGo (([], t) :: frames) (some h) made
  | none =>
    match frames with
    | [] => made
    | (done, []) :: rest => ofDataGo rest none (.arr (made :: done).reverse)
    | (done, next :: more) :: rest =>
      ofDataGo ((made :: done, more) :: rest) (some next) made

def Item.ofData (d : Data) : Item := ofDataGo [] (some d) (.nat 0)

def Item.ofDatas (xs : List Data) : List Item :=
  go xs []
where
  go : List Data → List Item → List Item
    | [], acc => acc.reverse
    | y :: ys, acc => go ys (Item.ofData y :: acc)

/-- `none` when there is a byte string anywhere in it. A nested array is a
    frame on the heap: a `cons` chain is that many nested three-item arrays. -/
private partial def toDataGo (frames : List (List Data × List Item))
    (arriving : Option Item) (made : Data) : Option Data :=
  match arriving with
  | some (.nat n) => toDataGo frames none (.nat n)
  | some (.name n) => toDataGo frames none (.name n)
  | some (.text t) => toDataGo frames none (.text t)
  | some (.bytes _) => none
  | some (.arr []) => toDataGo frames none (.arr [])
  | some (.arr (h :: t)) => toDataGo (([], t) :: frames) (some h) made
  | none =>
    match frames with
    | [] => some made
    | (done, []) :: rest => toDataGo rest none (.arr (made :: done).reverse)
    | (done, next :: more) :: rest =>
      toDataGo ((made :: done, more) :: rest) (some next) made

def Item.toData (i : Item) : Option Data := toDataGo [] (some i) (.nat 0)

def Item.toDatas (xs : List Item) : Option (List Data) :=
  go xs []
where
  go : List Item → List Data → Option (List Data)
    | [], acc => some acc.reverse
    | y :: ys, acc =>
      match Item.toData y with
      | none => none
      | some d => go ys (d :: acc)

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

/-- Write `cur`, then the sibling lists in `stack`, outermost last. A nested
    array is another list on the stack, not another call: a `cons` chain of
    about 66,000 items is that many nested arrays. -/
partial def writeGo (stack : List (List Item)) (cur : Item) (out : ByteArray) : ByteArray :=
  match cur with
  | .nat n => writeNext stack (writeNat n out)
  | .name n => writeNext stack (writeNat n (pushHead 6 39 out))
  | .text t =>
      let b := (String.ofList t).toUTF8
      writeNext stack (pushHead 3 b.size out ++ b)
  | .bytes b => writeNext stack (pushHead 2 b.size out ++ b)
  | .arr xs => writeNext (xs :: stack) (pushHead 4 xs.length out)
where
  writeNext (stack : List (List Item)) (out : ByteArray) : ByteArray :=
    match stack with
    | [] => out
    | [] :: rest => writeNext rest out
    | (x :: xs) :: rest => writeGo (xs :: rest) x out

def writeTo (i : Item) (out : ByteArray) : ByteArray := writeGo [] i out

def writeItem (i : Item) : ByteArray := writeTo i ByteArray.empty

/-- The byte form of a data value. A CBOR length is below 2^64, so an array of
    2^64 items or more, or a number (a name's number among them) or a text of
    2^64 bytes or more, has no byte form;
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

def notData : String := "a kind of value that is not a number, an array, a text or a name"

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
      else if major == 3 then
        -- A text: exactly `n` bytes that are UTF-8. Overlong forms, surrogates
        -- and numbers past U+10FFFF are not UTF-8.
        if pos + n > b.size then .error "the bytes end inside a value"
        else match String.fromUTF8? (b.extract pos (pos + n)) with
          | some s => next (.text s.toList) (pos + n)
          | none => .error "a text that is not UTF-8"
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

/-- The same walk as `readGo`, with the same refusals in the same order, that
    builds nothing: it keeps only how many values are still owed. Arrays the
    bytes open and never close cost a counter, not a frame each, so bytes that
    are no value are refused before anything is made from them. -/
def scanGo (b : ByteArray) : Nat → Nat → Nat → Except String Unit
  | 0, _, _ => .error "the bytes end inside a value"
  | fuel + 1, pos, owed => do
      let (major, n, pos) ← readHead b pos
      -- One value arrived; `owed` is at least one here.
      let next (pos : Nat) : Except String Unit :=
        if owed ≤ 1 then
          if pos == b.size then .ok () else .error "there are bytes after the value"
        else scanGo b fuel pos (owed - 1)
      if major == 0 then next pos
      else if major == 4 then
        if n == 0 then next pos
        else scanGo b fuel pos (owed - 1 + n)
      else if major == 2 then
        if pos + n > b.size then .error "the bytes end inside a value"
        else next (pos + n)
      else if major == 3 then
        if pos + n > b.size then .error "the bytes end inside a value"
        else match String.fromUTF8? (b.extract pos (pos + n)) with
          | some _ => next (pos + n)
          | none => .error "a text that is not UTF-8"
      else if major == 6 then
        if n == 2 then do
          let (_, pos) ← readBig b pos
          next pos
        else if n == 39 then do
          let (major, k, pos) ← readHead b pos
          if major == 0 then next pos
          else if major == 6 && k == 2 then do
            let (_, pos) ← readBig b pos
            next pos
          else .error "a name that is not over a number"
        else .error "a tag other than a positive bignum or a name"
      else .error notData

/-- Read one item from exactly these bytes. Bytes the writer would not have
    produced are refused, and they are refused by `scanGo` before `readGo`
    makes anything: what a refusal costs does not grow with how deep the
    bytes open arrays. Only bytes that are one value are built, and what they
    build is at most one item for each byte. -/
def readItem (b : ByteArray) : Except String Item := do
  scanGo b (b.size + 1) 0 1
  readGo b (b.size + 1) 0 []

/-- Read one data value from exactly these bytes. A byte string is refused. -/
def read (b : ByteArray) : Except String Data := do
  match (← readItem b).toData with
  | some d => .ok d
  | none => .error notData

end Wire
