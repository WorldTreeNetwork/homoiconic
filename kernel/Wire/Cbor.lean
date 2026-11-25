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

theorem pushBE_congr : ∀ b n m out, (∀ j, j < b → (n >>> (8 * j)).toUInt8 = (m >>> (8 * j)).toUInt8) →
    pushBE b n out = pushBE b m out := by
  intro b
  induction b with
  | zero => intro n m out _; rfl
  | succ b ih =>
    intro n m out h
    rw [pushBE, pushBE, h b (by omega)]
    exact ih n m _ (fun j hj => h j (by omega))

theorem pushBE_add (a : Nat) : ∀ b n out, pushBE (a + b) n out = pushBE b n (pushBE a (n >>> (8 * b)) out) := by
  induction a with
  | zero => intro b n out; simp [pushBE]
  | succ a ih =>
    intro b n out
    rw [Nat.add_right_comm, pushBE, ih, pushBE, ← Nat.shiftRight_add, Nat.mul_add, Nat.add_comm (8 * b)]

theorem toUInt8_mod (n b j : Nat) (hj : j < b) :
    ((n % 2 ^ (8 * b)) >>> (8 * j)).toUInt8 = (n >>> (8 * j)).toUInt8 := by
  apply UInt8.toNat_inj.1
  simp only [Nat.toUInt8, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ (8 * b) = 2 ^ (8 * j) * 2 ^ (8 * (b - j)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self]
  have d : 2 ^ 8 ∣ 2 ^ (8 * (b - j)) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mod_mod_of_dvd _ d

/-- `pushBE`, split in halves: the high bytes from `n` shifted, the low from
    `n` reduced below their power of two, so no byte costs a shift of the
    whole number. -/
def pushBig (k n : Nat) (out : ByteArray) : ByteArray :=
  if k ≤ 32 then pushBE k n out
  else pushBig (k / 2) (n % 2 ^ (8 * (k / 2))) (pushBig (k - k / 2) (n >>> (8 * (k / 2))) out)
termination_by k
decreasing_by all_goals omega

theorem pushBig_eq : ∀ k n out, pushBig k n out = pushBE k n out := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro n out
    rw [pushBig]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega),
        pushBE_congr (k / 2) (n % 2 ^ (8 * (k / 2))) n _ (fun j hj => toUInt8_mod n _ j hj),
        ← pushBE_add, Nat.sub_add_cancel (by omega)]

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
    pushBig k n (pushHead 2 k (out.push 0xc2))

/-- Write the items of each list in `stack`, the first list first. A nested
    array is another list on the stack, not another call: a `cons` chain of
    about 66,000 items is that many nested arrays. The walk is one function
    that calls only itself, in tail position, so it is a loop whatever the C
    compiler does with calls between functions (`homoiconic-q59.72`). -/
partial def writeGo (stack : List (List Item)) (out : ByteArray) : ByteArray :=
  match stack with
  | [] => out
  | [] :: rest => writeGo rest out
  | (x :: xs) :: rest =>
    match x with
    | .nat n => writeGo (xs :: rest) (writeNat n out)
    | .name n => writeGo (xs :: rest) (writeNat n (pushHead 6 39 out))
    | .text t =>
        let b := (String.ofList t).toUTF8
        writeGo (xs :: rest) (pushHead 3 b.size out ++ b)
    | .bytes b => writeGo (xs :: rest) (pushHead 2 b.size out ++ b)
    | .arr ys => writeGo (ys :: xs :: rest) (pushHead 4 ys.length out)

def writeTo (i : Item) (out : ByteArray) : ByteArray := writeGo [[i]] out

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

theorem takeBE_acc (b : ByteArray) : ∀ k pos acc, takeBE b pos k acc = acc * 256 ^ k + takeBE b pos k 0 := by
  intro k
  induction k with
  | zero => intro pos acc; simp [takeBE]
  | succ k ih =>
    intro pos acc
    rw [takeBE, takeBE, ih, ih (acc := 0 * 256 + _)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 256 (256 ^ k)]

theorem takeBE_add (b : ByteArray) : ∀ h j pos,
    takeBE b pos (h + j) 0 = takeBE b pos h 0 * 256 ^ j + takeBE b (pos + h) j 0 := by
  intro h
  induction h with
  | zero => intro j pos; simp [takeBE]
  | succ h ih =>
    intro j pos
    have e1 : takeBE b pos (h + 1 + j) 0 = takeBE b (pos + 1) (h + j) (b.get! pos).toNat := by
      rw [Nat.add_right_comm, takeBE]; simp
    have e2 : takeBE b pos (h + 1) 0 = takeBE b (pos + 1) h (b.get! pos).toNat := by
      rw [takeBE]; simp
    rw [e1, e2, takeBE_acc b (h + j), takeBE_acc b h, ih, show pos + 1 + h = pos + (h + 1) by omega]
    simp only [Nat.add_mul, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc]

/-- `takeBE`, split in halves: `k` bytes at `pos` as a number, in the time of
    a few shifts of the whole number for each halving. -/
def bigBE (b : ByteArray) (pos k : Nat) : Nat :=
  if k ≤ 32 then takeBE b pos k 0
  else (bigBE b pos (k / 2) <<< (8 * (k - k / 2))) + bigBE b (pos + k / 2) (k - k / 2)
termination_by k
decreasing_by all_goals omega

theorem bigBE_eq (b : ByteArray) : ∀ k pos, bigBE b pos k = takeBE b pos k 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro pos
    rw [bigBE]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega), Nat.shiftLeft_eq, Nat.pow_mul,
        show (2 : Nat) ^ 8 = 256 from rfl, ← takeBE_add, Nat.add_sub_cancel' (by omega)]

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

/-- The head of a bignum's byte string, after its tag 2: how many bytes the
    number has and where they begin. A leading zero, and a number that fits an
    unsigned integer, are refused: with no leading zero, `k` bytes are a
    number below 2^64 exactly when `k` is at most 8, so the number need not
    be made to be refused. -/
def bigHead (b : ByteArray) (pos : Nat) : Except String (Nat × Nat) := do
  let (major, k, pos) ← readHead b pos
  if major != 2 then .error "a bignum that is not a byte string"
  else if pos + k > b.size then .error "the bytes end inside a value"
  else if k == 0 || b.get! pos == 0 then .error "a bignum with a leading zero"
  else if k ≤ 8 then .error "a bignum that fits an unsigned integer"
  else .ok (k, pos)

/-- The byte string of a bignum, after its tag 2: the number and the position
    after it, refused as `bigHead` refuses. The number is read by halves
    (`bigBE`, proved to be `takeBE`), so a number of 2 MiB is read in the
    time of a few shifts of it, not one for each byte (`homoiconic-q59.64`). -/
def readBig (b : ByteArray) (pos : Nat) : Except String (Nat × Nat) := do
  let (k, pos) ← bigHead b pos
  .ok (bigBE b pos k, pos + k)

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
          let (k, pos) ← bigHead b pos
          next (pos + k)
        else if n == 39 then do
          let (major, k, pos) ← readHead b pos
          if major == 0 then next pos
          else if major == 6 && k == 2 then do
            let (k, pos) ← bigHead b pos
            next (pos + k)
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
