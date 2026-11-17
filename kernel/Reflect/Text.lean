namespace Reflect

/-! A text is a list of characters. A `Char` is a Unicode scalar value, so a
    text holds nothing else. These three functions are all that the rest of the
    kernel needs to know of that; bytes are made and read at the UTF-8 boundary,
    outside `Reflect`. Nothing is proved about them. -/

/-- The first code point and the rest, or `none` for the empty text. The same
    split the two case rules of `Direct` make by pattern. -/
def Text.uncons? : List Char → Option (Nat × List Char)
  | [] => none
  | c :: r => some (c.toNat, r)

/-- The code points of a text, in order. -/
def Text.codes (t : List Char) : List Nat :=
  t.map Char.toNat

/-- The text of these code points, or `none` if one of them is not a Unicode
    scalar value: a surrogate, or a number past U+10FFFF. -/
def Text.ofCodes? (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n => if h : n.isValidChar then some (Char.ofNatAux n h) else none

end Reflect
