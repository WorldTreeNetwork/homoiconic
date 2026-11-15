import Reflect.Request
import Reflect.Interpreter
import Reflect.Arith

/-!
The reader: program text to a `Reflect.Term`, or an error message with line and
column. Hand-written and total; recursion is bounded by fuel proportional to
the number of tokens, or goes down the syntax tree, never by `partial`. The
reader is tested against `Surface.reads` and `Surface.refused`; it is not
proved.

Pipeline: bytes → tokens (`lex`) → syntax tree with names (`parse`) → terms
with de Bruijn indices (`tr`). Layout is handled in the parser: a token that
starts a line ends the expression being read when its column is at or left of
the limit the construct was given (`Lim`).
-/
namespace Surface.Read
open Reflect

/-! ### Fixed constants of the translation -/

/-- The fixed point `def` uses for a self-call. -/
def recurT : Term := B.compile [] B.fix

/-- What a missing `case` arm reads as: applying a number, which is `wrong`. -/
def wrongTerm : Term := .app (.lit (.nat 0)) (.lit (.nat 0))

/-! ### Tokens -/

inductive Tk where
  | num (n : Nat)
  /-- A string literal, as its code points. -/
  | str (cs : List Nat)
  | name (s : String)
  | lparen | rparen | lbrack | rbrack
  | comma | dots | arrow | eq | plus | pipe | tilde
  deriving BEq

def Tk.show : Tk → String
  | .num n => toString n
  | .str _ => "a string"
  | .name s => s
  | .lparen => "("
  | .rparen => ")"
  | .lbrack => "["
  | .rbrack => "]"
  | .comma => ","
  | .dots => "..."
  | .arrow => "->"
  | .eq => "="
  | .plus => "+"
  | .pipe => "|>"
  | .tilde => "~"

/-- `line` counts from 1, `col` from 0; `first` marks the first token of its line. -/
structure Tok where
  kind : Tk
  line : Nat
  col : Nat
  first : Bool

def msgAt (line col : Nat) (msg : String) : String :=
  s!"line {line}, column {col + 1}: {msg}"

def Tok.fail (t : Tok) (msg : String) : String := msgAt t.line t.col msg

/-! ### Lexer -/

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isIdStart (c : UInt8) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isIdChar (c : UInt8) : Bool := isIdStart c || isDigit c || c == 39

def takeWhileB (p : UInt8 → Bool) : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | c :: cs =>
    if p c then
      let r := takeWhileB p cs
      (c :: r.1, r.2)
    else ([], c :: cs)

/-- Drop a comment up to, not including, the end of the line. -/
def dropLine : List UInt8 → List UInt8
  | [] => []
  | c :: cs => if c == 10 then c :: cs else dropLine cs

/-- Only blanks, a comment, or the end of the line remain on this line. -/
def restBlank (cs : List UInt8) : Bool :=
  match (takeWhileB (fun c => c == 32 || c == 9 || c == 13) cs).2 with
  | [] => true
  | c :: _ => c == 10 || c == 59

/-- One character inside quotes: a byte, or `\n`, `\t`, `\\`, `\"`, `\'`. Answers
    the byte it stands for, how many bytes of source it took, and the rest. -/
def lexChar : List UInt8 → Option (UInt8 × Nat × List UInt8)
  | 92 :: e :: rest =>
    if e == 110 then some (10, 2, rest)
    else if e == 116 then some (9, 2, rest)
    else if e == 92 || e == 34 || e == 39 then some (e, 2, rest)
    else none
  | c :: rest => if c == 10 || c == 92 then none else some (c, 1, rest)
  | [] => none

/-- The inside of a string literal up to its closing quote: the bytes it
    stands for, the source bytes taken (the closing quote among them), the rest. -/
def lexString : Nat → List UInt8 → Array UInt8 → Nat → Option (Array UInt8 × Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, 34 :: rest, acc, len => some (acc, len + 1, rest)
  | f + 1, cs, acc, len =>
    match lexChar cs with
    | some (b, k, rest) => lexString f rest (acc.push b) (len + k)
    | none => none

def lexGo : Nat → List UInt8 → Nat → Nat → Bool → Array Tok →
    Except String (Array Tok × Nat × Nat)
  | 0, _, line, col, _, _ => .error (msgAt line col "the input is too large to read")
  | _ + 1, [], line, col, _, acc => .ok (acc, line, col)
  | f + 1, c :: cs, line, col, fresh, acc =>
    if c == 10 then lexGo f cs (line + 1) 0 true acc
    else if c == 32 || c == 13 then lexGo f cs line (col + 1) fresh acc
    else if c == 9 then
      if fresh && !(restBlank cs) then
        .error (msgAt line col "tab in indentation; indent with spaces")
      else lexGo f cs line (col + 1) fresh acc
    else if c == 59 then lexGo f (dropLine cs) line col fresh acc
    else
      let tok (k : Tk) : Tok := { kind := k, line := line, col := col, first := fresh }
      let push (k : Tk) (len : Nat) (rest : List UInt8) :=
        lexGo f rest line (col + len) false (acc.push (tok k))
      if isDigit c then
        let r := takeWhileB isDigit (c :: cs)
        match r.2 with
        | d :: _ =>
          if isIdChar d then .error (msgAt line col "a number runs into letters")
          else push (.num (r.1.foldl (fun a d => a * 10 + (d.toNat - 48)) 0)) r.1.length r.2
        | [] => push (.num (r.1.foldl (fun a d => a * 10 + (d.toNat - 48)) 0)) r.1.length r.2
      else if isIdStart c then
        let r := takeWhileB isIdChar (c :: cs)
        push (.name (String.ofList (r.1.map fun b => Char.ofNat b.toNat))) r.1.length r.2
      else if c == 34 then
        match lexString (cs.length + 1) cs #[] 1 with
        | some (bytes, len, rest) =>
          match String.fromUTF8? (ByteArray.mk bytes) with
          | some text => push (.str (text.toList.map Char.toNat)) len rest
          | none => .error (msgAt line col "a string that is not UTF-8")
        | none => .error (msgAt line col
            "a string that does not end on its line, or an escape other than \\n \\t \\\\ \\\" \\'")
      else if c == 39 then
        match lexChar cs with
        | some (b, k, 39 :: rest) =>
          if b < 128 then push (.num b.toNat) (k + 2) rest
          else .error (msgAt line col "a character literal is one ASCII character")
        | _ => .error (msgAt line col "a character literal is one ASCII character between `'`")
      else if c == 40 then push .lparen 1 cs
      else if c == 41 then push .rparen 1 cs
      else if c == 91 then push .lbrack 1 cs
      else if c == 93 then push .rbrack 1 cs
      else if c == 44 then push .comma 1 cs
      else if c == 126 then push .tilde 1 cs
      else if c == 61 then push .eq 1 cs
      else if c == 43 then push .plus 1 cs
      else if c == 46 then
        match cs with
        | d :: e :: rest =>
          if d == 46 && e == 46 then push .dots 3 rest
          else .error (msgAt line col "a stray `.`; arrays continue with `...`")
        | _ => .error (msgAt line col "a stray `.`; arrays continue with `...`")
      else if c == 45 then
        if cs.head? == some 62 then push .arrow 2 cs.tail else
          .error (msgAt line col "a stray `-`; there is no subtraction, a function arrow is `->`")
      else if c == 124 then
        if cs.head? == some 62 then push .pipe 2 cs.tail else
          .error (msgAt line col "a stray `|`; the pipe is `|>`")
      else .error (msgAt line col "unexpected character; programs are ASCII text")

def lex (src : ByteArray) : Except String (Array Tok × Nat × Nat) :=
  lexGo (src.size + 1) src.data.toList 1 0 true #[]

/-! ### Syntax with names -/

abbrev Pos := Nat × Nat

def fmtPos (p : Pos) (msg : String) : String := msgAt p.1 p.2 msg

inductive Expr where
  | num : Nat → Expr
  | nil : Expr
  | ref : Pos → String → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | cons : Expr → Expr → Expr
  | succ : Expr → Expr
  | letE : String → Expr → Expr → Expr
  | defE : String → List String → Expr → Expr → Expr
  /-- Scrutinee; zero arm; successor name and arm; the array arms, a chain of
      `arm` in the order written; catch-all name and arm. An absent arm is
      `missing`. -/
  | caseE : Expr → Expr → String → Expr → Expr → String → Expr → Expr
  /-- One array arm of a `case` and the array arms after it: the names of the
      items, the name of the rest when the pattern ends in `...rest`, the body.
      The chain ends in `missing`. -/
  | arm : List String → Option String → Expr → Expr → Expr
  | quote : Pos → Expr → Expr
  | splice : Pos → Expr → Expr
  | missing : Expr

def Expr.isMissing : Expr → Bool
  | .missing => true
  | _ => false

/-- `arr items rest` is `[a, b]` when `rest` is absent, exactly that many
    items, and `[a, b, ...rest]` when it is present, at least that many. -/
inductive Pat where
  | zero | succ (m : String) | arr (items : List String) (rest : Option String)
  | any (x : String)

structure Arms where
  z : Option Expr := none
  sc : Option (String × Expr) := none
  /-- The array arms, in the order written. -/
  arrs : Array (List String × Option String × Expr) := #[]
  a : Option (String × Expr) := none

/-! ### Parser -/

/-- Where the current construct stops: at a first-on-line token whose column is
    at or left of the limit (`col`), at any first-on-line token (`line`), or never. -/
inductive Lim where
  | none
  | line
  | col (n : Nat)

def Lim.stops : Lim → Tok → Bool
  | .none, _ => false
  | .line, t => t.first
  | .col n, t => t.first && t.col ≤ n

structure PS where
  toks : Array Tok
  pos : Nat
  /-- The head token of the statement being read is not subject to its own limit. -/
  exempt : Nat
  /-- While a header is being read (binder names, a pattern, up to `=` or `->`),
      no token may be consumed that this limit stops. -/
  guard : Lim := .none
  eofLine : Nat
  eofCol : Nat

abbrev P := StateT PS (Except String)

def peekRaw : P (Option Tok) := do
  let s ← get
  pure s.toks[s.pos]?

def peek (l : Lim) : P (Option Tok) := do
  let s ← get
  match s.toks[s.pos]? with
  | none => pure none
  | some t => if s.pos != s.exempt && l.stops t then pure none else pure (some t)

def setGuard (l : Lim) : P Unit := modify fun s => { s with guard := l }

/-- Consume one token. Inside a header, a token on a new line that is not
    indented under the header is refused, so a header never swallows the next
    statement. -/
def advance : P Unit := do
  let s ← get
  match s.toks[s.pos]? with
  | some t =>
    if s.pos != s.exempt && s.guard.stops t then
      throw (t.fail "this line continues the line above and must be indented under it")
    else set { s with pos := s.pos + 1 }
  | none => set { s with pos := s.pos + 1 }

def failAt {α : Type} (t : Option Tok) (msg : String) : P α := do
  let s ← get
  match t with
  | some t => throw (t.fail msg)
  | none => throw (msgAt s.eofLine s.eofCol msg)

def failHere {α : Type} (msg : String) : P α := do
  failAt (← peekRaw) msg

def expectTok (k : Tk) : P Unit := do
  match ← peekRaw with
  | some t => if t.kind == k then advance else failAt (some t) s!"expected `{k.show}`, found `{t.kind.show}`"
  | none => failHere s!"expected `{k.show}`"

def isKeyword (s : String) : Bool :=
  s == "fn" || s == "let" || s == "def" || s == "case" || s == "quote"

def startsAtom : Tk → Bool
  | .num _ => true
  | .str _ => true
  | .name s => s != "let" && s != "def"
  | .lparen | .lbrack | .tilde => true
  | _ => false

def parseBinder : P String := do
  match ← peekRaw with
  | some ⟨.name s, line, col, _⟩ =>
    if isKeyword s then throw (msgAt line col s!"`{s}` is a keyword and cannot be a name")
    else do advance; pure s
  | t => failAt t "expected a name"

/-- Names up to, not including, `stop`. -/
def parseNames : Nat → Tk → List String → P (List String)
  | 0, _, _ => failHere "the input is too large to read"
  | f + 1, stop, acc => do
    match ← peekRaw with
    | some t =>
      if t.kind == stop then pure acc.reverse
      else
        let x ← parseBinder
        parseNames f stop (x :: acc)
    | none => failHere s!"expected `{stop.show}`"

/-- After `[` in a pattern: names or `_` with commas between, then `]` or
    `, ...rest]`. -/
def parseArrayPattern : Nat → List String → P Pat
  | 0, _ => failHere "the input is too large to read"
  | f + 1, acc => do
    match ← peekRaw with
    | some ⟨.name _, _, _, _⟩ => do
      let x ← parseBinder
      match ← peekRaw with
      | some ⟨.rbrack, _, _, _⟩ => do advance; pure (.arr (x :: acc).reverse none)
      | some ⟨.comma, _, _, _⟩ => do
        advance
        match ← peekRaw with
        | some ⟨.dots, _, _, _⟩ => do
          advance
          let tl ← parseBinder
          match ← peekRaw with
          | some ⟨.rbrack, _, _, _⟩ => do advance; pure (.arr (x :: acc).reverse (some tl))
          | u => failAt u "`...rest` is the last part of an array pattern; expected `]`"
        | _ => parseArrayPattern f (x :: acc)
      | u => failAt u "expected `,` or `]` in an array pattern"
    | some t@⟨.dots, _, _, _⟩ =>
      failAt (some t) "`...rest` comes after at least one item, as in `[head, ...tail]`"
    | u =>
      failAt u "an item of an array pattern is a name or `_`: `[a, b]` or `[a, b, ...rest]`"

def parsePattern : P Pat := do
  match ← peekRaw with
  | some t =>
    match t.kind with
    | .num 0 => do advance; pure .zero
    | .num _ => failAt (some t) "a number pattern must be 0; use `m + 1` for the rest"
    | .name _ => do
      let x ← parseBinder
      match ← peekRaw with
      | some ⟨.plus, _, _, _⟩ =>
        advance
        match ← peekRaw with
        | some ⟨.num 1, _, _, _⟩ => do advance; pure (.succ x)
        | u => failAt u "a successor pattern is written `name + 1`"
      | _ => pure (.any x)
    | .lbrack => do
      advance
      -- Inside brackets layout is off; the header's limit returns after `]`.
      let g := (← get).guard
      setGuard .none
      match ← peekRaw with
      | some ⟨.rbrack, _, _, _⟩ => do advance; setGuard g; pure (.arr [] none)
      | _ => do
        let p ← parseArrayPattern ((← get).toks.size + 1) []
        setGuard g
        pure p
    | k => failAt (some t) s!"expected a pattern, found `{k.show}`"
  | none => failHere "expected a pattern"

def addArm (t : Tok) (p : Pat) (body : Expr) (acc : Arms) : P Arms :=
  match p with
  | .zero =>
    match acc.z with
    | none => pure { acc with z := some body }
    | some _ => failAt (some t) "duplicate arm for `0`"
  | .succ m =>
    match acc.sc with
    | none => pure { acc with sc := some (m, body) }
    | some _ => failAt (some t) "duplicate arm for `m + 1`"
  | .arr items rest =>
    let k := items.length
    if acc.arrs.any (fun (is, r, _) => is.length == k && r.isSome == rest.isSome) then
      failAt (some t) (
        if k == 0 then "duplicate arm for `[]`"
        else if k == 1 && rest.isSome then "duplicate arm for `[head, ...tail]`"
        else if rest.isSome then s!"duplicate arm for an array of {k} items or more"
        else s!"duplicate arm for an array of exactly {k} items")
    else if acc.arrs.any (fun (is, r, _) => r.isSome && is.length ≤ k) then
      failAt (some t)
        "this arm is never taken: an arm above it takes every array this one would"
    else pure { acc with arrs := acc.arrs.push (items, rest, body) }
  | .any x =>
    match acc.a with
    | none => pure { acc with a := some (x, body) }
    | some _ => failAt (some t) "duplicate catch-all arm"

def closer : Tk → Bool
  | .rparen | .rbrack | .comma => true
  | _ => false

mutual
  def parseExpr : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      let e ← parsePlus f l
      pipeLoop f l e

  def pipeLoop : Nat → Lim → Expr → P Expr
    | 0, _, _ => failHere "the input is too large to read"
    | f + 1, l, e => do
      match ← peek l with
      | some ⟨.pipe, _, _, _⟩ =>
        advance
        let r ← parsePlus f l
        pipeLoop f l (.app r e)
      | _ => pure e

  def parsePlus : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      let e ← parseApp f l
      plusLoop f l e

  def plusLoop : Nat → Lim → Expr → P Expr
    | 0, _, _ => failHere "the input is too large to read"
    | f + 1, l, e => do
      match ← peek l with
      | some t@⟨.plus, _, _, _⟩ =>
        advance
        match ← peek l with
        | some ⟨.num 1, _, _, _⟩ => do advance; plusLoop f l (.succ e)
        | _ => failAt (some t) "`+` only means the successor, written `e + 1`; the right side must be the number 1"
      | _ => pure e

  def parseApp : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      match ← peek l with
      | some t =>
        if startsAtom t.kind then
          let h ← parseAtom f l
          appLoop f l h
        else failAt (some t) s!"expected an expression, found `{t.kind.show}`"
      | none => failHere "expected an expression"

  def appLoop : Nat → Lim → Expr → P Expr
    | 0, _, _ => failHere "the input is too large to read"
    | f + 1, l, e => do
      match ← peek l with
      | some t =>
        if startsAtom t.kind then
          let a ← parseAtom f l
          appLoop f l (.app e a)
        else pure e
      | none => pure e

  def parseAtom : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      match ← peek l with
      | none => failHere "expected an expression"
      | some t =>
        let pos : Pos := (t.line, t.col)
        match t.kind with
        | .num n => do advance; pure (.num n)
        | .str cs => do advance; pure (cs.foldr (fun c e => .cons (.num c) e) .nil)
        | .name "fn" => do
          advance
          setGuard l
          let ps ← parseNames (f + 1) .arrow []
          if ps.isEmpty then failAt (some t) "`fn` needs at least one parameter"
          else
            expectTok .arrow
            setGuard .none
            let body ← parseBody f l
            pure (ps.foldr Expr.lam body)
        | .name "case" => do advance; parseCase f l
        | .name "quote" => do
          advance
          let e ← parseExpr f l
          pure (.quote pos e)
        | .name "_" => failAt (some t) "`_` is only a pattern, not a value"
        | .name s =>
          if s == "let" || s == "def" then
            failAt (some t) s!"`{s}` can only start a line of a block"
          else do advance; pure (.ref pos s)
        | .lparen => do
          advance
          let e ← parseExpr f .none
          expectTok .rparen
          pure e
        | .lbrack => do advance; parseArray f
        | .tilde => do
          advance
          let a ← parseAtom f l
          pure (.splice pos a)
        | k => failAt (some t) s!"unexpected `{k.show}`"

  /-- After `[`. -/
  def parseArray : Nat → P Expr
    | 0 => failHere "the input is too large to read"
    | f + 1 => do
      match ← peekRaw with
      | some ⟨.rbrack, _, _, _⟩ => do advance; pure .nil
      | _ =>
        let x ← parseExpr f .none
        arrayRest f x

  /-- After an item: the end, `, item` and more, or `, ...tail` and the end. -/
  def arrayRest : Nat → Expr → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, x => do
      match ← peekRaw with
      | some ⟨.rbrack, _, _, _⟩ => do advance; pure (.cons x .nil)
      | some ⟨.comma, _, _, _⟩ =>
        advance
        match ← peekRaw with
        | some ⟨.dots, _, _, _⟩ =>
          advance
          let tl ← parseExpr f .none
          expectTok .rbrack
          pure (.cons x tl)
        | _ =>
          let y ← parseExpr f .none
          let rest ← arrayRest f y
          pure (.cons x rest)
      | t => failAt t "expected `,` or `]`"

  /-- After `->` or `=`: the rest of the line, or a block on the lines below. -/
  def parseBody : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      match ← peekRaw with
      | none => failHere "expected a value"
      | some t =>
        if t.first then
          match ← peek l with
          | none => failAt (some t) "expected a value, indented under the line above"
          | some _ => parseBlock f t.col
        else parseExpr f l

  /-- Lines at column `c`: `let`s and `def`s, then one value. -/
  def parseBlock : Nat → Nat → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, c => do
      modify fun s => { s with exempt := s.pos }
      match ← peekRaw with
      | none => failHere "expected a value"
      | some t =>
        match t.kind with
        | .name "let" =>
          advance
          setGuard (.col c)
          let x ← parseBinder
          expectTok .eq
          setGuard .none
          let v ← parseBody f (.col c)
          let rest ← blockRest f c
          pure (.letE x v rest)
        | .name "def" =>
          advance
          setGuard (.col c)
          let x ← parseBinder
          let ps ← parseNames (f + 1) .eq []
          expectTok .eq
          setGuard .none
          let b ← parseBody f (.col c)
          let rest ← blockRest f c
          pure (.defE x ps b rest)
        | _ =>
          let e ← parseExpr f (.col c)
          match ← peekRaw with
          | some u =>
            if u.first && u.col == c then
              failAt (some u) s!"unexpected `{u.kind.show}`; only `let` and `def` lines come before the last line of a block"
            else pure e
          | none => pure e

  /-- What follows a `let` or `def`: another line of the block. -/
  def blockRest : Nat → Nat → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, c => do
      match ← peekRaw with
      | some u =>
        if u.first && u.col == c then parseBlock f c
        else if u.first && u.col < c then
          failAt (some u) "a block must end in a value, not a binding"
        else failAt (some u) s!"unexpected `{u.kind.show}`"
      | none => failHere "a block must end in a value, not a binding"

  /-- After `case`: the scrutinee, then arms on the lines below, one column. -/
  def parseCase : Nat → Lim → P Expr
    | 0, _ => failHere "the input is too large to read"
    | f + 1, l => do
      let s ← parseExpr f .line
      match ← peekRaw with
      | none => failHere "a `case` needs arms, one per line, indented under it"
      | some t =>
        if !t.first then failAt (some t) "the arms of a `case` start on the lines below it"
        else
          match ← peek l with
          | none => failAt (some t) "a `case` needs arms, one per line, indented under it"
          | some _ =>
            let arms ← parseArms f l t.col {}
            let z := arms.z.getD .missing
            let sc := arms.sc.getD ("_", .missing)
            let arrs := arms.arrs.foldr (fun (is, r, b) next => Expr.arm is r b next) .missing
            let a := arms.a.getD ("_", .missing)
            pure (.caseE s z sc.1 sc.2 arrs a.1 a.2)

  def parseArms : Nat → Lim → Nat → Arms → P Arms
    | 0, _, _, _ => failHere "the input is too large to read"
    | f + 1, l, a, acc => do
      let some t ← peekRaw | failHere "expected an arm"
      modify fun s => { s with exempt := s.pos, guard := .col a }
      let p ← parsePattern
      expectTok .arrow
      setGuard .none
      let body ← parseBody f (.col a)
      let acc ← addArm t p body acc
      match ← peekRaw with
      | some u =>
        if !u.first || closer u.kind then pure acc
        else if u.col == a then parseArms f l a acc
        else if l.stops u then pure acc
        else failAt (some u) "this line is not aligned with the arms above it"
      | none => pure acc
end

def parse (toks : Array Tok) (eofLine eofCol : Nat) : Except String Expr :=
  match toks[0]? with
  | none => .error (msgAt 1 0 "empty program: there is nothing to read")
  | some t0 =>
    let st : PS := { toks := toks, pos := 0, exempt := 0, eofLine := eofLine, eofCol := eofCol }
    match (do
        let e ← parseBlock (16 * (toks.size + 2)) t0.col
        match ← peekRaw with
        | none => pure e
        | some u => failAt (some u) s!"unexpected `{u.kind.show}`" : P Expr).run st with
    | .ok (e, _) => .ok e
    | .error m => .error m

/-! ### Names to indices -/

/-- A term with live splices. `term` is closed code that is not a splice;
    `hole` is code a splice puts in place. -/
inductive TT where
  | var : Nat → TT
  | lam : TT → TT
  | app : TT → TT → TT
  | lit : Data → TT
  | succ : TT → TT
  | cons : TT → TT → TT
  | dcase : TT → TT → TT → TT → TT → TT
  | term : Term → TT
  | hole : Term → TT

def TT.toTerm : TT → Term
  | .var i => .var i
  | .lam b => .lam b.toTerm
  | .app f a => .app f.toTerm a.toTerm
  | .lit d => .lit d
  | .succ t => .succ t.toTerm
  | .cons a b => .cons a.toTerm b.toTerm
  | .dcase s z sc n c => .dcase s.toTerm z.toTerm sc.toTerm n.toTerm c.toTerm
  | .term t => t
  | .hole t => t

def TT.ground : TT → Bool
  | .var _ => true
  | .lam b => b.ground
  | .app f a => f.ground && a.ground
  | .lit _ => true
  | .succ t => t.ground
  | .cons a b => a.ground && b.ground
  | .dcase s z sc n c => s.ground && z.ground && sc.ground && n.ground && c.ground
  | .term _ => true
  | .hole _ => false

/-- The data form of a node: its tag, then its parts, as one `cons` chain. -/
def nodeT (tag : Nat) (parts : List Term) : Term :=
  .cons (.lit (.nat tag)) (parts.foldr Term.cons (.lit (.arr [])))

/-- The code that builds the quoted program: a subterm with no splice is a
    literal of its `reify`; a node with a splice below it is built from its parts. -/
def TT.build (t : TT) : Term :=
  if t.ground then .lit (reify t.toTerm) else
  match t with
  | .var _ => .lit (reify t.toTerm)
  | .lam b => nodeT 1 [b.build]
  | .app f a => nodeT 0 [f.build, a.build]
  | .lit _ => .lit (reify t.toTerm)
  | .succ e => nodeT 3 [e.build]
  | .cons a b => nodeT 4 [a.build, b.build]
  | .dcase s z sc n c => nodeT 5 [s.build, z.build, sc.build, n.build, c.build]
  | .term _ => .lit (reify t.toTerm)
  | .hole h => h

/-- Rewrite the free variables of a term. `f d j` is what free variable `j`
    becomes where `d` binders of the term itself enclose it. -/
def mapFree (f : Nat → Nat → Term) : Nat → Term → Term
  | d, .var i => if i < d then .var i else f d (i - d)
  | d, .lam b => .lam (mapFree f (d + 1) b)
  | d, .app g a => .app (mapFree f d g) (mapFree f d a)
  | _, .lit x => .lit x
  | d, .succ t => .succ (mapFree f d t)
  | d, .cons a b => .cons (mapFree f d a) (mapFree f d b)
  | d, .dcase s z sc n c =>
    .dcase (mapFree f d s) (mapFree f d z) (mapFree f (d + 1) sc) (mapFree f d n)
      (mapFree f (d + 2) c)
  | d, .prim c x => .prim (mapFree f d c) (mapFree f d x)

/-- The term under `k` more binders. -/
def shift (k : Nat) (t : Term) : Term :=
  if k == 0 then t else mapFree (fun d j => .var (d + j + k)) 0 t

/-- The free variables of a term, each as often as it occurs. -/
def frees : Nat → Term → List Nat → List Nat
  | d, .var i, acc => if i < d then acc else (i - d) :: acc
  | d, .lam b, acc => frees (d + 1) b acc
  | d, .app g a, acc => frees d g (frees d a acc)
  | _, .lit _, acc => acc
  | d, .succ t, acc => frees d t acc
  | d, .cons a b, acc => frees d a (frees d b acc)
  | d, .dcase s z sc n c, acc =>
    frees d s (frees d z (frees (d + 1) sc (frees d n (frees (d + 2) c acc))))
  | d, .prim c x, acc => frees d c (frees d x acc)

def lamsT : Nat → Term → Term
  | 0, t => t
  | k + 1, t => .lam (lamsT k t)

/-! ### Array arms

The array arms of a `case` are tried in the order written, and which is taken
depends only on how many items the array has. `arrayNode` reads the array one
item at a time until that is settled. Where it has read `d` items, `2 * d`
binders enclose the code: item `i` (from 1) is variable `2 * (d - i) + 1` and
the array after item `i` is variable `2 * (d - i)`. -/

/-- An array arm: how many items it names, whether it ends in `...rest`, and
    its body, read where the rest (if any) is the nearest name, then the items
    from the last to the first. -/
structure ArmT where
  k : Nat
  rest : Bool
  body : TT

def ArmT.takes (a : ArmT) (len : Nat) : Bool :=
  if a.rest then a.k ≤ len else a.k == len

/-- An arm's body where `d` items have been read. -/
def armLeaf (a : ArmT) (d : Nat) : Term :=
  let k := a.k
  mapFree (fun depth j =>
    if a.rest then
      if j == 0 then .var (depth + 2 * (d - k))
      else if j ≤ k then .var (depth + 2 * (d - (k + 1 - j)) + 1)
      else .var (depth + (j - (k + 1)) + 2 * d)
    else
      if j < k then .var (depth + 2 * (d - (k - j)) + 1)
      else .var (depth + (j - k) + 2 * d)) 0 a.body.toTerm

/-- The code where `d` items have been read and the array after them is
    variable 0. `none d` is what to do, under `d` binders, when no arm takes
    the array. -/
def arrayNode (arms : List ArmT) (none : Nat → Term) : Nat → Nat → Term
  | 0, d => none (2 * d)
  | fuel + 1, d =>
    match arms.find? (fun a => a.rest || a.k ≥ d) with
    | .none => none (2 * d)
    | some a =>
      if a.rest && a.k ≤ d then armLeaf a d
      else
        .dcase (.var 0) wrongTerm wrongTerm
          (match arms.find? (·.takes d) with
           | some w => armLeaf w d
           | .none => none (2 * d))
          (arrayNode arms none fuel (d + 1))

/-! ### Runs of definitions

A run is the `def`s of a block with no `let` between them. Each body is read
once, in a fixed layout, and `assemble` then puts the definitions in an order
in which each comes after the ones it uses, binding those that use one another
in a ring as one recursive function.

The layout of the free variables of definition `i` of `k`, where `n` names are
in scope around the run: `0` is the definition itself, `1` to `i` the earlier
ones, nearest first, the next `n` the names in scope, then the later
definitions in order, then whatever lies beyond the scope. The rest of the
block has the layout of the last definition, `0` being that definition. -/

inductive Ref where
  | member (m : Nat)
  | outer (v : Nat)

def decode (n k i j : Nat) : Ref :=
  if j ≤ i then .member (i - j)
  else if j < i + 1 + n then .outer (j - i - 1)
  else if j < n + k then .member (j - n)
  else .outer (j - k)

/-- Free variable `j` of definition `i`, where `st` lists the binders emitted
    so far for this run, nearest first (`none` is a ring's function), and
    `extra` more binders lie between them and the body. Inside the ring `ring`,
    member `q` is `self q`, and `self` is the outermost of the extra binders. -/
def place (n k i : Nat) (st : List (Option Nat)) (ring : List Nat) (extra : Nat)
    (d j : Nat) : Term :=
  match decode n k i j with
  | .member m =>
    let q := ring.idxOf m
    if q < ring.length then .app (.var (d + extra - 1)) (.lit (.nat q))
    else .var (d + extra + st.idxOf (some m))
  | .outer v => .var (d + extra + st.length + v)

/-- The members a ring's function chooses between: member `q` is under `q`
    binders, one for each number counted down. -/
def selChain : List Term → Term
  | [] => wrongTerm
  | [b] => b
  | b :: more => .dcase (.var 0) b (selChain more) wrongTerm wrongTerm

def bindMembers (cont : List (Option Nat) → Term) :
    List Nat → Nat → List (Option Nat) → Term
  | [], _, st => cont st
  | i :: more, q, st =>
    .app (.lam (bindMembers cont more (q + 1) (some i :: st)))
      (.app (.var q) (.lit (.nat q)))

/-- `uses[i]` is the definitions that definition `i` mentions. A definition by
    itself is bound as it always was: a function, under `recurT` when it
    mentions itself. A ring of `r` definitions is one function of a number
    under `recurT`; member `q` is that function applied to `q`, and each is
    then bound to its name for what follows. -/
def emit (n k : Nat) (defs : Array Term) (uses : Array (List Nat)) (rest : Term) :
    List (List Nat) → List (Option Nat) → Term
  | [], st => mapFree (place n k (k - 1) st [] 0) 0 rest
  | [i] :: groups, st =>
    let body := defs.getD i wrongTerm
    let value :=
      if (uses.getD i []).contains i then
        Term.app recurT (.lam (mapFree (place n k i (some i :: st) [] 0) 0 body))
      else mapFree (place n k i st [] 0) 0 body
    .app (.lam (emit n k defs uses rest groups (some i :: st))) value
  | ring :: groups, st =>
    let bodies := ring.zipIdx.map fun (i, q) =>
      mapFree (place n k i st ring (q + 2)) 0 (defs.getD i wrongTerm)
    .app (.lam (bindMembers (fun st' => emit n k defs uses rest groups st') ring 0 (none :: st)))
      (.app recurT (.lam (.lam (selChain bodies))))

/-- Everything a definition reaches through one use or more. -/
def reach (uses : Array (List Nat)) (i : Nat) : List Nat :=
  (List.range uses.size).foldl
    (fun seen _ => seen.foldl
      (fun acc x => (uses.getD x []).foldl
        (fun acc y => if acc.contains y then acc else acc ++ [y]) acc) seen)
    (uses.getD i [])

/-- The run as one term. Definitions that reach one another are one group. The
    groups are emitted so that each follows what it uses, the earliest written
    first where there is a choice; a run in which no definition mentions a
    later one keeps the order it was written in. -/
def assemble (n : Nat) (defs : Array Term) (rest : Term) : Term :=
  let k := defs.size
  let uses : Array (List Nat) := (Array.range k).map fun i =>
    ((frees 0 (defs.getD i wrongTerm) []).filterMap fun j =>
      match decode n k i j with
      | .member m => some m
      | .outer _ => none).eraseDups
  let reaches := (Array.range k).map (reach uses)
  let group (i : Nat) : List Nat := (List.range k).filter fun j =>
    j == i || ((reaches.getD i []).contains j && (reaches.getD j []).contains i)
  let order := ((List.range k).foldl
    (fun (acc : List Nat × List (List Nat)) _ =>
      match (List.range k).find? (fun i => !acc.1.contains i &&
          (group i).all fun m => (uses.getD m []).all fun y =>
            acc.1.contains y || (group i).contains y) with
      | some i => (acc.1 ++ group i, acc.2 ++ [group i])
      | none => acc)
    ([], [])).2
  emit n k defs uses rest order []

/-- The names of the `def`s a run goes on with. -/
def runNames : Expr → List String
  | .defE f _ _ r => f :: runNames r
  | _ => []

/-- `ctx` is the names in scope, nearest first. Inside a quotation `ctx` holds
    only the names bound inside it, and `outer` the names bound outside it.
    `later` is the names of the definitions still to come in the runs being
    read, nearest first: a name found nowhere else is looked for there, and
    reads as a variable past the end of `ctx`, which `assemble` resolves.
    `held` is the `later` of the code around a quotation, for its splices. -/
structure Scope where
  ctx : List String
  outer : Option (List String)
  later : List String := []
  held : List String := []

def Scope.push (sc : Scope) (x : String) : Scope := { sc with ctx := x :: sc.ctx }

/-- `op n x`: operation number `n` on the argument `x`. -/
def opTerm : Term := .lam (.lam (.prim (.var 1) (.var 0)))

/-- A named operation of two operands, as a function of two arguments. -/
def binaryOp (n : Nat) : Term :=
  .lam (.lam (.prim (.lit (.nat n)) (.cons (.var 1) (.cons (.var 0) (.lit (.arr []))))))

def lookup (sc : Scope) (p : Pos) (x : String) : Except String TT :=
  let i := sc.ctx.idxOf x
  if i < sc.ctx.length then .ok (.var i)
  else if sc.outer.any (·.contains x) then
    .error (fmtPos p s!"the quotation mentions `{x}`, which is bound outside it")
  else if x == "interpret" then .ok (.term interp)
  else if x == "op" then .ok (.term opTerm)
  else if x == "ask" then .ok (.term askTerm)
  else match arithNames.lookup x with
    | some n => .ok (.term (binaryOp n))
    | none =>
      let j := sc.later.idxOf x
      if j < sc.later.length then .ok (.var (sc.ctx.length + j))
      else if sc.held.contains x then
        .error (fmtPos p s!"the quotation mentions `{x}`, which is defined outside it")
      else .error (fmtPos p s!"unbound name `{x}`")

mutual
  def tr : Scope → Expr → Except String TT
    | _, .num n => .ok (.lit (.nat n))
    | _, .nil => .ok (.lit (.arr []))
    | sc, .ref p x => lookup sc p x
    | sc, .lam x b => do
      let b' ← tr (sc.push x) b
      pure (.lam b')
    | sc, .app f a => do
      let f' ← tr sc f
      let a' ← tr sc a
      pure (.app f' a')
    | sc, .cons a b => do
      let a' ← tr sc a
      let b' ← tr sc b
      pure (.cons a' b')
    | sc, .succ e => do
      let e' ← tr sc e
      pure (.succ e')
    | sc, .letE x v r => do
      let v' ← tr sc v
      let r' ← tr (sc.push x) r
      pure (.app (.lam r') v')
    | sc, .defE f ps b r => do
      -- The first definition of a run; `trRun` reads the ones after it.
      let b' ← tr { sc with ctx := ps.reverse ++ f :: sc.ctx,
                            later := runNames r ++ sc.later } b
      let (defs, rest) ← trRun sc [f] r
      pure (.term (assemble sc.ctx.length (lamsT ps.length b'.toTerm :: defs).toArray rest))
    | sc, .caseE s z m sn arrs a any => do
      let s' ← tr sc s
      let caught := !any.isMissing
      -- With a catch-all, the scrutinee is bound once. Only the catch-all body may
      -- name it; the written arms see that slot under a name no program can write.
      let hidden := "\x00scrutinee"
      let base := if caught then sc.push hidden else sc
      -- What an arm that is not written reads as, under `d` binders.
      let anyT ← if caught then (do let t ← tr (sc.push a) any; pure t.toTerm)
        else pure wrongTerm
      let fill (d : Nat) : Term := if caught then shift d anyT else wrongTerm
      let z' ← if z.isMissing then pure (.term (fill 0)) else tr base z
      let sn' ← if sn.isMissing then pure (.term (fill 1)) else tr (base.push m) sn
      let arms ← trArms base arrs
      let n' : TT := match arms.find? (·.takes 0) with
        | some w => w.body
        | none => .term (fill 0)
      let deepest := arms.foldl (fun k a => max k a.k) 0
      let c' : TT := .term (arrayNode arms fill (deepest + 2) 1)
      if caught then pure (.app (.lam (.dcase (.var 0) z' sn' n' c')) s')
      else pure (.dcase s' z' sn' n' c')
    | sc, .quote p e =>
      if sc.outer.isSome then
        .error (fmtPos p "a quotation inside a quotation is not supported")
      else do
        let tt ← tr { ctx := [], outer := some sc.ctx, held := sc.later } e
        pure (.term tt.build)
    | sc, .splice p e =>
      match sc.outer with
      | none => .error (fmtPos p "a splice `~` must be inside a quotation")
      | some o =>
        if sc.ctx.isEmpty then do
          let tt ← tr { ctx := o, outer := none, later := sc.held } e
          pure (.hole tt.toTerm)
        else .error (fmtPos p "a splice `~` cannot be under a binder of its quotation")
    | _, .arm _ _ _ _ => .ok (.term wrongTerm)
    | _, .missing => .ok (.term wrongTerm)
  termination_by _ e => (sizeOf e, 0)

  /-- The rest of a run, where `earlier` is its definitions already read,
      nearest first: the definitions still to come, each in the layout
      `assemble` takes, and then the rest of the block. -/
  def trRun (sc : Scope) (earlier : List String) : Expr → Except String (List Term × Term)
    | .defE f ps b r => do
      let b' ← tr { sc with ctx := ps.reverse ++ f :: earlier ++ sc.ctx,
                            later := runNames r ++ sc.later } b
      let (defs, rest) ← trRun sc (f :: earlier) r
      pure (lamsT ps.length b'.toTerm :: defs, rest)
    | e => do
      let t ← tr { sc with ctx := earlier ++ sc.ctx } e
      pure ([], t.toTerm)
  termination_by e => (sizeOf e, 1)

  /-- The array arms of a `case`, each body read where its names are bound. -/
  def trArms (base : Scope) : Expr → Except String (List ArmT)
    | .arm items rest body next => do
      let b ← tr { base with ctx := rest.toList ++ items.reverse ++ base.ctx } body
      let more ← trArms base next
      pure ({ k := items.length, rest := rest.isSome, body := b } :: more)
    | _ => pure []
  termination_by e => (sizeOf e, 0)
end

end Surface.Read

namespace Surface
open Reflect

/-- Program text to a term, or a message with line and column. -/
def read (src : ByteArray) : Except String Term := do
  let (toks, line, col) ← Read.lex src
  let e ← Read.parse toks line col
  let tt ← Read.tr { ctx := [], outer := none } e
  pure tt.toTerm

def readString (s : String) : Except String Term := read s.toUTF8

end Surface
