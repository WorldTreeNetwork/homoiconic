import Reflect.Request
import Reflect.Interpreter
import Reflect.Arith

/-!
The reader: program text to a `Reflect.Term`, or an error message with line and
column. Hand-written and total; recursion is bounded by fuel proportional to
the number of tokens, never by `partial`. The reader is tested against
`Surface.reads` and `Surface.refused`; it is not proved.

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
  | name (s : String)
  | lparen | rparen | lbrack | rbrack
  | comma | dots | arrow | eq | plus | pipe | tilde
  deriving BEq

def Tk.show : Tk → String
  | .num n => toString n
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
  /-- Scrutinee; zero arm; successor name and arm; empty arm; head name, tail
      name and non-empty arm; catch-all name and arm. An absent arm is `missing`. -/
  | caseE : Expr → Expr → String → Expr → Expr → String → String → Expr → String →
      Expr → Expr
  | quote : Pos → Expr → Expr
  | splice : Pos → Expr → Expr
  | missing : Expr

def Expr.isMissing : Expr → Bool
  | .missing => true
  | _ => false

inductive Pat where
  | zero | succ (m : String) | nil | cons (h t : String) | any (x : String)

structure Arms where
  z : Option Expr := none
  sc : Option (String × Expr) := none
  n : Option Expr := none
  c : Option (String × String × Expr) := none
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
      | some ⟨.rbrack, _, _, _⟩ => do advance; setGuard g; pure .nil
      | some ⟨.name _, _, _, _⟩ =>
        let h ← parseBinder
        expectTok .comma
        expectTok .dots
        let tl ← parseBinder
        expectTok .rbrack
        setGuard g
        pure (.cons h tl)
      | u => failAt u "patterns are one level deep: `[]` or `[head, ...tail]`"
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
  | .nil =>
    match acc.n with
    | none => pure { acc with n := some body }
    | some _ => failAt (some t) "duplicate arm for `[]`"
  | .cons h tl =>
    match acc.c with
    | none => pure { acc with c := some (h, tl, body) }
    | some _ => failAt (some t) "duplicate arm for `[head, ...tail]`"
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
            let n := arms.n.getD .missing
            let c := arms.c.getD ("_", "_", .missing)
            let a := arms.a.getD ("_", .missing)
            pure (.caseE s z sc.1 sc.2 n c.1 c.2.1 c.2.2 a.1 a.2)

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

def TT.lams : Nat → TT → TT
  | 0, t => t
  | k + 1, t => .lam (TT.lams k t)

/-- Does the term mention de Bruijn index `k` (counted under binders)? -/
def uses (k : Nat) : Term → Bool
  | .var i => i == k
  | .lam b => uses (k + 1) b
  | .app f a => uses k f || uses k a
  | .lit _ => false
  | .succ t => uses k t
  | .cons a b => uses k a || uses k b
  | .dcase s z sc n c =>
    uses k s || uses k z || uses (k + 1) sc || uses k n || uses (k + 2) c
  | .prim c x => uses k c || uses k x

/-- `ctx` is the names in scope, nearest first. Inside a quotation `ctx` holds
    only the names bound inside it, and `outer` the names bound outside it. -/
structure Scope where
  ctx : List String
  outer : Option (List String)

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
    | none => .error (fmtPos p s!"unbound name `{x}`")

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
    let n := ps.length
    let b1 ← tr { sc with ctx := ps.reverse ++ f :: sc.ctx } b
    let value ←
      if uses n b1.toTerm then pure (TT.app (.term recurT) (.lam (TT.lams n b1)))
      else do
        let b2 ← tr { sc with ctx := ps.reverse ++ sc.ctx } b
        pure (TT.lams n b2)
    let r' ← tr (sc.push f) r
    pure (.app (.lam r') value)
  | sc, .caseE s z m sn n h t c a any => do
    let s' ← tr sc s
    let caught := !any.isMissing
    -- With a catch-all, the scrutinee is bound once. Only the catch-all body may
    -- name it; the written arms see that slot under a name no program can write.
    let hidden := "\x00scrutinee"
    let base := if caught then sc.push hidden else sc
    let fill := sc.push a
    let wrong : TT := .term wrongTerm
    let z' ← if z.isMissing then (if caught then tr fill any else pure wrong) else tr base z
    let sn' ← if sn.isMissing then (if caught then tr (fill.push hidden) any else pure wrong)
      else tr (base.push m) sn
    let n' ← if n.isMissing then (if caught then tr fill any else pure wrong) else tr base n
    let c' ← if c.isMissing then
        (if caught then tr ((fill.push hidden).push hidden) any else pure wrong)
      else tr ((base.push h).push t) c
    if caught then pure (.app (.lam (.dcase (.var 0) z' sn' n' c')) s')
    else pure (.dcase s' z' sn' n' c')
  | sc, .quote p e =>
    if sc.outer.isSome then
      .error (fmtPos p "a quotation inside a quotation is not supported")
    else do
      let tt ← tr { ctx := [], outer := some sc.ctx } e
      pure (.term tt.build)
  | sc, .splice p e =>
    match sc.outer with
    | none => .error (fmtPos p "a splice `~` must be inside a quotation")
    | some o =>
      if sc.ctx.isEmpty then do
        let tt ← tr { ctx := o, outer := none } e
        pure (.hole tt.toTerm)
      else .error (fmtPos p "a splice `~` cannot be under a binder of its quotation")
  | _, .missing => .ok (.term wrongTerm)

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
