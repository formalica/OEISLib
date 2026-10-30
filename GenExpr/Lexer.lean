module
public import GenExpr.Types
public meta import GenExpr.Types

/-!
Tokenizer for the raw syntax.

Two properties are load-bearing downstream and must not be "simplified" away:

* every token records whether whitespace preceded it (`spaceBefore`) — the juxtaposition rules
  (`2n` is a product, `2 for` is not) are whitespace sensitive;
* anything the tokenizer does not recognise, including every non-ASCII character, becomes a
  `junk` token rather than being dropped, because junk is what stops an expression from
  swallowing the prose around it.
-/

namespace GenExpr
public section

/-- The input string together with the char/byte index tables needed for exact spans. -/
structure Input where
  text : String
  chars : Array Char
  /-- `bytes[i]` is the byte offset of char `i`; the array has `chars.size + 1` entries. -/
  bytes : Array Nat
deriving Inhabited

namespace Input

def ofString (s : String) : Input :=
  let cs := s.toList.toArray
  let bs := cs.foldl (init := #[0]) fun acc c => acc.push (acc.back! + c.utf8Size)
  { text := s, chars := cs, bytes := bs }

def size (inp : Input) : Nat := inp.chars.size

def get! (inp : Input) (i : Nat) : Char := inp.chars[i]!

def get? (inp : Input) (i : Nat) : Option Char := inp.chars[i]?

/-- Byte span of the char range `[i, j)`. -/
def span (inp : Input) (i j : Nat) : Span := ⟨inp.bytes[i]!, inp.bytes[j]!⟩

/-- Source text of the char range `[i, j)`. -/
def extract (inp : Input) (i j : Nat) : String :=
  String.ofList (inp.chars.extract i j).toList

end Input

/-- Lexical class of a token. Operator spelling lives in `Token.text`. -/
inductive TokKind where
  /-- `123` -/
  | num
  /-- `1.25` -/
  | dec
  /-- `abc`, `A000045`, `Sum`, `mod` -/
  | ident
  | op
  | lparen | rparen
  | lbrace | rbrace
  | lbrack | rbrack
  | comma
  | semi
  /-- Anything unrecognised, including all non-ASCII. Always terminates an expression. -/
  | junk
deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace TokKind

def name : TokKind → String
  | .num => "num" | .dec => "dec" | .ident => "ident"
  | .op => "op"
  | .lparen => "(" | .rparen => ")" | .lbrace => "{" | .rbrace => "}"
  | .lbrack => "[" | .rbrack => "]"
  | .comma => "," | .semi => ";" | .junk => "junk"

instance : ToString TokKind := ⟨name⟩

end TokKind

structure Token where
  kind : TokKind
  text : String
  /-- Char index of the first character. -/
  start : Nat
  /-- Char index one past the last character. -/
  stop : Nat
  spaceBefore : Bool
deriving Inhabited, Repr

namespace Token

def isOp (t : Token) (s : String) : Bool := t.kind == .op && t.text == s

def isIdent (t : Token) (s : String) : Bool := t.kind == .ident && t.text == s

def isJunk (t : Token) : Bool := t.kind == .junk

/-- Tokens no expression may span: junk and the top-level separators. -/
def isHardSep (t : Token) : Bool :=
  t.kind == .junk || t.kind == .comma || t.kind == .semi

instance : ToString Token where
  toString t := s!"{t.kind}:{t.text}"

end Token

namespace Lexer

private def twoCharOps : List String :=
  ["<=", ">=", "!=", "<>", "==", "**", ".."]

private def singleCharOps : List Char :=
  ['+', '-', '*', '/', '^', '%', '=', '<', '>', '!', '|', '_']

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- A junk run stops as soon as a character that could start a real token appears. -/
private def startsToken (c : Char) : Bool :=
  isSpace c || c.isAlphanum || singleCharOps.contains c ||
    ['(', ')', '{', '}', '[', ']', ',', ';', '.'].contains c

/-- Scans `chars` forward from `i` while `p` holds. -/
private def scanWhile (inp : Input) (i : Nat) (p : Char → Bool) : Nat := Id.run do
  let n := inp.size
  let mut j := i
  for _ in [0:n - i] do
    match inp.get? j with
    | some c => if p c then j := j + 1 else break
    | none => break
  return j

def tokenize (inp : Input) : Array Token := Id.run do
  let n := inp.size
  let mut out : Array Token := #[]
  let mut i := 0
  let mut space := false
  -- Every branch advances `i` by at least one, so `n + 1` iterations always suffice.
  for _ in [0:n + 1] do
    if i ≥ n then break
    let c := inp.get! i
    if isSpace c then
      space := true
      i := i + 1
      continue
    let mut stop := i + 1
    let mut kind := TokKind.junk
    if c.isDigit then
      let d := scanWhile inp i Char.isDigit
      if inp.get? d == some '.' && (inp.get? (d + 1)).any Char.isDigit then
        stop := scanWhile inp (d + 1) Char.isDigit
        kind := .dec
      else
        -- `3n` stays two tokens; the parser reads the adjacency as multiplication, or as the
        -- single name `2F1` when the catalogue knows it.
        stop := d
        kind := .num
    else if c.isAlpha then
      stop := scanWhile inp i Char.isAlphanum
      kind := .ident
    else
      let two := inp.extract i (min n (i + 2))
      if twoCharOps.contains two then
        stop := i + 2
        kind := .op
      else if singleCharOps.contains c then
        kind := .op
      else
        match c with
        | '(' => kind := .lparen
        | ')' => kind := .rparen
        | '{' => kind := .lbrace
        | '}' => kind := .rbrace
        | '[' => kind := .lbrack
        | ']' => kind := .rbrack
        | ',' => kind := .comma
        | ';' => kind := .semi
        | _ =>
          kind := .junk
          stop := max (i + 1) (scanWhile inp i (fun ch => !startsToken ch))
    out := out.push
      { kind, text := inp.extract i stop, start := i, stop, spaceBefore := space }
    space := false
    i := stop
  return out

/-- Convenience wrapper used throughout the tests. -/
def run (s : String) : Input × Array Token :=
  let inp := Input.ofString s
  (inp, tokenize inp)

end Lexer

end
end GenExpr
