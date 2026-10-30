module
/-!
Minimal JSON serialization helpers.

The ingest script only ever emits JSON *arrays of strings* (or of integer
numerals), so a full JSON library is not needed here.
-/

namespace Oeis.Json
public section

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

private def toHexAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => toHexAux fuel (n / 16) (hexDigit (n % 16) :: acc)

/-- Renders `n` in lowercase hex, left-padded with `0` to at least `width` digits. -/
public def toHex (n : Nat) (width : Nat := 0) : String :=
  let s := if n == 0 then "0" else String.ofList (toHexAux 128 n [])
  if s.length ≥ width then s else String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Escapes a Lean string into the body of a JSON string literal. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c => if c.toNat < 0x20 then acc ++ "\\u" ++ toHex c.toNat 4 else acc.push c

/-- A JSON string literal, quotes included. -/
public def str (s : String) : String :=
  "\"" ++ escape s ++ "\""

/-- A JSON array of string literals. -/
public def strArray (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map str) ++ "]"

private def isIntegerLiteral (s : String) : Bool :=
  let body := if s.startsWith "-" then s.drop 1 else s
  !body.isEmpty && body.all Char.isDigit

/--
A JSON array of OEIS terms. Terms are emitted as bare (arbitrary precision)
numerals; anything that does not look like an integer is quoted instead so the
output stays valid JSON.
-/
public def termArray (xs : Array String) : String :=
  "[" ++ String.intercalate "," (xs.toList.map fun x =>
    if isIntegerLiteral x then x else str x) ++ "]"

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decodes the string literal whose opening quote is at `cs[i]`; returns the text and the
index just past the closing quote. Inverse of `escape`. -/
private partial def decodeStr (cs : Array Char) (j : Nat) (acc : String) :
    Option (String × Nat) :=
  match cs[j]? with
  | none => none
  | some '"' => some (acc, j + 1)
  | some '\\' =>
    match cs[j + 1]? with
    | some '"' => decodeStr cs (j + 2) (acc.push '"')
    | some '\\' => decodeStr cs (j + 2) (acc.push '\\')
    | some '/' => decodeStr cs (j + 2) (acc.push '/')
    | some 'n' => decodeStr cs (j + 2) (acc.push '\n')
    | some 'r' => decodeStr cs (j + 2) (acc.push '\r')
    | some 't' => decodeStr cs (j + 2) (acc.push '\t')
    | some 'u' =>
      match cs[j + 2]?.bind hexVal, cs[j + 3]?.bind hexVal,
            cs[j + 4]?.bind hexVal, cs[j + 5]?.bind hexVal with
      | some a, some b, some c, some d =>
        decodeStr cs (j + 6) (acc.push (Char.ofNat (((a * 16 + b) * 16 + c) * 16 + d)))
      | _, _, _, _ => none
    | _ => none
  | some c => decodeStr cs (j + 1) (acc.push c)

private partial def skipSpace (cs : Array Char) (i : Nat) : Nat :=
  if (cs[i]?).any Char.isWhitespace then skipSpace cs (i + 1) else i

private partial def bareToken (cs : Array Char) (i : Nat) (acc : String) : String × Nat :=
  match cs[i]? with
  | some c => if c == ',' || c == ']' then (acc, i) else bareToken cs (i + 1) (acc.push c)
  | none => (acc, i)

private partial def arrayItems (cs : Array Char) (i : Nat) (acc : Array String) :
    Option (Array String) :=
  let i := skipSpace cs i
  match cs[i]? with
  | some ']' => some acc
  | some '"' =>
    match decodeStr cs (i + 1) "" with
    | none => none
    | some (s, j) => afterItem cs j (acc.push s)
  | some _ =>
    let (tok, j) := bareToken cs i ""
    afterItem cs j (acc.push tok.trimAscii.toString)
  | none => none
where
  afterItem (cs : Array Char) (j : Nat) (acc : Array String) : Option (Array String) :=
    let j := skipSpace cs j
    match cs[j]? with
    | some ',' => arrayItems cs (j + 1) acc
    | some ']' => some acc
    | _ => none

/-- Parses a JSON array written by `strArray` / `termArray`: quoted items are decoded, bare
numerals are returned as written. -/
public def parseArray (s : String) : Option (Array String) :=
  let cs := s.toList.toArray
  let i := skipSpace cs 0
  if cs[i]? == some '[' then arrayItems cs (i + 1) #[] else none

end
end Oeis.Json
