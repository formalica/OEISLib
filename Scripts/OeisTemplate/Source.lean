module
import SQLite
public import SQLite.LowLevel
import Scripts.OeisIngest.Db
import Scripts.OeisIngest.Json
import Scripts.OeisIngest.Parse
/-!
Everything a template may know about one sequence, loaded from `Metadata/oeis.db`.

Templates never see `oeisdata/`. Each *section* of a sequence has one canonical text, and
`formalization_item.original_text` must be a substring of exactly that text:

| `language`        | section text                                  |
| ----------------- | --------------------------------------------- |
| `maindef`         | the `%N` title                                |
| `formula`         | the `%F` lines joined with `\n`               |
| `comment`         | the `%C` lines joined with `\n`               |
| anything else     | `program.text` of block `(language, block)`   |
-/

namespace Oeis.Template

open SQLite

public section

/-- One row of the `program` table. -/
structure ProgramBlock where
  language : String
  blockIndex : Nat
  text : String
  /-- `program.hash`, stored as `formalization_item.source_hash`. -/
  hash : String

structure SeqSource where
  name : String
  title : String
  offset : Int
  /-- Published terms as written in the database (decimal numerals). -/
  terms : Array String
  formulaLines : Array String
  commentLines : Array String
  programs : Array ProgramBlock

namespace Section
def maindef : String := "maindef"
def formula : String := "formula"
def comment : String := "comment"
end Section

namespace SeqSource

def formulaText (s : SeqSource) : String := "\n".intercalate s.formulaLines.toList
def commentText (s : SeqSource) : String := "\n".intercalate s.commentLines.toList

/-- Program blocks of one language, in block order. -/
def blocksOf (s : SeqSource) (language : String) : Array ProgramBlock :=
  s.programs.filter (·.language == language)

/-- The text a candidate of section `language` / `blockIndex` has to be quoted from. -/
def sectionText? (s : SeqSource) (language : String) (blockIndex : Nat) : Option String :=
  if language == Section.maindef then some s.title
  else if language == Section.formula then some s.formulaText
  else if language == Section.comment then some s.commentText
  else (s.programs.find? fun p => p.language == language && p.blockIndex == blockIndex).map (·.text)

/-- `program.hash` for program sections, the hash of the section text otherwise. -/
def sectionHash? (s : SeqSource) (language : String) (blockIndex : Nat) : Option String :=
  match s.programs.find? (fun p => p.language == language && p.blockIndex == blockIndex) with
  | some p => some p.hash
  | none => (s.sectionText? language blockIndex).map formulaHash

end SeqSource

private def lines (json : String) : IO (Array String) :=
  match Json.parseArray json with
  | some xs => pure xs
  | none => throw <| IO.userError s!"malformed JSON array in the database: {json.take 60}"

/-- Loads one sequence, or `none` if it is not in the database. -/
def loadSource (db : SQLite) (name : String) : IO (Option SeqSource) := do
  let stmt ← db.prepare
    "SELECT title, \"offset\", data, formula_lines, comment_lines FROM sequence WHERE name = ?1"
  stmt.bindText 1 name
  unless ← stmt.step do return none
  let title ← stmt.columnText 0
  let offset := (← stmt.columnInt64 1).toInt
  let terms ← lines (← stmt.columnText 2)
  let formulaLines ← lines (← stmt.columnText 3)
  let commentLines ← lines (← stmt.columnText 4)
  let progStmt ← db.prepare
    "SELECT language, block_index, text, hash FROM program
       WHERE oeis_name = ?1 ORDER BY language, block_index"
  progStmt.bindText 1 name
  let mut programs := #[]
  while ← progStmt.step do
    programs := programs.push {
      language := ← progStmt.columnText 0
      blockIndex := (← progStmt.columnInt64 1).toNatClampNeg
      text := ← progStmt.columnText 2
      hash := ← progStmt.columnText 3 }
  return some { name, title, offset, terms, formulaLines, commentLines, programs }

end
end Oeis.Template
