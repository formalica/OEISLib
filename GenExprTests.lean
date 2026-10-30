module
/-!
Test harness for GenExpr.

`Assert` collects failures instead of aborting so that one run reports every broken case.
Pure test modules also use `#guard`, which turns a regression into a build error.
-/

namespace GenExprTests
public section

/-- One failed expectation. -/
structure Failure where
  test : String
  detail : String
deriving Inhabited

abbrev Result := Array Failure

/-- `check name expected actual` records a failure when the two differ. -/
def check [BEq α] [ToString α] (name : String) (expected actual : α) : Result :=
  if expected == actual then #[]
  else #[{ test := name, detail := s!"expected: {expected}\n  actual:   {actual}" }]

def checkTrue (name : String) (b : Bool) (detail : String := "") : Result :=
  if b then #[] else #[{ test := name, detail }]

/-- Prints every failure and returns the exit code for the whole suite. -/
def report (suite : String) (rs : Array Result) : IO UInt32 := do
  let failures := rs.flatten
  if failures.isEmpty then
    IO.println s!"ok  {suite} ({rs.size} checks)"
    return 0
  for f in failures do
    IO.eprintln s!"FAIL {suite} / {f.test}\n  {f.detail}"
  IO.eprintln s!"{failures.size} failure(s) in {suite}"
  return 1

end
end GenExprTests
