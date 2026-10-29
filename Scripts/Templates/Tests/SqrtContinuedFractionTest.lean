import Scripts.Templates.SqrtContinuedFraction

/-! Recognizer and value regressions for the `sqrtContinuedFraction` template; the Mathlib bridge
itself is proved in `OEISLib.Common.SqrtContinuedFraction`. -/

set_option linter.hashCommand false

namespace Oeis.Template.SqrtContinuedFraction.Tests

#guard parseTitle "Numerators of continued fraction convergents to sqrt(6)." == some 6
#guard parseTitle "Numerators of continued fraction convergents to sqrt(9)." == none
#guard parseTitle "Numerators of continued fraction convergents to sqrt(6). Extra" == none

/-- Every shape rebuilt from its parameters is recognized with the same parameters, and the
recognized prefix stops before a trailing comment. -/
private def roundTrips : Bool := Id.run do
  for d in [2, 5, 6, 10, 245, 1000] do
    for count in [1, 30, 50] do
      for flavor in [Flavor.direct, .postfix, .table] do
        for prependOne in [false, true] do
          let source := reconstruct d count flavor prependOne
          match recognizeLine d (source ++ " (* attribution *)") with
          | some s =>
            unless s.flavor == flavor && s.count == count && s.prependOne == prependOne &&
                s.endPos == source.length do
              return false
          | none => return false
  return true

#guard roundTrips
#guard (recognizeLine 6 "Numerator [ Convergents [ Sqrt [6], 30 ] ]").isSome

private def rejected : List String :=
  ["Numerator[Convergents[Sqrt[7],30]]",
   "Numerator[Convergents[Sqrt[6],0]]",
   "Numerator[Convergents[Sqrt[6],10001]]",
   "Numer ator[Convergents[Sqrt[6],30]]",
   "Numerator[Convergents[Sqrt[6],3 0]]",
   "Numerator[Convergents[Sqrt[6],30]]//Reverse",
   "Numerator[Convergents[Sqrt[6],30]] (* note *) + {1}",
   "Numerator[Convergents[Sqrt[6],30]] (* unclosed",
   "Numerator[Convergents[Sqrt[6],30]] (* nested (* x *)",
   "Numerator[Convergents[Sqrt[6],30]];",
   "Join[{1},Numerator[Convergents[Sqrt[6],30]]] (* or *) other"]

#guard rejected.all fun s => (recognizeLine 6 s).isNone

/-! ### The whole template on a stored sequence -/

private def seqOf (name title : String) (terms : Array String) (mma : String) : SeqSource where
  name := name
  title := title
  offset := 0
  terms := terms
  formulaLines := #[]
  commentLines := #[]
  programs := #[{ language := "mathematica", blockIndex := 0, text := mma, hash := "h" }]

private def outcome (src : SeqSource) : Option (Nat × List String) :=
  match formalize [] src with
  | .items cs => some (cs.size, (cs.map (·.language)).toList)
  | _ => none

private def ordinary (mma : String) : SeqSource :=
  seqOf "A041006" "Numerators of continued fraction convergents to sqrt(6)."
    #["2", "5", "22", "49", "218"] mma

-- main definition (computable + relation) and the recognized program
#guard outcome (ordinary (reconstruct 6 3 .direct false ++ " (* _Joe_, Jan 1 2020 *)")) ==
  some (3, ["maindef", "maindef", "mathematica"])
-- the same expression twice is one snippet; a different count is another
#guard (outcome (ordinary (reconstruct 6 3 .direct false ++ "\n" ++ reconstruct 6 3 .direct false)))
  == some (3, ["maindef", "maindef", "mathematica"])
#guard (outcome (ordinary (reconstruct 6 3 .direct false ++ "\n" ++ reconstruct 6 4 .direct false)))
  == some (4, ["maindef", "maindef", "mathematica", "mathematica"])
-- a program whose leading-one convention disagrees with the sequence is not quoted
#guard outcome (ordinary (reconstruct 6 3 .direct true)) == some (2, ["maindef", "maindef"])
-- the surveyed exceptions carry a leading 1
#guard outcome (seqOf "A001077" "Numerators of continued fraction convergents to sqrt(5)."
    #["1", "2", "9", "38", "161"] "") == some (2, ["maindef", "maindef"])
#guard outcome (seqOf "A001077" "Numerators of continued fraction convergents to sqrt(5)."
    #["2", "9", "38"] "") == none
-- wrong data, non-square radicand, missing terms
#guard outcome (seqOf "A041006" "Numerators of continued fraction convergents to sqrt(6)."
    #["2", "5", "23"] "") == none
#guard outcome (seqOf "A000001" "Numerators of continued fraction convergents to sqrt(9)."
    #["3"] "") == none
#guard outcome (seqOf "A041006" "Numerators of continued fraction convergents to sqrt(6)."
    #[] "") == none

end Oeis.Template.SqrtContinuedFraction.Tests
