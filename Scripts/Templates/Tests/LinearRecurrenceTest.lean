module
public import Scripts.Templates.LinearRecurrence
public meta import Scripts.Templates.LinearRecurrence

/-! `#guard` tests of the `linearRecurrence` recognizers; a failure breaks `lake build`. -/

namespace Oeis.Template.LinearRecurrence.Tests
public section

open Recognize

/-- Coefficients and quoted text of every recurrence found. -/
private def scan (s : String) : List (List Int × String) :=
  ((scanText (plainSyn #["a", "A000045"]) #["="] "t" s).1.map fun r =>
    (r.recur.coeffs.toList, slice (chars s) r.start r.stop)).toList

private def refused (s : String) : List String :=
  (scanText (plainSyn #["a"]) #["="] "t" s).2.toList

/-! ### Statements -/

#guard scan "a(n) = 19*a(n-1) + a(n-2)" == [([19, 1], "a(n) = 19*a(n-1) + a(n-2)")]
#guard scan "a(n)=1*a(n-1)" == [([1], "a(n)=1*a(n-1)")]
-- glued products, parentheses, unary minus
#guard (scan "a(n) = 2a(n-1) - 3(a(n-2) + a(n-3))").map (·.1) == [[2, -3, -3]]
#guard (scan "a(n) = -a(n-2)").map (·.1) == [[0, -1]]
-- shifted lags and the all-on-one-side form
#guard (scan "a(n+2) = 3*a(n+1) - a(n)").map (·.1) == [[3, -1]]
#guard (scan "a(n+2) - 3*a(n+1) + a(n) = 0").map (·.1) == [[3, -1]]
-- guards and initial values next to it belong to the quoted text
#guard scan "a(n)=a(n-1)+a(n-2) for n>=2; a(0)=0, a(1)=1." ==
  [([1, 1], "a(n)=a(n-1)+a(n-2) for n>=2; a(0)=0, a(1)=1")]
#guard scan "Pell: a(0) = 0, a(1) = 1; for n > 1, a(n) = 2*a(n-1) + a(n-2)." ==
  [([2, 1], "a(0) = 0, a(1) = 1; for n > 1, a(n) = 2*a(n-1) + a(n-2)")]
#guard scan "a(n) = a(n-1) + a(n-2) + a(n-3) for n >= 3 with a(0) = a(1) = 0 and a(2) = 1." ==
  [([1, 1, 1], "a(n) = a(n-1) + a(n-2) + a(n-3) for n >= 3 with a(0) = a(1) = 0 and a(2) = 1")]
-- prose in front, a credit behind
#guard (scan "Recurrence: a(n) = 4*a(n-1) - a(n-2). - _Joe Doe_, Jan 01 2020").map (·.1) == [[4, -1]]
-- own A-number as the name
#guard (scan "A000045(n) = A000045(n-1) + A000045(n-2)").map (·.1) == [[1, 1]]
-- a chain never reaches across the credit of a line
#guard scan "a(0)=8. - _Joe_, Jan 01 2020\na(n) = a(n-1) + a(n-2)" ==
  [([1, 1], "a(n) = a(n-1) + a(n-2)")]
#guard scan "a(n) = a(n-1) + a(n-2). - _Joe_, Jan 01 2020\na(0)=1, a(1)=1" ==
  [([1, 1], "a(n) = a(n-1) + a(n-2)")]
-- two statements in one text
#guard (scan "a(n) = a(n-1) + a(n-2). Also a(n) = 3*a(n-2)").map (·.1) == [[1, 1], [0, 3]]

/-! ### What is not a constant-coefficient homogeneous recurrence -/

#guard scan "a(n) = 1 + a(n-1)" == []
#guard refused "a(n) = 1 + a(n-1)" == ["has a constant or n-dependent term"]
#guard scan "a(n) = n*a(n-1)" == []
#guard scan "a(n) = a(n-1)^2 + a(n-2)" == []
#guard scan "a(n) = a(n-1)/2" == []
#guard scan "a(n) = 2*a(n-1) + b(n)" == []
#guard scan "a(0) = 1, a(1) = 2" == []
-- not the sequence's own equation
#guard scan "b(n) = b(n-1) + b(n-2)" == []
#guard scan "2*a(n) = a(n-1)" == []
#guard scan "Limit_{n->oo} a(n)/a(n-1) = 2" == []

-- what a title may call the sequence
#guard callNames "Fibonacci numbers: F(n) = F(n-1) + F(n-2) with F(0) = 0 and F(1) = 1." == #["F"]
#guard callNames "Number of walks with a(n) steps and b(2) ways" == #["a"]

/-! ### Wolfram -/

private def mma (s : String) : List (List Int × String) :=
  ((scanMathematica s).1.map fun r =>
    (r.recur.coeffs.toList, slice (chars s) r.start r.stop)).toList

#guard mma "LinearRecurrence[{1,1,-1},{1,6,6},70]" ==
  [([1, 1, -1], "LinearRecurrence[{1,1,-1},{1,6,6},70]")]
#guard mma "Table[x, {5}]; LinearRecurrence[{2, 1}, {0, 1}, {1, 20}]" ==
  [([2, 1], "LinearRecurrence[{2, 1}, {0, 1}, {1, 20}]")]
-- trailing zeros in the kernel do not change the recurrence
#guard (mma "LinearRecurrence[{1, 1, 0}, {1, 1, 2}, 30]").map (·.1) == [[1, 1]]
#guard mma "LinearRecurrence[{1,1},{1,1},{n}]" == []
#guard mma "RecurrenceTable[{a[n] == 19 a[n - 1] + a[n - 2], a[0] == 1, a[1] == 19}, a, {n, 0, 20}]"
  == [([19, 1], "RecurrenceTable[{a[n] == 19 a[n - 1] + a[n - 2], a[0] == 1, a[1] == 19}, a, {n, 0, 20}]")]
#guard (mma "RecurrenceTable[{a[n+2] == 3 a[n+1] - a[n], a[1] == 1, a[2] == 3}, a, {n, 1, 20}]").map (·.1)
  == [[3, -1]]
#guard mma "RecurrenceTable[{a[n] == n a[n - 1], a[0] == 1}, a, {n, 0, 20}]" == []
#guard mma "a[0] = 1; a[1] = 19; a[n_] := a[n] = 19 a[n-1] + a[n-2]; Table[a[n], {n, 0, 20}]" ==
  [([19, 1], "a[0] = 1; a[1] = 19; a[n_] := a[n] = 19 a[n-1] + a[n-2]")]
#guard (mma "f[n_Integer] := 3 f[n - 1] - f[n - 2] + 0; f[1] = 1").map (·.1) == [[3, -1]]

/-! ### Programs -/

private def progs (scan : Int → Nat → String → Array Raw × Array String) (s : String)
    (offset : Int := 0) : List (List Int × String) :=
  ((scan offset 20 s).1.map fun r => (r.recur.coeffs.toList, slice (chars s) r.start r.stop)).toList

#guard progs scanPari "a(n)=if(n<2,n,a(n-1)+a(n-2))" ==
  [([1, 1], "a(n)=if(n<2,n,a(n-1)+a(n-2))")]
#guard (progs scanPari "a(n) = if(n<2, n, a(n-1) + a(n-2)); \\\\ _Joe_").map (·.1) == [[1, 1]]
#guard (progs scanPari "a(n)=if(n==0,1,if(n==1,2,3*a(n-1)-a(n-2)))").map (·.1) == [[3, -1]]
#guard (progs scanPari "a(n)=if(n<3,[1,1,2][n+1],a(n-1)+a(n-3))").map (·.1) == [[1, 0, 1]]
#guard (progs scanPari "f(n)=if(n<=1, 1, 2*f(n-1)+f(n-2))").map (·.1) == [[2, 1]]
#guard progs scanPari "a(n)=if(n<2,n,n*a(n-1))" == []
#guard progs scanPari "a(n)=if(n<2,n,a(n-1)+1)" == []
-- the base cases of a recurrence that does not start at its order
#guard (progs scanPari "a(n)=if(n<4,n,a(n-1)+a(n-2))").map (·.1) == [[1, 1]]
-- a different offset moves the base cases, not the recurrence
#guard (progs scanPari "a(n)=if(n<2,1,a(n-1)+a(n-2))" (offset := 1)).map (·.1) == [[1, 1]]

#guard (progs scanMaple "a := proc(n) option remember; if n<2 then n else a(n-1)+a(n-2) fi end proc;").map
  (·.1) == [[1, 1]]
#guard progs scanMaple "a:= n -> `if`(n<2, n, a(n-1)+a(n-2));" ==
  [([1, 1], "a:= n -> `if`(n<2, n, a(n-1)+a(n-2))")]
#guard (progs scanMaple "a := proc(n) if n=0 then 1 elif n=1 then 2 else 3*a(n-1)-a(n-2) end if end proc:").map
  (·.1) == [[3, -1]]
#guard (progs scanMaple "A := proc(n) option remember; if n = 0 or n = 1 then 1 else A(n-1)+A(n-2) fi; end;").map
  (·.1) == [[1, 1]]
#guard (progs scanMaple "a(0):=0: a(1):=1: a(n):=a(n-1)+a(n-2):").map (·.1) == [[1, 1]]

#guard progs scanMagma "[n le 2 select 1 else Self(n-1)+Self(n-2): n in [1..30]]" ==
  [([1, 1], "[n le 2 select 1 else Self(n-1)+Self(n-2): n in [1..30]]")]
#guard progs scanMagma "I:=[1,1]; [n le 2 select I[n] else 3*Self(n-1)-Self(n-2): n in [1..30]]" ==
  [([3, -1], "I:=[1,1]; [n le 2 select I[n] else 3*Self(n-1)-Self(n-2): n in [1..30]]")]
#guard progs scanMagma "[n le 2 select 1 else Self(n-1)+1: n in [1..30]]" == []

/-! ### Python and Haskell -/

#guard (progs scanPython "def a(n):\n    if n < 2: return n\n    return a(n-1) + a(n-2)").map (·.1) ==
  [[1, 1]]
#guard progs scanPython "@cached_function\ndef a(n):\n    if n == 0:\n        return 1\n    elif n == 1:\n        return 2\n    else:\n        return 3*a(n-1) - a(n-2)  # note\nprint(a(5))" ==
  [([3, -1], "def a(n):\n    if n == 0:\n        return 1\n    elif n == 1:\n        return 2\n    else:\n        return 3*a(n-1) - a(n-2)")]
#guard (progs scanPython "def a(n):\n    return n if n < 2 else a(n-1) + a(n-2)").map (·.1) == [[1, 1]]
#guard progs scanPython "def a(n):\n    return a(n-1)**2 + 1" == []
#guard (progs scanPython "a = [1, 1]\nfor i in range(2, 30):\n    a.append(a[i-1] + a[i-2])").map (·.1) ==
  [[1, 1]]
#guard (progs scanPython "a = [1, 3]\nfor i in range(2, 30): a.append(3*a[-1] - a[-2])").map (·.1) ==
  [[3, -1]]

-- the stored programs have lost their indentation
#guard (progs scanPython "def a(n):\nif n in [0, 1]:\nreturn [1, 10][n]\nreturn 9*a(n-1)+6*a(n-2)").map
  (·.1) == [[9, 6]]
#guard (progs scanPython "@CachedFunction\ndef a(n): # a = A105051\nif (n<3): return (0,1,5)[n]\nelse: return 4*a(n-1) -5*a(n-2) +2*a(n-3)\n[a(n) for n in range(41)]").map
  (·.1) == [[4, -5, 2]]
#guard (progs scanPython "def a(n): return [1, 3][n-1] if n < 3 else a(n-1) + a(n-2)" (offset := 1)).map
  (·.1) == [[1, 1]]
#guard (progs scanMaple "A := proc(n)\noption remember ;\nif n <= 1 then\nn;\nelse\n5*procname(n-1)-9*procname(n-2) ;\nend if;\nend proc:").map
  (·.1) == [[5, -9]]

#guard (progs scanHaskell "a 0 = 1\na 1 = 2\na n = 3 * a (n-1) - a (n-2)").map (·.1) == [[3, -1]]
#guard progs scanHaskell "a 0 = 1\na 1 = 2\na n = 3 * a (n-1) - a (n-2) -- _Joe_" ==
  [([3, -1], "a 0 = 1\na 1 = 2\na n = 3 * a (n-1) - a (n-2)")]
#guard (progs scanHaskell "fibs = 0 : 1 : zipWith (+) fibs (tail fibs)").map (·.1) == [[1, 1]]
#guard progs scanHaskell "a n = a (n-1) * 2 + n" == []

-- a period is not a recurrence
#guard scan "a(n+25239592216021) = a(n)" == []

/-! ### The template on a whole sequence -/

private def seqOf (title : String) (terms : List String) (formulas : List String)
    (programs : List ProgramBlock := []) (offset : Int := 0) : SeqSource where
  name := "A000045"
  title := title
  offset := offset
  terms := terms.toArray
  formulaLines := formulas.toArray
  commentLines := #[]
  programs := programs.toArray

private def fibTerms : List String := ["0", "1", "1", "2", "3", "5", "8", "13", "21", "34", "55"]
private def fibMma : ProgramBlock :=
  { language := "mathematica", blockIndex := 0, text := "LinearRecurrence[{1, 1}, {0, 1}, 40]",
    hash := "h" }

private def items (v : Verdict) : Array Candidate :=
  match v with
  | .items cs => cs
  | _ => #[]

private def fibItems := items (formalize [] (seqOf "Fibonacci numbers: F(n) = F(n-1) + F(n-2) with F(0) = 0 and F(1) = 1."
  fibTerms ["a(n) = a(n-1) + a(n-2)."] [fibMma]))

-- one item for the one recurrence, with the title, the formula and the program as its sources
#guard fibItems.size == 1
#guard fibItems[0]!.sources.size == 3 &&
  ["maindef", "formula", "mathematica"].all fun l => fibItems[0]!.sources.any (·.language == l)
#guard fibItems[0]!.auxCode ==
  "def linearrec : LinearRecurrence Nat :=\n  ⟨2, ![1, 1]⟩\n\ndef init : Fin 2 → Nat :=\n  ![0, 1]"
-- it is the main definition: no equation with itself
#guard fibItems[0]!.leanType == "Nat → Nat" && fibItems[0]!.leanCode == "fun n => linearrec.mkSol init n"
#guard fibItems[0]!.eqStatement == "" && fibItems[0]!.argKind == "Nat"
#guard fibItems[0]!.verifiedUpto == 11

-- without a title recurrence the item is an alternative, equal to `fn` up to a `sorry`
private def alt := items (formalize [] (seqOf "Fibonacci numbers." fibTerms
  ["a(n) = a(n-1) + a(n-2)."]))
#guard alt.size == 1 && alt[0]!.leanType == "Nat → Nat"
#guard alt[0]!.eqStatement == "∀ n : Nat, «self» n = «main».fn n" && alt[0]!.eqProof == "sorry"

-- negative coefficients over a `Nat`-valued sequence go through `Int`
private def cheb := items (formalize [] (seqOf "x" ["1", "4", "15", "56", "209", "780", "2911"]
  ["a(n) = 4*a(n-1) - a(n-2)"]))
#guard cheb.size == 1
#guard cheb[0]!.auxCode ==
  "def linearrec : LinearRecurrence Int :=\n  ⟨2, ![-1, 4]⟩\n\ndef init : Fin 2 → Int :=\n  ![1, 4]"
#guard cheb[0]!.leanCode == "fun n => (linearrec.mkSol init n).toNat" && cheb[0]!.leanType == "Nat → Nat"

-- a sequence that starts at 1: the position is shifted, the equation holds from the offset on
private def shifted := items (formalize [] (seqOf "x" ["1", "1", "2", "3", "5", "8", "13"]
  ["a(n) = a(n-1) + a(n-2)"] (offset := 1)))
#guard shifted[0]!.leanCode == "fun n => linearrec.mkSol init (n - 1)"
#guard shifted[0]!.eqStatement == "∀ n : Nat, 1 ≤ n → «self» n = «main».fn n"

-- the main definition of a sequence that starts at 1 takes a `PNat`
private def pnatMain := items (formalize [] (seqOf "a(n) = a(n-1) + a(n-2)"
  ["1", "1", "2", "3", "5", "8", "13"] [] (offset := 1)))
#guard pnatMain[0]!.argKind == "PNat" && pnatMain[0]!.leanType == "PNat → Nat"
#guard pnatMain[0]!.leanCode == "fun n => linearrec.mkSol init (n.val - 1)"

-- two recurrences of one sequence are two items; the title's is the main definition
private def two := items (formalize [] (seqOf "a(n) = a(n-1) + a(n-2)" fibTerms
  ["a(n) = 2*a(n-2) + a(n-3), n > 2"]))
#guard two.size == 2 && two[0]!.eqStatement == "" && two[1]!.eqStatement != ""

-- refused: a constant term, data that disagrees, too few terms, a negative offset
private def refusedVerdict (v : Verdict) : Bool := match v with | .skip _ => true | _ => false
#guard refusedVerdict (formalize [] (seqOf "x" ["1", "2", "3", "4", "5", "6"] ["a(n) = 1 + a(n-1)"]))
#guard refusedVerdict (formalize [] (seqOf "x" ["1", "2", "3", "5", "8", "14"] ["a(n) = a(n-1) + a(n-2)"]))
#guard refusedVerdict (formalize [] (seqOf "x" ["1", "1", "2"] ["a(n) = a(n-1) + a(n-2)"]))
#guard refusedVerdict (formalize [] (seqOf "x" fibTerms ["a(n) = a(n-1) + a(n-2)"] (offset := -1)))
-- a stated initial value that disagrees with the data
#guard refusedVerdict (formalize [] (seqOf "x" fibTerms ["a(n) = a(n-1) + a(n-2), a(0) = 1, a(1) = 1"]))

/-! ### Verification against the published terms -/

private def check (r : Rec) (claim : Claim) (offset : Int) (data : List Int) : Bool :=
  (r.verify claim offset data.toArray 1000 3).toOption.isSome

private def fib : Rec := ⟨#[1, 1]⟩
private def fibData : List Int := [0, 1, 1, 2, 3, 5, 8, 13, 21]

#guard check fib .none 0 fibData
-- data that is not Fibonacci
#guard !check fib .none 0 [0, 1, 1, 2, 3, 5, 8, 14, 22]
-- too short to say anything
#guard !check fib .none 0 [0, 1, 1, 2]
-- stated values are cross-checked, at their own indices
#guard check fib (.values #[(0, 0), (1, 1)]) 0 fibData
#guard !check fib (.values #[(0, 1), (1, 1)]) 0 fibData
#guard !check fib (.values #[(3, 1), (4, 2)]) 3 fibData
-- a program listing: the output has to be the data
#guard check fib (.listing #[1, 1] #[0, 1] 1 1 9) 0 fibData
#guard check fib (.listing #[1, 1] #[1, 1] 1 1 8) 0 (fibData.drop 1)
#guard !check fib (.listing #[1, 1] #[1, 1] 1 2 8) 0 (fibData.drop 1)
#guard !check fib (.listing #[1, 1] #[1, 1] 1 1 9) 0 fibData

end
end Oeis.Template.LinearRecurrence.Tests
