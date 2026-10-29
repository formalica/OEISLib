import Mathlib.Tactic

/-!
# Primes in a residue class

Generic parameterized library behind the OEIS template

> Primes congruent to `a` mod `m`.

(~980 sequences). Everything is parameterized by the residue `a` and the modulus `m`;
a concrete sequence only supplies its parameters plus a search bound.

The programs shipped in those sequences all have one of two shapes:

* characteristic functions — `(PARI) is(n)=isprime(n) && n%m==a`
  (Wolfram `MemberQ[{a}, Mod[#, m]]&`, Magma `p mod m eq a`);
* bounded enumerations — Magma `[p: p in PrimesUpTo(B) | p mod m eq a]`,
  Wolfram `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]`,
  Wolfram `Select[Range[s, e, m], PrimeQ]`.

Both shapes are provided here once:

* `isMember a m n` — `n` is prime and `n ≡ a (mod m)` (boolean characteristic function);
* `primesUpTo bound`, `selectFrom l a m`, `membersUpTo a m bound` — the bounded-list
  transcriptions;
* `nthIn a m n bound` — the `n`-th (0-indexed) member `≤ bound`, junk value `0` past the
  end; the generated sequences delegate their main definition to it.

`nthIn_spec` proves that `nthIn` really produces the `n`-th smallest member — prime,
congruent, and preceded by exactly `n` smaller members — which is the high-level
propositional characterization used in the generated files.
-/

namespace OEISLib.Common.Residue

/-! ## Small list helpers -/

/-- Composition of two list filters as one filter (specialized to `Nat`). -/
private theorem filter_and_filter (p q : Nat → Bool) (l : List Nat) :
    (l.filter p).filter q = l.filter (fun x => p x && q x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> by_cases h' : q a <;>
      simp [h, h', Bool.and_comm, ih]

/-- Filter order under `&&` does not matter. -/
private theorem filter_and_comm (p q : Nat → Bool) (l : List Nat) :
    l.filter (fun x => p x && q x) = l.filter (fun x => q x && p x) := by
  apply congrArg (List.filter · l)
  funext x
  simp [Bool.and_comm]

/-- Filtering a range by `< z` cuts it down to `range z` (for `z ≤ k`). -/
private theorem filter_lt_range :
    ∀ k z : Nat, z ≤ k →
      (List.range k).filter (fun x => decide (x < z)) = List.range z
  | 0, z, h => by
      have hz : z = 0 := Nat.le_zero.mp h
      subst hz; rfl
  | k + 1, z, h => by
      by_cases hkz : k < z
      · have hz : z = k + 1 := by omega
        subst hz
        exact List.filter_eq_self.mpr fun x hx => decide_eq_true
          (by simpa using List.mem_range.mp hx)
      · have hd : decide (k < z) = false := decide_eq_false_iff_not.mpr hkz
        rw [List.range_succ, List.filter_append, filter_lt_range k z (by omega),
          List.filter_cons_of_neg (by simp [hd])]
        simp

/-- Window restriction commutes with filtering by another predicate. -/
private theorem filter_P_lt_range {P : Nat → Bool} :
    ∀ k z : Nat, z ≤ k →
      ((List.range k).filter P).filter (fun x => decide (x < z))
        = (List.range z).filter P
  | 0, z, h => by
      have hz : z = 0 := Nat.le_zero.mp h
      subst hz; rfl
  | k + 1, z, h => by
      by_cases hkz : k < z
      · have hz : z = k + 1 := by omega
        subst hz
        have hall : ∀ x ∈ (List.range (k + 1)).filter P,
            decide (x < k + 1) = true := by
          intro x hx
          have h1 : x ∈ List.range (k + 1) := (List.mem_filter.mp hx).1
          simpa using List.mem_range.mp h1
        exact List.filter_eq_self.mpr hall
      · have hd : decide (k < z) = false := decide_eq_false_iff_not.mpr hkz
        have hnil : ([k].filter P).filter (fun x => decide (x < z)) = [] :=
          List.filter_eq_nil_iff.mpr fun x hx => by
            have h1 : x = k := List.mem_singleton.mp (List.mem_filter.mp hx).1
            subst h1
            simpa using hkz
        rw [List.range_succ, List.filter_append, List.filter_append,
          filter_P_lt_range k z (by omega), hnil]
        simp

/-- The first `k` naturals are strictly increasing. -/
private theorem pairwise_range_lt : ∀ k : Nat, (List.range k).Pairwise (· < ·)
  | 0 => by simp
  | k + 1 => by
      rw [List.range_succ]
      refine List.pairwise_append.mpr ⟨pairwise_range_lt k, by simp, ?_⟩
      intro a ha b hb
      have hbk : b = k := List.mem_singleton.mp hb
      subst hbk
      simpa using List.mem_range.mp ha

/-! ## Definitions -/

/-- `n` is prime, as a boolean. -/
def isPrimeB (n : Nat) : Bool := decide (Nat.Prime n)

theorem isPrimeB_iff {n : Nat} : isPrimeB n = true ↔ Nat.Prime n :=
  decide_eq_true_iff

/-- Characteristic function of the residue class inside the primes: `n` is prime and
`n % m = a`. Transcription of `(PARI) is(n)=isprime(n) && n%<m>==<a>` /
Wolfram `MemberQ[{<a>}, Mod[#, <m>]]&` / Magma `p mod <m> eq <a>`. -/
def isMember (a m n : Nat) : Bool := isPrimeB n && n % m == a

theorem isMember_iff {a m n : Nat} :
    isMember a m n = true ↔ Nat.Prime n ∧ n % m = a := by
  simp [isMember, isPrimeB_iff]

/-- All primes `≤ bound`, increasing. -/
def primesUpTo (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter isPrimeB

/-- The elements of `l` lying in the residue class, preserving order. Transcription of
the Wolfram `Select[l, MemberQ[{<a>}, Mod[#, <m>]] &]` /
Magma `[p: p in l | p mod <m> eq <a>]` filters. -/
def selectFrom (l : List Nat) (a m : Nat) : List Nat := l.filter (isMember a m)

/-- All members of the residue class `≤ bound`, increasing. Transcription of Magma
`[p: p in PrimesUpTo(<B>) | p mod <m> eq <a>]`. -/
def membersUpTo (a m bound : Nat) : List Nat := selectFrom (primesUpTo bound) a m

/-- `membersUpTo` as a single filter over the naturals below `bound + 1`. -/
theorem membersUpTo_eq (a m bound : Nat) :
    membersUpTo a m bound =
      (List.range (bound + 1)).filter (fun x => isPrimeB x && x % m == a) := by
  rw [membersUpTo, selectFrom, primesUpTo, filter_and_filter]
  congr 1
  funext x
  simp [isMember]

/-- The `n`-th member (0-indexed) among the members `≤ bound`; junk value `0` when there
are fewer than `n + 1` of them. Main computable definition of the generated sequences. -/
def nthIn (a m n bound : Nat) : Nat := ((membersUpTo a m bound)[n]?).getD 0


theorem mem_primesUpTo {p bound : Nat} :
    p ∈ primesUpTo bound ↔ p ≤ bound ∧ Nat.Prime p := by
  simp [primesUpTo, List.mem_filter, List.mem_range, isPrimeB_iff]

theorem mem_membersUpTo {p a m bound : Nat} :
    p ∈ membersUpTo a m bound ↔ p ≤ bound ∧ isMember a m p = true := by
  rw [membersUpTo_eq, List.mem_filter]
  constructor
  · rintro ⟨hrange, hpred⟩
    exact ⟨Nat.lt_succ_iff.mp (List.mem_range.mp hrange), hpred⟩
  · rintro ⟨hle, hm⟩
    exact ⟨List.mem_range.mpr (by omega), hm⟩

theorem selectFrom_primesUpTo (a m bound : Nat) :
    selectFrom (primesUpTo bound) a m = membersUpTo a m bound := rfl

/-- Within range, `nthIn` returns a genuine class member, hence positive. -/
theorem nthIn_pos {a m n bound : Nat} (h : n < (membersUpTo a m bound).length) :
    0 < nthIn a m n bound := by
  obtain ⟨v, hv⟩ : ∃ v, (membersUpTo a m bound)[n]? = some v :=
    ⟨(membersUpTo a m bound)[n]'h, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩⟩
  rw [nthIn, hv]
  have hmem : v ∈ membersUpTo a m bound := List.mem_of_getElem? hv
  exact Nat.Prime.pos (isMember_iff.mp (mem_membersUpTo.mp hmem).2).1

/-- Bridging `Option.getD` back to a known element. -/
theorem some_getD_self {l : List Nat} {i : Nat} {v : Nat} (h : l[i]? = some v) :
    (l[i]?).getD 0 = v := by rw [h]; rfl

/-- Taking a prefix before filtering yields a (not necessarily contiguous) subsequence
of the full filtered list. This connects the Wolfram `Select[Prime[Range[K]], …]`
transcription to the bounded enumeration: the transcription is the full enumeration,
restricted to members that happen to sit among the first `K` primes. -/
theorem selectFrom_take_sub {l : List Nat} (K a m : Nat) :
    List.Sublist (selectFrom (l.take K) a m) (selectFrom l a m) := by
  induction l generalizing K with
  | nil => simp
  | cons b t ih =>
    unfold selectFrom
    cases K with
    | zero => simp
    | succ k =>
      rw [show List.take (k + 1) (b :: t) = b :: List.take k t from rfl]
      by_cases hb : isMember a m b
      · rw [List.filter_cons_of_pos hb, List.filter_cons_of_pos hb]
        exact List.Sublist.cons_cons _ (ih k)
      · rw [List.filter_cons_of_neg hb, List.filter_cons_of_neg hb]
        have ih' := ih k
        unfold selectFrom at ih'
        exact ih'

/-- Equal-length subsequences are equal. -/
theorem eq_of_sub_of_length {α : Type*} :
    ∀ {l₁ l₂ : List α}, List.Sublist l₁ l₂ → l₁.length = l₂.length → l₁ = l₂ := by
  intro l₁ l₂ s h
  induction s with
  | slnil => rfl
  | cons b s ih =>
    have hle := s.length_le
    simp only [List.length_cons] at h
    omega
  | cons_cons b s ih => rw [ih (by simpa using h)]

/-- The main-definition bridge: the `n`-th member of the canonical bounded list is
exactly what `nthIn` returns (used as `formula_eq` in the generated files). -/
theorem getElem?_nthIn (a m n bound : Nat) :
    (membersUpTo a m bound)[n]? =
      some (nthIn a m n bound) ∨ nthIn a m n bound = 0 := by
  rcases hl : (membersUpTo a m bound)[n]? with _ | v
  · right
    rw [nthIn, hl]
    rfl
  · left
    simp [nthIn, hl]

/-! ## The specification theorem -/

/-- Core counting fact: in a strictly increasing list, the `n`-th element satisfying `p`
satisfies `p` itself, belongs to the list, and has exactly `n` satisfying predecessors. -/
private theorem filter_nth_count_below {l : List Nat} {P : Nat → Bool} :
    l.Pairwise (· < ·) →
    ∀ n : Nat, n < (l.filter P).length →
      ((l.filter P).filter
          (fun x => decide (x < ((l.filter P)[n]?).getD 0))).length = n ∧
      P (((l.filter P)[n]?).getD 0) = true ∧
      ((l.filter P)[n]?).getD 0 ∈ l.filter P := by
  induction l with
  | nil => intro _ n hn; simp at hn
  | cons a t ih =>
    intro hpair n hn
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hpair
    by_cases hP : P a
    · have habove : ∀ x ∈ t.filter P, a < x := fun x hx =>
        @ha x (List.mem_filter.mp hx).1
      rw [List.filter_cons_of_pos hP]
      cases n with
      | zero =>
        refine ⟨?_, hP, List.mem_cons_self ..⟩
        have hnil : (t.filter P).filter (fun x => decide (x < a)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx hc'
          exact Nat.lt_asymm (habove x hx) (of_decide_eq_true hc')
        simp [hnil]
      | succ k =>
        rw [List.filter_cons_of_pos hP] at hn
        have hk : k < (t.filter P).length := by
          simpa using Nat.lt_of_succ_lt_succ hn
        obtain ⟨hc, hp, hm⟩ := ih ht k hk
        refine ⟨?_, hp, List.mem_cons_of_mem _ hm⟩
        have haz : a < ((t.filter P)[k]?).getD 0 := habove _ hm
        rw [show ((a :: t.filter P)[k + 1]?).getD 0 = ((t.filter P)[k]?).getD 0
          from rfl]
        have hcons : List.filter
            (fun x => decide (x < ((t.filter P)[k]?).getD 0)) (a :: t.filter P)
            = a :: List.filter
                (fun x => decide (x < ((t.filter P)[k]?).getD 0)) (t.filter P) :=
          List.filter_cons_of_pos (decide_eq_true haz)
        rw [hcons]
        simp only [List.length_cons]
        omega
    · rw [List.filter_cons_of_neg hP]
      rw [List.filter_cons_of_neg hP] at hn
      exact ih ht n hn

/-- **Specification of `nthIn`**: whenever the class has more than `n` members up to
`bound`, its `n`-th member (0-indexed) is prime, congruent to `a` mod `m`, and preceded
by exactly `n` smaller members. This is the high-level propositional characterization
of the sequences of the template. -/
theorem nthIn_spec {a m n bound : Nat}
    (hn : n < (membersUpTo a m bound).length) :
    Nat.Prime (nthIn a m n bound) ∧ nthIn a m n bound % m = a ∧
      (membersUpTo a m (nthIn a m n bound - 1)).length = n := by
  have hL : membersUpTo a m bound =
      (List.range (bound + 1)).filter (fun x => isPrimeB x && x % m == a) :=
    membersUpTo_eq a m bound
  have hn' : n < ((List.range (bound + 1)).filter
      (fun x => isPrimeB x && x % m == a)).length := by
    have hn2 := hn
    rw [hL] at hn2
    exact hn2
  obtain ⟨hc, hp, hmem⟩ :=
    filter_nth_count_below (pairwise_range_lt (bound + 1)) n hn'
  have hnth : nthIn a m n bound =
      (((List.range (bound + 1)).filter
        (fun x => isPrimeB x && x % m == a))[n]?).getD 0 := by rw [nthIn, hL]
  rw [hnth]
  set z := (((List.range (bound + 1)).filter
    (fun x => isPrimeB x && x % m == a))[n]?).getD 0 with hzdef
  -- the value is a member of the class: prime and congruent
  have hism : isMember a m z = true := hp
  obtain ⟨hprime, hzc⟩ := isMember_iff.mp hism
  refine ⟨hprime, hzc, ?_⟩
  -- it lies below the bound
  have hzin : z ∈ membersUpTo a m bound := by rw [hL]; exact hmem
  have hzle : z ≤ bound := (mem_membersUpTo.mp hzin).1
  -- the count of smaller members equals `n`
  have key : (membersUpTo a m (z - 1)).length =
      (((List.range (bound + 1)).filter
        (fun x => isPrimeB x && x % m == a)).filter
        (fun x => decide (x < z))).length := by
    have hzpos : 0 < z := hprime.pos
    have hr : List.range (z - 1 + 1) = List.range z := by
      have hzz : z - 1 + 1 = z := by omega
      rw [hzz]
    rw [membersUpTo_eq, filter_P_lt_range _ _ (by omega), hr]
  rw [key]
  exact hc

end OEISLib.Common.Residue
