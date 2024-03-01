import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.Sequences


namespace UCL
open Nat Real Set

/-
We will use Mathlibs definitions of bounds for sets :
-/
#check upperBounds
#check lowerBounds
#check BddAbove
#check BddBelow
/--
b is an upperBound of [a,b] -/
lemma Icc_ub {a b : ℝ}: b ∈ upperBounds (Icc a b) :=
by
  sorry

/--a is a lowerBound on (a,b] -/
lemma Ioc_lb {a b : ℝ} : a ∈ lowerBounds (Ioc a b) :=
by
  sorry

/--[a,b] is bounded above -/
lemma bddAbove_of_Icc {a b : ℝ} : BddAbove (Icc a b) :=
by
  sorry

/--(a,b] is bounded below -/
lemma bddBelow_of_Icc {a b : ℝ} : BddBelow (Ioc a b) :=
by
  sorry

/-- If a < b then (a,b) is not empty-/
lemma exists_mem_Ioo {a b : ℝ} (hab : a < b) : ∃ c, c ∈ Ioo a b :=
by
  sorry

/-- If c ∈ (a,b) then there exists δ > 0 such that (x - δ,x + δ) ⊆ (a,b) -/
lemma exists_nbhd_mem_Ioo {a b : ℝ} (hc : c ∈ Ioo a b) : ∃ δ > 0, ∀ x, |x - c| < δ → x ∈ Ioo a b :=
by
  sorry

/-
The next result is useful for Rolle's lemma where we need to consider endpoints
of [a,b] separately from interior points
-/
/-- If c ∈ [a,b] and c ∉ (a,b) then c is an endpoint -/
lemma mem_Icc_not_Ioo {a b : ℝ} (hic : c ∈ Icc a b) (hno : c ∉ Ioo a b) : c = a ∨ c = b :=
by
  sorry

/-
In Lean the reals, `ℝ`, are defined as the type of equivalence classes of
Cauchy sequences of rational numbers.

The completeness of the reals: if S ⊆ ℝ is nonempty and bounded above it
has a least upper bound
-/
#check exists_isLUB
/-
Lean has functions `Sup : Set ℝ → ℝ` and `Inf : Set ℝ → ℝ` that are the sup/inf
of sets that we can prove are nonempty and bounded above/below respectively.

Rather like 0/0 = 0 these functions take on the junk value of `0` when the
conditions (nonempty and bounded) are not satisfied.
-/
/-- a ≤ sSup s iff .... -/
lemma le_sSup_iff' {s : Set ℝ} (hbd : BddAbove s) (hne : s.Nonempty) :
    a ≤ sSup s ↔ ∀ ε > 0, ∃ x ∈ s, a - ε < x :=
by
  sorry

/-- If s is bdd above and non-empty then there is a sequence of points in s
tending its supremum-/
lemma seq_sLim_sSup (hbd : BddAbove s) (hne : s.Nonempty) :
    ∃ x : ℕ → ℝ, (∀ n, x n ∈ s) ∧ limₙ x (sSup s) :=
by
  sorry

/-- f is bounded below on s iff -f is bounded above on S -/
lemma bddBelow_iff_neg {s : Set ℝ} {f : ℝ → ℝ} : BddBelow (f '' s) ↔ BddAbove ((-f) '' s) :=
by
  sorry
