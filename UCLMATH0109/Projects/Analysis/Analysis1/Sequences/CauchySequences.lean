import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.Subsequences


namespace UCL

/-

We say a sequence is `Cauchy` iff for all ε > 0 there is N such
that all subsequent terms are within ε of x_N -/

/-- A sequence is Cauchy iff ∀ ε >0, ∃ N, ∀ n ≥ N, |x n - x N| < ε -/
def Cauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - x N| < ε

/-- A sequence is Cauchy₂ if ∀ ε>0, ∃ N, ∀ m n, N ≤ m → N ≤ n → |x n - x m|< ε -/
def Cauchy₂ (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → |x n - x m| < ε

/-- The more cumbersome but familiar definition is equivalent to the one we use.-/
lemma cauchy_iff_cauchy₂ : Cauchy x ↔ Cauchy₂ x :=
by
  sorry

/-- Any convergent sequence is Cauchy -/
lemma cauchyOfSlim (h : limₙ x a) : Cauchy x :=
by
  sorry

open Finset

/-- Any Cauchy sequence is bounded -/
lemma bd_of_cauchy (h : Cauchy x) : Bd x :=
by
  sorry

/-- If a Cauchy sequence contains a convergent subsequence then it converges -/
lemma subseq_sLim_of_cauchy_imp_sLim (h : Cauchy x)
    (hf : ∃ f : ℕ → ℕ, StrictMono f ∧ limₙ (x ∘ f) a) : limₙ x a :=
by
  sorry

/-- Any Cauchy sequence converges -/
theorem sLim_of_cauchy (h : Cauchy x) : ∃ a, limₙ x a :=
by
  sorry
