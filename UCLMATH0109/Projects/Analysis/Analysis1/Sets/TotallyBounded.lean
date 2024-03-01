import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice


namespace UCL
open Finset Nat


/-- Any (closed) bounded interval of reals is totally bounded -/
lemma Icc_totally_bounded {a b : ℝ}(hne : a < b) :
    ∀ ε > 0, ∃ (P : Finset ℝ), ∀ x, a ≤ x → x ≤ b → ∃ p ∈ P, |x - p| < ε :=
by
  sorry
