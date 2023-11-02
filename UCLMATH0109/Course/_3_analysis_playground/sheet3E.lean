import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open Finset
open scoped BigOperators
noncomputable section

def c : ℕ → ℝ := fun n ↦ 1 / ((n+1)*(n+2))

def S : ℕ → ℝ := fun N ↦ ∑ n in range N, c n

lemma c_def : c n = 1 / ((n+1)*(n+2)) := rfl

lemma S_def : S N = ∑ n in range N, c n := rfl


theorem S_eq : S N = 1 - 1 / (N+1) :=
by
  have partial_frac : ∀ n, c n = 1/(n+1 : ℝ) - 1/(n+2 : ℝ)
  · sorry
  sorry
