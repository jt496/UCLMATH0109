import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open Finset
open scoped BigOperators


/-#01
Prove this generalized version of the triange inequality by induction.
-/
example (c : ℕ → ℝ) : |c n - c 0| ≤ ∑ i in range n, |c (i+1) - c i| :=
by
  sorry


/-#02
Prove the following formula
for the partial sums of the series `∑ (1 / ((n+1) * (n+2)))`.
You may find it helpful to prove the `have` statement first.
-/
example : ∑ n in range N, 1 / ((n+1)*(n+2) : ℝ) = N / (N+1) :=
by
  have partial_frac : ∀ n : ℕ, 1 / ((n+1)*(n+2) : ℝ) = 1/(n+1 : ℝ) - 1/(n+2 : ℝ)
  · sorry
  sorry
