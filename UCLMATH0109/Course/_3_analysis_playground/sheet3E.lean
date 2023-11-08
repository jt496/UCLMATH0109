import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

open Finset
open scoped BigOperators


/-
Prove this generalized version of the triange inequality by induction.
01 -/
example (c : ℕ → ℝ) : |c n - c 0| ≤ ∑ i in range n, |c (i+1) - c i| :=
by
  sorry


/-
Prove the following formula
for the partial sums of the series `∑ (1 / ((n+1) * (n+2)))`.
You may find it helpful to prove the `have` statement first.
02 -/
example : ∑ n in range N, 1 / ((n+1)*(n+2) : ℝ) = N / (N+1) :=
by
  have partial_frac : ∀ n : ℕ, 1 / ((n+1)*(n+2) : ℝ) = 1/(n+1 : ℝ) - 1/(n+2 : ℝ)
  · sorry
  sorry

/- Recall that if `s` is a Finset then `s.card` is the cardinality of s.
Note this can also be written `card s`
03 -/
example (s t : Finset ℕ)  : card (s ∪ t) + card (s ∩ t) = card s + card t :=
by
  sorry

/-
The next example is easy to solve using a `calc` block if you first find the
correct lemma from Mathlib.
(To do this you could introduce a `have` statement and use `apply?`.)
04 -/
example (s t u : Finset ℕ) : (s ∪ t ∪ u).card ≤ s.card  + t.card + u.card :=
by
  sorry

/-
For this example first prove it on paper: `apply?` with the correct `have` statements
or in a `calc` block should do it.
05 -/
example (s t : Finset ℕ) (f : ℕ → ℕ) (hs : ∀ i, i ∈ s → f i ≤ n) (ht: ∀ i, i ∈ t → f i ≤ 2*n) :
∑ i in s ∪ t, f i ≤ n * s.card + 2 * n * (t \ s).card :=
by
  have hu: s ∪ t = s ∪ (t \ s) := by sorry
  have hD: Disjoint s (t \ s) := by sorry
  -- try setting out a `calc` block to complete this
  sorry

/-

06 -/
example (n : ℕ) (x y : ℕ → ℝ) : |∑ i in range n, x n + y n| ≤ ∑ i in range n, |x n| + ∑ i in range n, |y n|:=
by
  sorry
