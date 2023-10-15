import UCLMATH0109.Course._3_analysis_playground.C_have


/-
A `calc`-block is a useful way of writing a proof which consists of
a series of rearrangements of a formula. This way of writing proofs is
very similar to the way that most mathematicians write proofs on paper,
so the resulting proofs are easy to read.

Here is a simple example.
-/

example (x y a b : ℚ) (hx : x = a^2 - b^2) (hy : y = 2 * a * b) (hab : a^2 + b^2 = 1):
  x^2 + y^2 = 1 :=
by
  calc
  x^2 + y^2 = (a^2-b^2)^2 + (2*a*b)^2                     := by rw [hx,hy]
  _         = a^4 - 2 * a^2 * b^2 + b^4 + 4 * a^2 * b^2   := by ring
  _         = a^4 + 2 * a^2 * b^2 + b^4                   := by ring
  _         = (a^2 + b^2)^2                               := by ring
  _         = 1^2                                         := by rw [hab]
  _         = 1                                           := by rfl

/-
`calc`-blocks can also be used to prove inequalities.
When dealing with inequalities in `calc`-blocks, the tactic `rel` is often useful.
`rel` is similar to `rw`, but substitutes inequalities rather than equalities.
-/

example (a b x y : ℝ) (hx : x = a+2*b) (hy : |a-b| ≤ y) (ha : 10 < a) :
  x + 2 * y > 30  :=
by
  calc
  _ = a + 2*b + 2*y       := by rw [hx]
  _ ≥ a + 2*b + 2*|a-b|   := by rel [hy]
  _ ≥ a + 2*b + 2*(a-b)   := by rel [le_abs_self (a-b)]
  _ = 3 * a               := by ring
  _ > 3 * 10              := by rel [ha]
  _ = 30                  := by norm_num



/-
`calc`-blocks with inequalities are often useful is analysis proofs.
Here is a simple example, proving that limits of sequences are unique.
-/
theorem sLim_unique (ha : limₙ x a) (hb : limₙ x b) : a = b :=
by
  by_contra h
  rw [sLim] at ha hb
  let ε := |a - b| / 2
  have : ε > 0
  · refine half_pos ?this.h
    refine abs_pos.mpr ?this.h.a
    exact sub_ne_zero.mpr h
  specialize ha ε this
  specialize hb ε this
  obtain ⟨Na, hA⟩ := ha
  obtain ⟨Nb, hB⟩ := hb
  let N := max Na Nb
  specialize hA N (by exact Nat.le_max_left Na Nb)
  specialize hB N (by exact Nat.le_max_right Na Nb)
  have := calc
    |a - b| = |(a - x N) + (x N - b)|   := by ring
     _      ≤ |a - x N| + |x N - b|     := by exact abs_add (a - x N) (x N - b)
     _      = |x N - a| + |x N - b|     := by congr 1; exact abs_sub_comm a (x N)
     _      < ε + ε                     := by rel [hA,hB]
     _      = |a - b|                   := by ring
  exact LT.lt.false this
