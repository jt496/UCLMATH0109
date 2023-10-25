import Mathlib.Tactic
import Mathlib.Data.Real.Basic



example (a b x : ℕ) (h₁ : a + b = 5) (h₂ : a * b = 6) :
  x ^ 2 + 5 * x + 6 = (x + a) * (x + b) :=
by
  calc
    _ = x^2 + (a+b) * x + a*b := by rw [h₁,h₂]
    _ = _ := by ring




open Polynomial
/-
In the next example, we do a similar kind of calculation in the
ring `ℝ[X]` of polynomials over the real numbers.
-/
example (a b c d : ℝ[X]) (h₁ : a^2 + b^2 = X * c) (h₂ : a * b = d) :
    (X + a^2) * (X+b^2) = X^2 * (1 + c) + d^2 := by
  calc
    _ = X^2 + (a^2 + b^2) *X + (a * b)^2 := by ring
    _ = X^2 + X * c  * X + d^2           := by rw [h₁, h₂]
    _ = _                                := by ring


/-
This next example is a proof that `x^2` is a continuous function of `x`.
You should prove the `have` statement by a single `calc` block,
abd then prove the main result by a single `calc` block. In each `calc`-block
you should only use the tactics `ring`, `rw`, `rel` and `exact`.

You might find the following lemmas from Mathlib useful:
  `min_le_left`
  `min_le_right`
  `abs_add`
  `abs_mul`
-/
example (x ε δ : ℝ) (hδ : δ = min 1 (ε/3)) (hx : |x - 1| < δ) :
  |x^2 - 1^2| < ε :=
by
  have : |x + 1| < 3 := by
    sorry
  sorry
