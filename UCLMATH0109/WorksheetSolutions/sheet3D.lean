import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b x : ℕ) (h₁ : a + b = 5) (h₂ : a * b = 6) :
  x ^ 2 + 5 * x + 6 = (x + a) * (x + b) :=
by
  calc
    _ = x^2 + (a+b) * x + a*b   := by rw [h₁,h₂]
    _ = _                       := by ring

open Polynomial
/-
In the next example, we do a similar kind of calculation in the
ring `ℝ[X]` of polynomials over the real numbers. Prove the
formula using a `calc` block.
-/
example (a b c d : ℝ[X]) (h₁ : a^2 + b^2 = X * c) (h₂ : a * b = d) :
    (X + a^2) * (X+b^2) = X^2 * (1 + c) + d^2 :=
by
  calc
    (X + a^2) * (X + b^2) = X^2 + (a^2 + b^2) * X + (a*b)^2 := by ring
    _                     = X^2 + X * c * X + d^2           := by rw [h₁,h₂]
    _                     = _                               := by ring

/-
Here is an example with inequalities.
Use `ring`, `norm_num`, `rw` and `rel` in a `calc` clock.-/
example (x y : ℝ) (hx : x > 1) (hy : 5 < y) :
  x ^ 3 + 4 * x * y - 20 > 0 :=
by
  calc
    x^3 + 4 * x * y - 20 > 1^3 + 4 * x * y - 20 := by rel [hx]
    _                    = 4 * x * y - 19       := by ring
    _                    > 4 * 1 * 5 - 19       := by rel [hx,hy]
    _                    > 0                    := by norm_num


/-
This last example is a proof that `x^2` is a continuous at the point `x=1`.

You should prove the `have` statement by a single `calc` block,
abd then prove the main result by a single `calc` block.
In each `calc`-block you will only need the tactics`ring`, `rw`, `rel` and `exact`.

You might find the following lemmas from Mathlib useful:
  `lt_min`
  `min_le_left`
  `min_le_right`
  `abs_add`
  `abs_mul`
-/
example (x ε : ℝ) (hε : 0 < ε) :
  ∃ δ, 0 < δ ∧ (|x - 1| < δ → |x^2 - 1^2| < ε) := by
  let δ := min 1 (ε/3)
  have δpos : 0 < δ
  · apply lt_min
    · exact Real.zero_lt_one
    · linarith
  use δ
  constructor
  · exact δpos
  · intro hx
    have : |x + 1| < 3
    · -- use a `calc`-block here.
      calc
        |x + 1| = |(x-1) + 2|       := by ring
        _       ≤ |x-1| + |2|       := by exact abs_add (x - 1) 2 -- used `exact?`
        _       < δ + |2|           := by rel [hx]
        _       = δ + 2             := by norm_num
        _       ≤ 1 + 2             := by rel [min_le_left 1 (ε/3)]
        _       = 3                 := by ring
    -- Use a `calc`-block here. First factorize the left hand side,
    -- and then use `this`, `hx` and `δpos`.
    calc
      |x^2 - 1^2| = |(x+1) * (x-1)|       := by ring
      _           = |x+1| * |x-1|         := by rw [abs_mul]
      _           < 3 * δ                 := by rel [this,hx]
      _           ≤ 3 * (ε / 3)           := by rel [min_le_right 1 (ε/3)]
      _           = ε                     := by ring

