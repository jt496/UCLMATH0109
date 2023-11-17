import Mathlib.Tactic

/-
  #  Higher-level tactics

Mathlib has a number of higher-level tactics:

`ring` can prove identities in commutative rings (eg ℝ, ℤ, ℚ).

`norm_num` can close goals involving numerical expressions.

`decide` can close a goal if Lean knows an algorithm for checking whether the goal is true or false.

`linarith` proves results that follow from linear (in)equalities
`nlinarith` is a version that can handle some non-linear arithmetic

-/

-- 01
example (x y : ℝ) : (x + 2*y)^3 = x^3+6*x^2*y + 12*x*y^2 +8*y^3:=
by
  sorry

-- 02
example (a b c: ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a + 2*b + 3*c ≤ 6*c  :=
by
  sorry

-- 03
example (a b : ℝ) (n : ℕ) : a^n * b ^n = (a*b)^n:=
by
  sorry

-- 04  If a b : ℤ then a ∣ b ↔ ∃ c, c*a = b
example (a : ℤ) : 2 ∣ 4*a + 6 :=
by
  sorry

-- 05
example (a b : ℝ) (n : ℕ) : (a^2 - b^2)^n = (a + b)^n * (a-b)^n :=
by
  sorry


-- 06
example (a b c : ℝ) (ha: 0 ≤ a) (hab : a ≤ 2*b) (hbc : b ≤ 3*c) : a^2 + b^2 ≤ 45*c^2  :=
by
  sorry


-- 07
example : 4 + 3 ≠ 2 :=
by
  sorry


-- 08
example (a b : ℝ) : 4 ≤ a → a ≤ b → 12 ≤ 3*b :=
by
  sorry
  