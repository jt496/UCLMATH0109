import Mathlib.Tactic

/-
If `a : α` and `b : β`, then the expression `a = b` does not make
sense in Lean.
-/
section
variable (α β : Type) (a : α) (b : β)
-- #check a = b
/-
type mismatch
  b
has type
  β : Type
but is expected to have type
  α : Type

Lean is complaining that this doesn't make sense because `=` is only defined for
terms of the same type, so given the LHS `a : α` it was expecting the RHS of the
equality to also be a term of type A.

But as mathematicians we happily form expressions that involve terms
of different types.

For example if `n : ℕ` and `x : ℝ` then `x = n` is a perfectly reasonable proposition.

Lean requires us to convert the smaller type ℕ to the larger type ℝ.
This is called a `coercion` or `cast`
-/
variable (n : ℕ) (x : ℝ)
#check x = n -- x = ↑n, th `↑` in the Infoview indicates that a coercion has taken place
end

/-
Below we describe the main tactics for dealing with these situations:
`norm_cast` and `push_cast`,

See https://lean-forward.github.io/norm_cast/norm_cast.pdf for more details.

-/
-- 01
example (a b : ℕ) : a + b = (a : ℤ) + b :=
by
  sorry

-- 02
example (a b : ℕ) : (a + b : ℕ) = (a : ℝ) + b :=
by
  sorry

-- 03
example (n : ℕ) : (2 * n : ℝ) + 3  = (2 * n : ℤ) + 3 :=
by
  sorry

-- 04
example (a b : ℕ) (c : ℤ) : (a + b : ℕ) + (c : ℤ) = (((a : ℤ) + (b + c : ℚ) : ℝ) : ℂ) :=
by
  sorry

-- 05
example (n : ℕ) (z : ℤ) (h : n - z < (5 : ℚ)) : n - z < 5 :=
by
  sorry


-- If (a b : ℕ) and a ≤ b then a - b = 0 (subtraction is `truncated` in ℕ)
-- 06
example (a b : ℕ) (h : a ≤ b) : a - b = 0 :=
by
  exact Nat.sub_eq_zero_of_le h

-- 07
example (a b : ℕ) : (a : ℤ) - (a + b) = -b :=
by
  sorry


-- 08
example (a b c: ℕ) (h : c = a + b) : (a : ℤ) - c = -b :=
by
  sorry


-- 09
example (a b : ℕ) (h : a ≤ b) : (b - a : ℕ)  = (b : ℤ)  - a:=
by
  sorry


/-
If (n d : ℕ) then n / d is a natural number, n = (n / d) * d does not hold
unless d divides n. Instead we have `n = (n / d) * d + (n % d)` where `n % d` is
the remainder of n mod d,
-/
-- 10
example (n d : ℕ) (h: d ∣ n) : (n / d) * d = n :=
by
  sorry

-- 11
example (a b c : ℕ) (hb: b ∣ a) (hc: c ∣ a) (ha : a ≠ 0)   :
((a / b : ℕ)) / (a / c : ℕ) = (c : ℝ )/ b :=
by
  have hab: ((a / b : ℕ) : ℝ) = (a : ℝ) / b
  · sorry
  have hac: ((a / c : ℕ) : ℝ) = (a : ℝ) / c
  · sorry
  sorry


-- 12
example (a b : ℕ) (h: a ∣ b) : (a : ℤ) ∣ (-(b : ℤ)):=
by
  sorry

-- 13
example (a b : ℕ) (z : ℤ) (ha : z ≤ a) (hb : z ≤ b) : z ≤ min (a : ℝ) b :=
by
  sorry

/-
A useful tactic for cancelling denominators is `cancel_denoms`
-/
open scoped BigOperators
open Finset

-- 14
example (n : ℕ) : ∑ i in range n.succ, (i : ℝ)^(3 : ℕ) = (n : ℝ)^2 * (n + 1 : ℝ)^2/4 :=
by
  sorry
