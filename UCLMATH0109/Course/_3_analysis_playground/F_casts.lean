import Mathlib.Tactic
/-
If `a : A` and `b : B`, then the expression `a = b` does not make
sense in Lean.
-/
section
variable (A B : Type) (a : A) (b : B)
-- #check a = b
/-
type mismatch
  b
has type
  B : Type
but is expected to have type
  A : Type

Lean is complaining that this doesn't make sense because `=` is only defined for
terms of the same type, so given the LHS `a : A` it was expecting the RHS of the
equality to also be a term of type A.
-/
end

/-
But as mathematicians we happily form expressions that involve terms
of different types.

For example if `n : ℕ` and `x : ℝ` then `x = n` is a perfectly reasonable proposition.

Lean requires us to convert the smaller type ℕ to the larger type ℝ.
This is called a `coercion` or `cast`
-/
variable (n : ℕ) (x : ℝ)
#check x = n -- x = ↑n, th `↑` in the Infoview indicates that a coercion has taken place

/-
Below we describe the main tactics for dealing with these situations:
`norm_cast`, `push_cast`, `exact_mod_cast`, `rw_mod_cast`.

See https://lean-forward.github.io/norm_cast/norm_cast.pdf for more details.

-/

example (a b : ℕ) : a + b = (a : ℤ) + b :=
by
  sorry

example (a b : ℕ) : (a + b : ℕ) = (a : ℝ) + b :=
by
  sorry
--  exact Nat.cast_add a b


example (n : ℕ) : (2 * n : ℝ) + 3  = (2 * n : ℤ) + 3 :=
by
-- norm_cast  -- or
  push_cast
  rfl

example (a b : ℕ) : (a : ℝ) + b = (((a : ℤ) + (b : ℚ) : ℝ) : ℂ) :=
by
  push_cast
  norm_cast


example (n : ℕ) (z : ℤ) (h : n - z < (5 : ℚ)) : n - z < 5 :=
by
  sorry



-- If (a b : ℕ) and a ≤ b then a - b = 0 (subtraction is `truncated` in ℕ)
example (a b : ℕ) (h : a ≤ b) : a - b = 0 :=
by
  exact Nat.sub_eq_zero_of_le h


example (a b : ℕ): a - (a + b) = 0 :=
by
  exact Nat.sub_self_add a b


example (a b : ℕ)  : (b : ℤ) - a  = b - a:=
by
  sorry


example (a b : ℕ) : (a : ℤ) - (a + b) = -b :=
by
  sorry


example (a b c: ℕ) (h : c = a + b) : (a : ℤ) - c = -b :=
by
  sorry


example (a b : ℕ) (h : a ≤ b) : (b - a : ℕ)  = (b : ℤ)  - a:=
by
  sorry


/-
If (n d : ℕ) then n / d is a natural number, n = (n / d) * d does not hold
unless d divides n. Instead we have `n = (n / d) * d + (n % d)` where `n % d` is
the remainder of n mod d,
-/
example (n d : ℕ) (h: d ∣ n) : (n / d) * d = n :=
by
  exact Nat.div_mul_cancel h

/-
A useful tactic for cancelling denominators is `cancel_denom`
-/
open scoped BigOperators
open Finset


example (n : ℕ) : ∑ i in range n.succ, (i : ℝ)^(3 : ℕ) = (n : ℝ)^2 * (n + 1 : ℝ)^2/4 :=
by
  cancel_denoms -- only works for Fields
  induction n with
  | zero =>
    norm_cast
  | succ n ih =>
    rw [sum_range_succ]
    rw [mul_add, ih, Nat.succ_eq_add_one]
    norm_cast
    ring






/-
The binomial coefficient `n.choose k` is the number of subsets of size k from
a set of size n. In Lean this is defined as:

def choose : ℕ → ℕ → ℕ
  | _    , 0     => 1 (there is one empty set)
  | 0    , _ + 1 => 0 (the empty set has no subsets that are non-empty)
  | n + 1, k + 1 => n.choose k + n.choose (k + 1) Pascal's Identity

Note that `n.choose k = n! / (k! * (n - k)!)`, but this is a theorem not a definition
(and doesn't hold if n = 0 and k = 1)

-/
-- This last example can be solved using the following two results, together
-- with `norm_cast` and `apply?`
#check div_lt_one -- if 0 < b then a / b < 1 ↔ a < b
#check Nat.choose_succ_succ -- Pascal's identity

/-- If k ≤ n then `(n choose k + 1)/(n + 1 choose k + 1) < 1 -/
example (n : ℕ) (h : k ≤ n): (n.choose (k + 1) : ℝ) / ((n + 1).choose (k + 1)) < 1:=
by
  sorry
