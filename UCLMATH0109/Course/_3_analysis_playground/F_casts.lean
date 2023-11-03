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
#check x = n -- x = ↑n



/-
Below we describe the main tactics for dealing with these situations:
`norm_cast` and `push_cast`.

See https://lean-forward.github.io/norm_cast/norm_cast.pdf for more details.
-/
set_option trace.Tactic.norm_cast true
example (a b : ℕ) : (a : ℝ) + b = ((a : ℤ) + b : ℝ) :=
by
  rfl

example (n : ℕ) : (2 * n : ℝ) + 3  = (2 * n : ℤ) + 3 :=
by
-- norm_cast  -- or
  push_cast
  rfl


example (n : ℕ) (z : ℤ) (h : n - z < (5 : ℚ)) : n - z < (5 : ℤ) :=
by
  norm_cast at h
-- notice that `h` doesn't change but the goal does!
