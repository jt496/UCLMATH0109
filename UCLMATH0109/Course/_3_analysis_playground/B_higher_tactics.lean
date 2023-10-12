import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-
  #  Higher-level tactics: ring / norm_num / decide / linarith / nlinarith

Mathlib has a number of higher-level tactics:

`ring` can prove identities in commutative rings (eg ℝ, ℤ, ℚ). 

-/

lemma sq_add (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  rw [sq, mul_add, add_mul, add_mul, ← sq, ← sq, mul_comm, two_mul, add_mul, 
      add_assoc, add_assoc, add_assoc]
      

lemma sq_add' (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  ring

-- You really wouldn't want to prove this by hand
lemma pow_four_add (a b : ℝ) : (a + b)^4 = a^4 + 4*a^3*b+ 6*a^2*b^2 + 4*a*b^3 + b^4 :=
by 
  ring

#print sq_add
#print sq_add'
#print pow_four_add


/-
Beware that in `ℕ` subtraction is truncated (so a - b = 0 if a ≤ b). 
`ring` can still be useful in `ℕ` but it sometimes fails badly
-/

lemma nat_add_sub (a b : ℕ) : a + b - b = a:=
by
  exact Nat.add_sub_cancel a b

/- 
 
 `norm_num` can close goals involving numerical expressions.

-/

lemma less_than : (123123123123123 : ℝ) < 212312312312312 :=
by
  norm_num

/-
`decide` can close a goal if Lean knows an algorithm for checking whether the goal is true or false.
-/

lemma small_prime : Nat.Prime 13 :=
by
  decide

-- However sometimes the algorithm called by `decide` will fail
lemma larger_prime: Nat.Prime 110017 :=
by
  norm_num

/-
`linarith` can prove results involving linear (in)equalities. 
-/

lemma linear_ineq (a b c : ℝ) (h1: a ≤ 2 * b) (h2: b ≤ 3 * c) : 2 * a ≤ 12 *c:=
by
  linarith

/-
For non-linear inequalities we can try `nlinarith`.
-/

example (a b : ℝ) : 0 ≤ (a + b)^2 - 2*a*b :=
by
  ring
  nlinarith



