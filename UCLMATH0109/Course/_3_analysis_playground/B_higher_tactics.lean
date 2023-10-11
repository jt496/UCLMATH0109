import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-
  #  Higher-level tactics

Mathlib has a number of higher-level tactics:

`ring` can prove identities in commutative rings (eg ℝ, ℤ, ℚ). 
 
`norm_num` can close goals involving numerical expressions.

`decide` can close a goal if Lean knows an algorithm for checking whether the goal is true or false.

`linarith` proves results that follow from linear (in)equalities
`nlinarith` is a version that can handle some non-linear arithmetic

`exact?` searchs Mathlib for a result that will close the goal.
`apply?` gives suggestions for a lemma to apply when `exact?` fails.
-/

lemma sq_add (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  rw [sq, mul_add, add_mul, add_mul, ← sq, ← sq, mul_comm, two_mul, add_mul, 
      add_assoc, add_assoc, add_assoc]
      

lemma sq_add' (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  sorry

-- You really wouldn't want to prove this by hand
lemma pow_four_add (a b : ℝ) : (a + b)^4 = a^4 + 4*a^3*b+ 6*a^2*b^2 + 4*a*b^3 + b^4 :=
by 
  sorry


/- 
If we have a goal that is involves numerical expressions then `norm_num` may be able to close it.
-/

lemma less_than : 123123123123123 < 212312312312312 :=
by
  sorry

/-
We can also use `decide` for proving propositions
-/

lemma small_prime : Nat.Prime 13 :=
by
  sorry

-- However sometimes the algorithm called by `decide` will time-out
lemma prime: Nat.Prime 110017 :=
by
  sorry

/-
`linarith` can prove results involving linear (in)equalities
-/

lemma linear_ineq (a b c : ℝ) (h1: a ≤ 2 * b) (h2: b ≤ 3 * c) : 2 * a ≤ 12 *c:=
by
  sorry
/-
For non-linear inequalities we can try `nlinarith`
-/

example (a b : ℝ) : 0 ≤ (a + b)^2 - 2*a*b :=
by
  sorry

/-
`exact?` and `apply?` will both search Mathlib for results that will help you close your
current goal. 

`exact?` will either close the goal or suggest you try `apply?`
`apply?` will either close the goal or suggest possible results that might help
-/


example (a b : ℕ) : a + b - b = a:=
by
  sorry

example (a b c : ℕ) (h : c < a)  : 0 < a + b - c := 
by
  sorry
