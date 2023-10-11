import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-
Mathlib has a number of higher-level tactics:

`ring` can prove identities in commutative rings (eg ℝ, ℤ, ℚ). 
 
`norm_num` normalizes numerical expressions

`linarith` proves results that follow from linear inequalities
-/

lemma sq_add (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  rw [sq, mul_add, add_mul, add_mul, ← sq, ← sq, mul_comm, two_mul, add_mul, 
      add_assoc, add_assoc, add_assoc]
      
lemma sq_add' (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  ring
#print sq_add


lemma pow_four_add (a b : ℝ) : (a + b)^4 = a^4 + 4*a^3*b+ 6*a^2*b^2 + 4*a*b^3 + b^4 :=
by 
  ring

example (a b c : ℝ) (h1: a ≤ 2 * b) (h2: b ≤ 3 * c) : 2*a ≤ 12 *c:=
by
  linarith -- note rel [h1,h2] doesn't work here

example (P : ℝ → Prop) (h : ∀ x : ℝ, P x) : ∃ y , P y:=
by
  use 0; tauto