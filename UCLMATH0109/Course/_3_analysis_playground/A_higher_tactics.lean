import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-
Mathlib has a number of higher-level tactics:

`ring` can prove identities in commutative rings (eg ℝ, ℤ, ℚ). 
 
`norm_num` normalizes numerical expressions
`decide` if Lean has an algorithm for checking whether a proposition holds this will
  try to apply the algorithm.

`linarith` proves results that follow from linear (in)equalities
`nlinarith` is a version that can handle some non-linear arithmetic

`exact?` searchs for a result in Mathlib that will close the goal.
`apply?` can give suggestions for a lemma to apply when `exact?` fails.

-/



lemma sq_add (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  rw [sq, mul_add, add_mul, add_mul, ← sq, ← sq, mul_comm, two_mul, add_mul, 
      add_assoc, add_assoc, add_assoc]
      

lemma sq_add' (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2  :=
by
  ring


lemma pow_four_add (a b : ℝ) : (a + b)^4 = a^4 + 4*a^3*b+ 6*a^2*b^2 + 4*a*b^3 + b^4 :=
by 
  ring


/- 
If we have a goal that is a numerical fact then `norm_num` should be able to prove it.
-/

lemma lessthan : 123123123123123 < 212312312312312 :=
by
  norm_num

/-
We can also use `decide` for proving propositions
-/
lemma prime: Nat.Prime 110017 :=
by
  norm_num


example (a b c : ℝ) (h1: a ≤ 2 * b) (h2: b ≤ 3 * c) : 2 * a ≤ 12 *c:=
by
  linarith -- note rel [h1,h2] doesn't work here


example (a b : ℝ) : 0 ≤ (a + b)^2 - 2*a*b :=
by
  ring
  nlinarith


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
