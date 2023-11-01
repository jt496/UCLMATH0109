import Mathlib
/-
TODO: write a sheet on using Mathlib (following video 2H)
-/


variable (x y z  : ℝ)


-- if `a ≤ b` and  `b < c` then `a < c`
-- In Lean this is `a ≤ b → b < c → a < c`
#check lt_of_le_of_lt


-- 01
example (h1 : x ≤ y) (h2 : y < 3) : x < 3:=
by
  sorry

-- In our next example we need to use `x < y → y ≤ z → x < z`
-- This is also in Mathlib, can you guess its name?
-- 02
example (h1 : x < y) (h2 : y ≤ z) : x < z :=
by
  sorry


-- If we want to show `x = y`, where `x y : ℝ` then we can use the fact that
-- `≤` is anti-symmetric, i.e. `x ≤ y → y ≤ x → x = y`
#check le_antisymm

-- 03
example (h1 : x ≤ 3) (h2 : 3 ≤ x) : x = 3 :=
by
  sorry
/-
Other properties of `<` include
`<` is irreflexive and transitive  -/

#check lt_irrefl -- ¬ x < x
#check lt_trans  -- x < y → y < z → x < z

-- 04 Recall that `exfalso` allows you to prove anything by proving `False`
example (h1 : x < y) (h2 : y < x) : x = 73:=
by
  exfalso
  apply lt_irrefl x
  apply lt_trans h1 h2

/-
If `a < b` then `a ≠ b` -/
#check ne_of_lt
-- 05
example (h1 : x < y) (h2 : y ≤ z) : x ≠ z:=
by
  apply ne_of_lt
  apply lt_of_lt_of_le h1 h2


#check le_trans -- x ≤ y → y ≤ z → x ≤ z
/-
Note that if `h1 : x ≤ y` then `h1.trans` is `le_trans h1`
So if we have `h1 : x ≤ y` and `h2 : y ≤ z` then `h1.trans h2` is `x ≤ z` -/

-- If `a ≤ b` and `c ≤ d` and `0 ≤ c` and `0 ≤ b` then `a * c ≤ b * d`
#check mul_le_mul


-- You can do the next example by using `apply mul_le_mul` and solving
-- the four resulting subgoals. Once you've done this see if you can reduce your
-- proof to a single line `exact mul_le_mul ...` using the `dot` notation.
-- 06
example (h1 : x ≤ y) (h2 : 3 ≤ z) (h3 : 0 ≤ x) (h4 : y ≤ z): 3 * x ≤ z * z :=
by
  exact mul_le_mul h2 (h1.trans h4) h3 <| h3.trans (h1.trans h4)
