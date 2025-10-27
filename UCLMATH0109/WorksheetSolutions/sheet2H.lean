import Mathlib


variable (x y z  : ℝ)


-- if `a ≤ b` and  `b < c` then `a < c`
-- In Lean this is `a ≤ b → b < c → a < c`
#check lt_of_le_of_lt


-- 01
example (h1 : x ≤ y) (h2 : y < 3) : x < 3:=
by
  apply lt_of_le_of_lt h1 h2

-- In our next example we need to use `x < y → y ≤ z → x < z`
-- This is also in Mathlib, can you guess its name?
-- 02
example (h1 : x < y) (h2 : y ≤ z) : x < z :=
by
  apply lt_of_lt_of_le h1 h2


-- If we want to show `x = y`, where `x y : ℝ` then we can use the fact that
-- `≤` is anti-symmetric, i.e. `x ≤ y → y ≤ x → x = y`
#check le_antisymm

-- 03
example (h1 : x ≤ 3) (h2 : 3 ≤ x) : x = 3 :=
by
  apply le_antisymm h1 h2
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

-- With `lt_trans` we can also use `dot` notation
-- so `lt_trans h1 h2` can be replaced by `h1.trans h2` in the previous proof
-- 04'
example (h1 : x < y) (h2 : y < x) : x = 73:=
by
  exfalso
  apply lt_irrefl x (h1.trans h2)

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

-- If `b ≤ c` then  `∀ a, a + b ≤ a + c`
#check add_le_add_left --  b ≤ c →  ∀ (a : α), a + b ≤ a + c`
-- Note that if you `Ctrl + click` on `add_le_add_left` above then you will be taken to
-- `mul_le_mul_left` in Mathlib.
-- 06
example (h1 : x ≤ z) (h2 : 2 ≤ x)  : x + 2 ≤ x + z :=
by
  apply add_le_add_left <|  h2.trans h1


-- If `a ≤ b` and `c ≤ d` then `a + c ≤ b + d`
#check add_le_add -- a ≤ b → c ≤ d → a + c ≤ b + d

-- 07
example (h1 : x ≤ y) (h2 : 2 ≤ x) (h3 : y ≤ z) : 2 + x ≤ y + z :=
by
  apply add_le_add (h2.trans h1) (h1.trans h3)


-- If `a ≤ b` and `c ≤ d` and `0 ≤ c` and `0 ≤ b` then `a * c ≤ b * d`
#check mul_le_mul -- `(h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d`

/-
 You can do the next example by using `apply mul_le_mul` and solving
 the four resulting subgoals. Once you've done this see if you can reduce your
 proof to a single line `exact mul_le_mul ...` using the `dot` notation.
 (You could also do this for some of the previous examples.) -/

-- 08
example (h1 : x ≤ y) (h2 : 3 ≤ z) (h3 : 0 ≤ x) (h4 : y ≤ z) : 3 * x ≤ z * z :=
by
  apply mul_le_mul h2 (h1.trans h4) h3 (h3.trans (h1.trans h4))

-- You can do the next example using lemmas we have introduced above, or you can find it in Mathlib
-- 09
example  (h1 : x + y < u + z) : x < u ∨ y < z :=
by
  exact lt_or_lt_of_add_lt_add h1

-- |a - c| ≤ |a - b| + |b - c|
#check abs_sub_le -- (a b c : α) : |a - c| ≤ |a - b| + |b - c|

-- 10 Hint: work out the proof on paper (its easy) and then start with `apply le_trans`
example : |x - u| ≤  |x - y| + |y - z| + |z - u| :=
by
  apply le_trans
  · apply abs_sub_le x z u
  · apply add_le_add_right
    · apply abs_sub_le x y z


-- 10' we can do this in one line.. but you need to put in an underscore to tell Lean to work
-- out the final explicit input to `add_le_add_right`
example : |x - u| ≤  |x - y| + |y - z| + |z - u| :=
by
  apply (abs_sub_le x z u).trans (add_le_add_right (abs_sub_le x y z) _)


-- 10'' in fact Lean can work out all the explicit inputs...
-- If the inputs had been complicated expressions then this would have been very useful!
example : |x - u| ≤  |x - y| + |y - z| + |z - u| :=
by
  apply (abs_sub_le _ _ _).trans (add_le_add_right (abs_sub_le _ _ _) _)
