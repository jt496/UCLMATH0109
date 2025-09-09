import Mathlib.Tactic
namespace UCL
/-
Define a structure, whose terms are points on the circle
of radius 1 around the origin in the plane.
-/
structure circle where
  x         : ℝ
  y         : ℝ
  property  : x^2 + y^2 = 1

/-
#01 Change the code above to automatically generate the lemma `circle.ext`-/
-- #check circle.ext

/- Note that we also have the following lemma.-/
#check circle.property


namespace circle

/--
#02 Complete the following definition of an element `one : circle`
-/
def one : circle where
  x := 1
  y := 0
  property := sorry

/-
#03
Create an instance of the class `One circle`, so that we can write `1`
instead of `one`.
-/
instance : One circle := sorry

/-
#04
prove the definitional lemmas
-/
lemma one_def : (1 : circle) = ⟨1,0,h⟩ := sorry

lemma one.x : (1 : circle).x = 1:= sorry

lemma one.y : (1 : circle).y = 0:= sorry


/-
#05
Define a multiplication operation on `circle`.
-/
def mul (a b : circle) : circle where
  x := a.x * b.x - a.y * b.y
  y := a.x * b.y + a.y * b.x
  property := by
    sorry

/-
#06
Create an instance of `Mul circle`, so that we can use the symbol `*`
for multiplication on the circle.
-/
instance : Mul circle := sorry

/-
#07
State and prove a definitional lemmas
-/
lemma mul.x (a b : circle) : (a * b).x = sorry := sorry
lemma mul.y (a b : circle) : (a * b).y = sorry := sorry

/-
#08
-/
lemma mul_one (a : circle) : a * 1 = a := sorry

/-
#09
-/
lemma mul_comm (a b : circle) : a * b = b * a := sorry

/-
#10
-/
lemma mul_assoc (a b c : circle) : (a * b) * c = a * (b * c) := sorry

/-
#11 Define an inverse for multiplication, and create an
instance of the class `Inv circle`, so that we can write `a⁻¹`.
-/
def inv (a : circle) : circle := sorry

instance : Inv circle := sorry


--#12 prove the definitional lemmas
lemma inv.x (a : circle ) : (a⁻¹).x = sorry := sorry

lemma inv.y (a : circle ) : (a⁻¹).y = sorry := sorry


/-
#13
-/
lemma mul_left_inv (a : circle) : a⁻¹ * a = 1 := sorry

/-
#14
create in instance of `CommGroup circle`, showing that `circle` is
a commutative group.
-/
instance : CommGroup circle where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
  mul_comm := sorry
