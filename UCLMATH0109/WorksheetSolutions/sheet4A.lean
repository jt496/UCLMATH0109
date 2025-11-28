import Mathlib.Tactic
namespace UCL
/-
Define a structure, whose terms are points on the circle
of radius 1 around the origin in the plane.
-/
@[ext]
structure circle where
  x         : ℝ
  y         : ℝ
  property  : x^2 + y^2 = 1

/-
#01 Adding `@[ext]` above `structure circle` generates the lemmas `circle.ext` -/
#check circle.ext
#check circle.ext_iff

/- Note that we also have the following lemma.-/
#check circle.property


namespace circle

/--
#02 Complete the following definition of an element `one : circle`
-/
def one : circle where
  x := 1
  y := 0
  property :=by norm_num

/-
#03
Create an instance of the class `One circle`, so that we can write `1`
instead of `one`.
-/
instance : One circle where
one := one

/-
#04
Prove the definitional lemmas
-/
lemma one_def : (1 : circle) = ⟨1,0,h⟩ := rfl

lemma one.x : (1 : circle).x = 1:=  rfl

lemma one.y : (1 : circle).y = 0:=  rfl



/-
#05
Define a multiplication operation on `circle`.
-/
def mul (a b : circle) : circle where
  x := a.x * b.x - a.y * b.y
  y := a.x * b.y + a.y * b.x
  property := by
    ring; rw[←mul_add,b.property,mul_one,add_assoc,mul_comm,←mul_add,b.property,mul_one]
    exact a.property

/-
#06
Create an instance of `Mul circle`, so that we can use the symbol `*`
for multiplication on the circle.
-/
instance : Mul circle where
  mul := mul

/-
#07
State and prove definitional lemmas
-/
lemma mul.x (a b : circle) : (a * b).x = a.x * b.x - a.y * b.y := rfl
lemma mul.y (a b : circle) : (a * b).y = a.x * b.y + a.y * b.x := rfl



-- #08
lemma mul_one (a : circle) : a * 1 = a :=by
  ext
  · rw [mul.x]
    rw [one.x,one.y]; norm_num
  · rw [mul.y]
    rw [one.x,one.y]; norm_num

-- #09
lemma mul_comm (a b : circle) : a * b = b * a :=by
  ext
  · rw [mul.x,mul.x]; ring
  · rw [mul.y,mul.y]; ring

/-
#10
-/
lemma mul_assoc (a b c : circle) : (a * b) * c = a * (b * c) :=by
  ext
  · rw [mul.x,mul.x,mul.x,mul.x,mul.y,mul.y]; ring
  · rw [mul.y,mul.y,mul.y,mul.y,mul.x,mul.x]; ring

/-
#11 Define an inverse for multiplication, and create an
instance of the class `Inv circle`, so that we can write `a⁻¹`.
-/
def inv (a : circle) : circle where
  x := a.x
  y := -a.y
  property :=by
    rw [← a.property]
    norm_num

instance : Inv circle where
  inv := inv

--#12
lemma inv.x (a : circle ) : (a⁻¹).x = a.x :=rfl

lemma inv.y (a : circle ) : (a⁻¹).y = -a.y :=rfl


/-
#13
-/
lemma mul_left_inv (a : circle) : a⁻¹ * a = 1 :=by
  ext
  · rw [mul.x,one.x,inv.x,inv.y]; ring
    exact a.property
  · rw [mul.y,one.y,inv.y,inv.x]; ring


/-
#14
Create an instance of `CommGroup circle`, showing that `circle` is
a commutative group.
-/
instance : CommGroup circle where
  mul_assoc := mul_assoc
  one_mul :=
  by
    intro a; rw [mul_comm]; exact mul_one _
  mul_one := mul_one
  inv := inv
  mul_left_inv :=mul_left_inv
  mul_comm := mul_comm
