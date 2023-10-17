import Mathlib.Tactic

/-
We can create a type as a `structure`.
Here is a type whose terms can be thought of as
being points in the plane. They each have an `x`-coordinate
and a `y`-coordinate.
-/

structure Plane where
  x : ℤ
  y : ℤ

/-
We can define terms of type `plane` in one of the following
equivalent methods:
-/

def origin : Plane := {x := 0, y:= 0}
def origin' := Plane.mk 0 0
def origin'' : Plane := ⟨0,0⟩
/-
We can check that these are genuinely the same:
-/
example : origin = origin' := rfl
example : origin' = origin'' := rfl

/-
Give a term `P : Plane`, we can write `P.x` and `P.y` for its `x`- and `y`-coordinates.
-/

#eval origin.x

/-
We'll now introduce an operation of addition on `Plane`.
-/
def plane_add (P Q : Plane) : Plane := ⟨P.x + Q.x, P.y + Q.y⟩
/-
To be able to write `+` for this operation, we need to
create an instance of the class `Add`.
-/
instance : Add Plane where
  add := plane_add

/-
It would also be nice to write `0` instead of `origin`.
For this, we create an instance of the class `Zero`.
-/
instance : Zero Plane where
  zero := origin

/-
We can now prove simple things about the plane like this.
-/
lemma zero_def : (0 : Plane) = origin := rfl

lemma zero_x : (0 : Plane).x = 0 := rfl

lemma zero_y : (0 : Plane).y = 0 := rfl

lemma add_def (P Q : Plane) : P + Q = ⟨P.x + Q.x, P.y + Q.y⟩ := rfl

@[ext]
lemma ext (P Q : Plane) (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q :=
by
  obtain ⟨px,py⟩ := P
  dsimp at hx hy
  rw [hx,hy]

lemma my_add_zero (P : Plane) : P + 0 = P :=
by
  ext
  · rw [add_def, zero_x]
    dsimp
    rw [add_zero]
  · rw [add_def, zero_y]
    dsimp
    rw [add_zero]

lemma my_zero_add (P : Plane) : 0 + P = P :=
by
  sorry

lemma my_add_assoc (P Q R : Plane) : (P + Q) + R = P + (Q + R) :=
by
  sorry

/-
Let's now define `-P` for a point `P : Plane`.
-/
def plane_neg (P : Plane) : Plane := ⟨-P.x, -P.y⟩

instance : Neg Plane where
  neg := plane_neg

lemma neg_def (P : Plane) : -P = ⟨-P.x,-P.y⟩ := rfl

lemma my_add_neg_self (P : Plane) : P + (-P) = 0 := by
  sorry

lemma my_neg_add_self (P : Plane) : -P + P = 0 := by
  sorry

lemma my_add_comm (P Q : Plane) : P + Q = Q + P := by
  sorry


/-
We have now proved all of the axioms, which say that `Plane`
is a commutative group with the operation of addition.
To allow lean to use all the theorems it knows about groups,
we create an instance of `AddGroup Plane`.
-/

instance : AddCommGroup Plane where
  add_assoc     := my_add_assoc
  zero_add      := my_zero_add
  add_zero      := my_add_zero 
  add_left_neg  := my_neg_add_self
  add_comm      := my_add_comm


/-
To demonstrate that this works, prove the following using Mathlib.
-/
example (P R : Plane) : P + R - P = R :=
by
  sorry

example (P Q R : Plane) : P + Q + R = P + R + Q :=
by
  sorry

example (P : Plane) : P - 0 = P :=
by
  sorry
