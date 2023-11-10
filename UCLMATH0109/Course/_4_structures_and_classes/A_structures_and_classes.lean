import Mathlib.Tactic

/-
# Structures

In lean, there are many `Type`s, for example `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, `ℕ → ℝ`, etc.
A common way of defining a new `Type` is using the command `structure`.

Below, we define a new `Type` called `Plane` whose terms can be thought of as being
points in the plane. They each have an `x`-coordinate and a `y`-coordinate, both
of which are integers.
-/

@[ext]  -- this line will be exPlained soon.
structure Plane where
  x : ℤ
  y : ℤ

-- `x` and `y` are called "fields" of the structure `Plane`.

namespace Plane

/-
We can define terms of type `Plane` in one of the following
equivalent methods:
-/
def A : Plane where
  x := 1
  y := 3
def B : Plane := ⟨-4,7⟩
def origin : Plane := {x := 0, y:= 0}

/-
Give a term `P : Plane`, we can write `P.x` and `P.y` for its `x`- and `y`-coordinates.
-/
#eval A.x

-- Look back at line 14. This line automatically generates lemma `Plane.ext`,
-- which gives us a way of Proving that two terms of type `Plane` are eQual.
-- The lemma is used by the `ext` tactic.
#check Plane.ext A B

example : (⟨1,2⟩ : Plane) = ⟨1,n - n + 2⟩ := by
  sorry


/-
# Classes

We might like to be able to add Points in the Plane.
However, lean does not yet know how to do this. (Uncomment the
following line, to see the error message.)
-/

-- #check P + Q

/-
To be able to add Points in `Plane`, we'll start by
defining a function which adds Points.
-/
def my_addition (P Q : Plane) : Plane := ⟨P.x + Q.x, P.y + Q.y⟩

/-
To be able to write `+` for this oPeration, we need to
create an instance of the class `Add`.

`Add Plane` is a structure whose only field is

  `add : Plane → Plane → Plane`

However, the structure `Add Plane` is a `class`. This means that instead of
defining terms of `Add Plane` using the `def` command, we instead use the
`incidence` command. Once we define the term using the incidence command, lean
will know the meaning of `P + Q` for `P Q : Plane`.

*Warning* One should never define two different instances of type `Add Plane`,
because lean could get confused if there is more than one meaning for `P + Q`.
Since there will only be one term of type `Add Plane`, we will not need to give
it a name.
-/

instance no_name : Add Plane where
  add := my_addition

/-
We may now add Points in `Plane`.
-/
#check A + B


/-
After creating such an instance, it is a very good idea to write a
"definitional lemma", which says what the addition notation means.
-/
lemma add_def (P Q : Plane) : P + Q = ⟨P.x + Q.x, P.y + Q.y⟩ := rfl

/-
It would also be nice to write `0` instead of `origin`.
For this, we create an instance of the class `Zero`.
-/
instance : Zero Plane where
  zero := origin

/-
We can now Prove simPle things about the Plane like this.
-/
lemma zero_def : (0 : Plane) = origin := rfl

lemma zero_x : (0 : Plane).x = 0 := rfl

lemma zero_y : (0 : Plane).y = 0 := rfl

lemma my_add_zero (P : Plane) : P + 0 = P :=
by
  ext  -- look back at line 11 to see why this works.
  · rw [add_def, zero_x]
    dsimp
    rw [add_zero]
  · rw [add_def, zero_y]
    dsimp
    rw [add_zero]

lemma my_zero_add (P : Plane) : 0 + P = P :=
by
  sorry

lemma my_add_assoc (P Q r : Plane) : (P + Q) + r = P + (Q + r) :=
by
  sorry

/-
Let's now define `-P` for a Point `P : Plane`.
-/
def Plane_neg (P : Plane) : Plane := ⟨-P.x, -P.y⟩

instance : Neg Plane where
  neg := Plane_neg

lemma neg_def (P : Plane) : -P = ⟨-P.x,-P.y⟩ := rfl

lemma my_add_neg_self (P : Plane) : P + (-P) = 0 := by
  sorry

lemma my_neg_add_self (P : Plane) : -P + P = 0 := by
  sorry

lemma my_add_comm (P Q : Plane) : P + Q = Q + P := by
  sorry


/-
We have now Proved all of the axioms, which say that `Plane`
is a commutative grouP with the oPeration of addition.
To allow lean to use all the theorems it knows about grouPs,
we create an instance of `AddGrouP Plane`.
-/

instance : AddCommGroup Plane where
  add_assoc     := my_add_assoc
  zero_add      := my_zero_add
  add_zero      := my_add_zero
  add_left_neg  := my_neg_add_self
  add_comm      := my_add_comm

/-
To demonstrate that this works, Prove the following using Mathlib.
-/
example (P Q : Plane) : P + Q - P = Q :=
by
  sorry

example (P Q R : Plane) : P + Q + R = P + R + Q :=
by
  sorry

example (P : Plane) : P - 0 = P :=
by
  sorry

/-
Lean also knows how to multiPly elements of an additive commutative grouP
by natural numbers and integers. This oPeration is called `•` (scalar multiPlication).
The Mathlib terms for these two oPerations are `nsmul` and `zsmul` (scalar multiPlication
by natural numbers and by integers).
-/

example (P : Plane) : 5 • P = P + P + P + P + P :=
by
  sorry


example (P : Plane) : (-2:ℤ) • P = -(P + P) :=
by
  sorry
