import Mathlib.Tactic

/-
# Structures

In Lean, there are many `Type`s, for example

  `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`,
  `ℕ → ℝ`, `Set ℕ`, ... etc.

A common way of defining a new `Type` is using the command `structure`.

Below, we define a new `Type` called `Plane` whose terms can be thought of as being
points in the plane. They each have an `x`-coordinate and a `y`-coordinate, both
of which are integers.
-/

@[ext]  -- this line will be explained soon.
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

-- Look back at line 18. This line automatically generates  a lemma `Plane.ext`,
-- which gives us a way of Proving that two terms of type `Plane` are equal.
-- The lemma is used by the `ext` tactic.
#check Plane.ext A B

example : (⟨1,2⟩ : Plane) = ⟨1,n - n + 2⟩ := by
  ext
  · rfl
  · dsimp
    rw [sub_self, zero_add]


/-
# Classes

We might like to be able to add terms of `Plane`.
However, lean does not yet know how to do this. (Uncomment the
following line, to see the error message.)
-/

-- #check A + B

/-
To be able to add Points in `Plane`, we'll start by
defining a function which adds Points.
-/
def my_addition (P Q : Plane) : Plane := ⟨P.x + Q.x, P.y + Q.y⟩

/-
To be able to write `+` for this operation, we need to
create an instance of the class `Add`.

`Add Plane` is a structure whose only field is

  `add : Plane → Plane → Plane`

However, the structure `Add Plane` is a `class`. This means that instead of
defining terms of `Add Plane` using the `def` command, we instead use the
`instance` command. Once we define the term using the `instance` command, lean
will know the meaning of `P + Q` for `P Q : Plane`.

*Warning* One should never define two different instances of type `Add Plane`,
because lean could get confused if there is more than one meaning for `P + Q`.
Since there will only be one term of type `Add Plane`, we will not need to give
it a name.
-/

instance : Add Plane where
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
lemma add_x (P Q : Plane) : (P + Q).x = P.x + Q.x := rfl
lemma add_y (P Q : Plane) : (P + Q).y = P.y + Q.y := rfl

/-
It would also be nice to write `0` instead of `origin`.
For this, we create an instance of the class `Zero`.
-/

instance : Zero Plane where
  zero := origin

#check (0 : Plane)
/-
Here are some definitional lemmas for `Zero`.
-/
lemma zero_def : (0 : Plane) = origin := rfl

lemma zero_x : (0 : Plane).x = 0 := rfl

lemma zero_y : (0 : Plane).y = 0 := rfl

lemma my_add_zero (P : Plane) : P + 0 = P :=
by
  ext  -- look back at line 18 to see why this works.
  · rw [add_x, zero_x, add_zero]
  · rw [add_y, zero_y, add_zero]

lemma my_zero_add (P : Plane) : 0 + P = P :=
by
  ext
  · rw [add_x, zero_x, zero_add]
  · rw [add_y, zero_y, zero_add]


lemma my_add_assoc (P Q R : Plane) :
  (P + Q) + R = P + (Q + R) :=
by
  ext
  · rw [add_x, add_x, add_x, add_x, add_assoc]
  · rw [add_y, add_y, add_y, add_y, add_assoc]

/-
Let's now define `-P` for a Point `P : Plane`.
-/
def my_neg (P : Plane) : Plane := ⟨-P.x, -P.y⟩

instance : Neg Plane where
  neg := my_neg

/-
Here are some definitional lemmas.
-/
lemma neg_def (P : Plane) : -P = ⟨-P.x,-P.y⟩ := rfl
lemma neg_x (P : Plane) : (-P).x = -P.x := rfl
lemma neg_y (P : Plane) : (-P).y = -P.y := rfl

lemma my_add_neg_self (P : Plane) : P + (-P) = 0 := by
  ext
  · rw [add_x, neg_x, zero_x, add_neg_self]
  · rw [add_y, neg_y, zero_y, add_neg_self]

lemma my_neg_add_self (P : Plane) : -P + P = 0 := by
  ext
  · rw [add_x, neg_x, zero_x, neg_add_self]
  · rw [add_y, neg_y, zero_y, neg_add_self]

lemma my_add_comm (P Q : Plane) : P + Q = Q + P := by
  ext
  · rw [add_x,add_x, add_comm]
  · rw [add_y,add_y, add_comm]


/-
We have now proved all of the axioms, which say that `Plane`
is a commutative group with the operation of addition.
To allow lean to use all the theorems it knows about such groups,
we create an instance of `AddCommGroup Plane`.
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
  exact add_sub_cancel' P Q

example (P Q R : Plane) : P + Q + R = P + R + Q :=
by
  exact add_right_comm P Q R

example (P : Plane) : P - 0 = P :=
by
  exact sub_zero P

/-
Lean also knows how to multiply elements of an additive commutative group
by natural numbers and integers. These operations are typed as `•` (scalar multiplication).
The Mathlib terms for these two operations are `nsmul` and `zsmul` (scalar multiplication
by natural numbers and by integers).
-/

example (P : Plane) : 5 • P = P + P + P + P + P :=
by
  rw [succ_nsmul,succ_nsmul,three_nsmul, add_assoc,add_assoc,add_assoc]


example (P : Plane) : (-2:ℤ) • P = -(P + P) :=
by
  rw [neg_zsmul, two_zsmul]
