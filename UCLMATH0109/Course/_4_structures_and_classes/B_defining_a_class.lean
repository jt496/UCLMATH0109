import Mathlib.Tactic

/-
A `class` is a special kind of `structure`;
This file demonstrates how to create and use a `class`.

Let's define the notion of a group in lean.
Recall that a group is a set `G`, together with
* a multiplication operation `G → G → G`,
* a function `G → G` taking an element `x` to an element `x⁻¹`,
* a certain element in `G` called `1`.
Furthermore, `G` must satisfy the group axioms:
* multiplication in `G` is associative,
* `1` is a 2-sided identity element,
* For every element `x`, the element `x⁻¹`
  is a 2-sided inverse of `x`.

The following code tells lean what it means for `G` to be a group.
Note that `Mul` and `Inv` and `One` are also classes, and
you can see their definition by control-clicking on them.
-/
class MyGroup (G : Type) extends Mul G, Inv G, One G where
  ax_assoc    : ∀ x y z : G, (x * y) * z = x * (y * z)
  ax_mul_one  : ∀ x : G, x * 1 = x
  ax_one_mul  : ∀ x : G, 1 * x = x
  ax_mul_inv  : ∀ x : G, x * x⁻¹ = 1
  ax_inv_mul  : ∀ x : G, x⁻¹ * x = 1

/-
In other words, for any Type `G`,
an element of type `MyGroup G` is a group structure on `G` (ie. multiplication
and inversion maps, the identity element, and proofs of the group axioms.)

Now let's try to build up group theory from those axioms, without
using any of the theorems from Mathlib.
-/
section
    /-
    We begin by telling lean that `G` is a Type, and `G_axioms` is
    a `MyGroup G`, as defined above.
    -/
    variable (G : Type) (G_axioms : MyGroup G) (x y : G)
    /-
    We can use the symbols `1`, `*` and `⁻¹` in the group `G`.
    -/
    #check x * (y⁻¹ * 1)⁻¹ * x
    /-
    Note that `G_axioms` is a variable of type `MyGroup G`.
    This means that we have the following terms:
    -/
    #check G_axioms.ax_assoc
    #check G_axioms.ax_mul_one
    #check G_axioms.ax_one_mul
    #check G_axioms.ax_mul_inv
    #check G_axioms.ax_inv_mul
     /-
    Let's forget what `G` and `G_axioms` are now by ending the section.
    -/
end

/-
There is a potential danger.

Suppose we defined two different group structures on `G`,
by having two terms of type `MyGroup G`.
This would confuse lean, because it would not know (for example)
which multiplication function to use when we type `x * y`.
For this reason, one does *not* define more than one term of
type `MyGroup G`, and one doesn't need to give this variable a name
(because there is only one). Hence it's much more normal to type:
-/
variable {G : Type} [MyGroup G]

/-
We can still access the various parts of the group structure, even though we haven't given it a name.
For example:
-/
#check MyGroup.ax_assoc

namespace MyGroup
/-
By using the `MyGroup` namespace, we can now use the following abbreviarions
for the group axioms:
-/
#check ax_assoc
#check ax_assoc (G := G) -- the associativity axiom for `G`
#check ax_mul_one
#check ax_one_mul
#check ax_inv_mul
#check ax_mul_inv
/-
  We can use these axioms to prove statements about the group `G`.
  Here are a few examples.
-/

lemma assoc_assoc ( w x y z : G) : w * x * y * z = w * (x * (y * z)) :=
by
  rw [ax_assoc,ax_assoc]

lemma inv_eq (x y : G) (h : x * y = 1) : x⁻¹ = y :=
calc
  x⁻¹ = x⁻¹ * 1         := by rw [ax_mul_one]
  _   = x⁻¹ * (x * y)   := by rw [h]
  _   = (x⁻¹ * x) * y   := by rw [ax_assoc]
  _   = 1 * y           := by rw [ax_inv_mul]
  _   = y               := by rw [ax_one_mul]

lemma inv_one : (1 : G)⁻¹ = 1 :=
by
  apply inv_eq
  rw [ax_mul_one]

lemma inv_inv (x : G) : x⁻¹⁻¹ = x :=
by
  apply inv_eq
  apply ax_inv_mul

lemma inv_mul (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
by
  apply inv_eq
  rw [ax_assoc, ←ax_assoc y, ax_mul_inv, ax_one_mul, ax_mul_inv]



open Nat
/-
Currently, the notation `x^n` has no meaning for `x : G` and `n : ℕ`.
We shall define the power notation here recursively. This is first
done by defining a function `pow : G → ℕ → G` representing the power:
-/
def pow (x : G) : ℕ → G
| 0      => 1             -- `pow x 0 := 1`
| n + 1  => x * (pow x n) -- `pow x (n+1) := x * pow x n`
/-
The following line of code allows us to use the notation `x^n` to mean `pow x n`.
-/
instance : Pow G ℕ := ⟨pow⟩
/-
Recall that `pow x 0` is defined to be `1`
and `pow x (n+1)` is defined to be `x * (pow x n)`.
Therefore the next two lemmas can be proved by `rfl`.
-/
lemma pow_zero (x : G) : x ^ 0 = 1 :=
by
  rfl

lemma pow_succ (x : G) : x ^ (n + 1) = x * x^n :=
by
  rfl

/-
The next lemma is not proved by `rfl`,
because we also need to use the group axiom `mygroup.ax_mul_one` in its proof.
-/
lemma pow_one (x : G) : x ^ 1 = x :=
by
  rw [pow_succ, pow_zero, ax_mul_one]

lemma pow_two (x : G) : x ^ 2 = x * x :=
by
  rw [pow_succ, pow_one]

/-
The next lemma should be proved by induction.
-/
lemma pow_add (x : G) (n m : ℕ): x ^ (n + m) = (x ^ n) * (x ^ m) :=
by
  induction n with
  | zero =>
    rw [zero_add, pow_zero, ax_one_mul]
  | succ n ih =>
    rw [succ_add, pow_succ, ih, pow_succ, ax_assoc]

lemma pow_mul_pow_comm (x : G) (n m : ℕ) : x ^ n * x ^ m = x ^ m * x ^ n :=
by
  sorry

lemma pow_mul (x : G) (n m : ℕ) : x ^ (n * m) = (x ^ n) ^ m :=
by
  sorry

lemma inv_pow (x : G) (n : ℕ) : x⁻¹ ^ n = (x ^ n)⁻¹ :=
by
  sorry


/-
Here is a harder example.
-/
lemma my_lemma (x y : G) (h : x * y = y⁻¹ * x) : x^2 * y = y * x^2 :=
by
  sorry


/-
In the next example, prove by `induction`, using `my_lemma`
and the other results proved above for the inductive step.
-/
example (x y : G) (n : ℕ) (h : x * y = y⁻¹ * x) :
  x^(2*n) * y = y * x^(2*n) :=
by
  sorry

end MyGroup
