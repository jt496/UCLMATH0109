import Mathlib.Tactic --# do not change this line

section Automorphisms_of_G
/-
An automorphism of a group `G` is a bijective homomorphism from `G` to `G`.

We prove that for any group `G`, the automorphisms of `G` form a group
with the operation of composition. We shall write `Aut G` for the group of
automorphisms of `G`.

Given an element `x : G`, we show that the function

  `g ↦ x * g * x⁻¹`

is an automorphism of `G`. Automorphisms of this kind are called
*inner automorphisms*.
We shall write `inn x` for the inner automorphism given by the element `x:G`.

We also prove that the function `inn : G → Aut G` is a group homomorphism,
and that the set of all inner automorphisms is a normal subgroup of `Aut G`.
-/


def Aut (G : Type) [Group G] := G ≃* G

variable [Group G] -- for the rest of this section, G will be a group.

namespace Aut

/-
An automorphism `φ` is defined to be 5 things:
  `φ.toFun : G → G`
  `φ.invFun : G → G`
  `φ.left_inv` : a proof that `φ.inv_fun` is a left inverse of `φ.toFun`
  `φ.right_inv` : a proof that `φ.inv_fun` is a right inverse of `φ.toFun`
  `φ.map_mul` : a proof that `φ.toFun` is a group homomorphism.
Here is an example of how to write down an automorphism:
-/
def one : Aut G := sorry
instance : One (Aut G) := ⟨one⟩

/-
If `φ` is an automorphism, then we will often want to write `φ` for
the function `φ.toFun`. In particular, this will allow us to write `φ g`
for an element `g : G`. The next two lines of code allow this notation,
i.e. they allow lean to coerce `φ` to the function `φ.toFun`.
-/
instance : CoeFun (Aut G) ( λ _ ↦ G → G ) where
  coe := fun φ ↦ φ.toFun

/-
Show that two elements of the `Aut G` are equal if their underlying functions are equal.
-/
@[ext]
lemma eq (φ ψ : Aut G)  (h : φ.toFun = ψ.toFun ) :
  φ=ψ := sorry

/-
Define the inverse of an element `f : Aut G`.
-/
def inv (f : Aut G) : Aut G := sorry
instance : Inv (Aut G) := ⟨inv⟩

/-
Define the product of two elements to `Aut G`.
-/
def mul (f g : Aut G) : Aut G := sorry

lemma mul_left_inv (a : Aut G) :
  mul (inv a) a = one := sorry

instance : Group (Aut G) := sorry

@[simp]
theorem one_defn (x : G) : (1 : Aut G) x = x := sorry

@[simp]
theorem mul_defn (f g : Aut G) (x : G) :
  (f * g) x = f (g x) := sorry


/-
For example for any `x : G`, there is an automorphism
`inn x : G ≃* G` given by the map `g ↦ x * g * x⁻¹`. This kind
of automorphism is called an *inner automorphism* of `G`.

Prove that `inn x` is an automorphism of `G`, and also that
the map `inn : G → Aut G` is a group homomorphism.
-/

def inn : G →* Aut G := sorry




/-
We'll write `Inn G` for the set of inner automorphisms of `G`.
Prove that `Inn G` is a subgroup of `Aut G`.
-/

def Inn (G : Type) [Group G] : Subgroup (Aut G) := sorry

/-
In fact, you can even show the the subgroup of inner automorphisms is
a Normal subgroup.
-/

lemma Normal_Inn : Subgroup.Normal (Inn G) := sorry

end Aut

end Automorphisms_of_G


section SemiDirectProduct

/-
In this section we introduce semi-direct products of `G` and `H`.
An element of the semi-direct product `G ⋊ H` has the form `⟨g,h⟩`,
with `g : G` and `h : H`. Multiplication in the semi-direct product
is defined by

  `⟨g,h⟩ * ⟨g',h'⟩ = ⟨g* φ(h) (g'), h*h'⟩`,

where `φ: H →* Aut G` is a specified homomorphism. We prove that the
semi-direct product is a group.

After this, we define an equivalence relation on the set `H →* Aut G`
in which `φ ≈ ψ` if and only if there is an automorphism `p : Aut H`
such that `φ = ψ ∘ p`. We prove that if `φ ≈ ψ` then the resulting
semidirect products are isomorphic.
-/

variable [Group G] [Group H]

@[ext]
structure SemiDirectProduct (φ : H →* Aut G) where
  g : G
  h : H

namespace SemiDirectProduct

notation G" ⋊["φ"] " H => SemiDirectProduct (G :=G) (H := H) φ

def mul (a b : G ⋊[φ] H) : G ⋊[φ]H :=
  ⟨a.g * (φ a.h) b.g, a.h * b.h⟩

/-
The identity element in the semi-direct product.
-/
def one {φ : H →* Aut G} : G ⋊[φ]H := sorry

/-
The inverse of an element of the semi-direct product.
-/
def inv {φ : H →* Aut G} (a : G ⋊[φ]H) : G ⋊[φ]H := sorry

instance : Mul (G ⋊[φ]H) := ⟨mul⟩
instance : Inv (G ⋊[φ]H) := ⟨inv⟩
instance : One (G ⋊[φ]H) := ⟨one⟩


variable {φ : H →* Aut G} (a b c : G ⋊[φ]H)

/-
State and prove some definitional lemmas.
-/
@[simp]
theorem mul_defn : a * b = sorry := sorry

@[simp]
theorem inv_defn : a⁻¹ = sorry := sorry

@[simp]
theorem one_defn : (1 : G ⋊[φ]H) = sorry := sorry


/-
Next, show that the semi-direct product is a group.
-/
theorem mul_assoc : a * b * c = a * (b * c) := sorry

theorem mul_one : a * 1 = a := by sorry

theorem one_mul : 1 * a = a := by sorry

theorem mul_left_inv : a⁻¹ * a = 1 := by sorry

instance : Group (G ⋊[φ]H) := sorry


/-We'll call tw homomorphisms `φ,ψ : H →* Aut G` equivalent if
  `φ` is the composition of `ψ` with an automorphism of `H`.-/

def equiv (φ ψ : H →* Aut G) : Prop :=
  ∃ p : Aut H, φ = ψ ∘ p

/-
Prove that `equiv` is an equivalence relation.
-/
instance : Setoid  ( H →* Aut G) where
  r := equiv
  iseqv := sorry


/-
Prove that if `φ ≈ ψ`
then the resulting semi-direct products are isomorphic.
-/
example (h : φ ≈ ψ) : Nonempty ( (G ⋊[φ]H) ≃* (G ⋊[ψ] H)) := sorry


end SemiDirectProduct -- end the namespace
end SemiDirectProduct -- end the section.
