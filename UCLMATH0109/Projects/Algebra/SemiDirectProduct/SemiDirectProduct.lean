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

@[ext]
structure Aut (G : Type) [Group G] where
  homomorphism : G →* G
  bijective    : homomorphism.toFun.Bijective

variable [Group G] -- for the rest of this section, `G` will be a group.

instance : CoeFun (Aut G) (fun _ ↦ G → G) where
  coe f := f.homomorphism.toFun

/-
Make `Aut G` into a group. The group operation should be composition of automorphisms.
The hardest part is to prove that an automorphism has an inverse
-/
instance : Group (Aut G) := sorry

/-
In Mathlib, the group of automorphisms of `G` is defined in a slightly different way,
and is written `G ≃* G`.
Prove that these `Aut G` and `G ≃* G` are isomorphic:
-/

def Aut_equiv : Aut G ≃* (G ≃* G) := sorry

namespace Aut

@[simp]
theorem one_apply (x : G) : (1 : Aut G) x = x := sorry

@[simp]
theorem mul_apply (f g : Aut G) (x : G) :
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
We'll write `Inn G` for the subgroup of inner automorphisms of `G`.
-/
def Inn (G : Type) [Group G] : Subgroup (Aut G) := inn.range

/-
Show the the subgroup of inner automorphisms is
a Normal subgroup.
-/

instance : (Inn G).Normal := sorry

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

notation G " ⋊["φ"] " H => SemiDirectProduct (G :=G) (H := H) φ

instance : Group (G ⋊[φ] H) where
  mul a b := ⟨a.g * (φ a.h) b.g, a.h * b.h⟩
  one := sorry
  inv := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  mul_left_inv := sorry





/-We'll call two homomorphisms `φ,ψ : H →* Aut G` equivalent if
  `φ` is the composition of `ψ` with an automorphism of `H`.-/

def equiv (φ ψ : H →* Aut G) : Prop :=
  ∃ p : Aut H, φ = ψ ∘ p

/-
Prove that `equiv` is an equivalence relation.
-/
instance : Setoid  (H →* Aut G) where
  r := equiv
  iseqv := sorry


/-
Prove that if `φ ≈ ψ` then the resulting semi-direct products are isomorphic.
-/
def SemiDirectProduct_equiv (h : φ ≈ ψ) : (G ⋊[φ] H) ≃* (G ⋊[ψ] H) := sorry


end SemiDirectProduct

/-
Define the cyclic group `Cyclic n` for any `n : ℕ`.
-/

notation3 "Cyclic " n => Multiplicative (ZMod n)

/--
`gen` is the generator of `Cyclic n`.
-/
def gen : Cyclic n := Multiplicative.ofAdd 1



/-
Next, list the homomorphisms from `Cyclic 2` to `Aut (Cyclic 5)`. There are two of these.
Show that these are not equivalent. Show that one of the semi-direct products
is isomorphic to `Cyclic 10` and the other is isomorphic to `DihedralGroup 5`.
-/



end SemiDirectProduct
