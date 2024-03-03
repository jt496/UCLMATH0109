import Mathlib

/-
# This project is a topic in group theory

Show how central extensions may be defined using 2-cocycles.
Prove that cohomologous cocycles give rise to isomorphic group extensions.
-/


/-
Definition of a cocycle.
-/
@[ext] structure Cocycle (G K : Type) [Group G] [CommGroup K] where
  toFun : G → G → K
  relation : ∀ x y z : G, toFun x y * toFun (x*y) z = toFun x (y*z) * toFun y z

/-
Given a cocycle, we define a new structure `CoveringGroup`.
-/
@[ext] structure CoveringGroup [Group G] [CommGroup K] (σ : Cocycle G K) where
  g : G
  k : K

namespace CoveringGroup

variable {G K : Type} [Group G] [CommGroup K] {σ : Cocycle G K}

/-
definition of multiplication in `CoveringGroup`.
-/
def mul (a b : CoveringGroup σ) : CoveringGroup σ where
  g := a.g * b.g
  k := a.k * b.k * σ.toFun a.g b.g

/-
Prove that `CoveringGroup σ` is a group.
-/
instance : Group (CoveringGroup σ) := sorry

variable (σ)

/-
Define the homomorphism taking `⟨g,k⟩` to `g`.
-/
def π : CoveringGroup σ →* G := sorry

lemma surjective_pi : Function.Surjective (π σ) := by sorry

def ι : K ≃* (π σ).ker := sorry

/-
Definition of a coboundary.
-/
def coboundary (τ : G → K) : Cocycle G K where
  toFun g h := τ g * τ h * τ (g * h)⁻¹
  relation := sorry

/-
Prove that the covering group corresponding to a coboundary is
isomorphic to the direct sum.
-/
def coveringGroup_of_coboundary (τ : G → K) :
    CoveringGroup (coboundary τ) ≃* G × K := sorry

/-
# Further suggestions

Construct a cocycle on SL₂(ℝ) with values in `{1,-1}` (ask for the formula)
and prove that this cocycle is not a coboundary.

Show that `coboundary` is a group homomorphism, and define `Coboundary G K` to be
its image.

Prove that if `σ` and `σ'` are in the same coset
of `Coboundary G K`, then the corresponding covering groups are isomorphic.

Conversely, prove that if there is an isomorphism between
`CoveringGroup σ` and `CoveringGroup σ'`, which is compatible with the
maps `π σ` and `π σ'`, then there is a `τ : G → K`,
such that `σ' = σ * coboundary τ`.
-/
