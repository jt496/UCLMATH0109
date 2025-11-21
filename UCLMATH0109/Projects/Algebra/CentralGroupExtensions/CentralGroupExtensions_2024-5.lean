import Mathlib

/-
# This project is a topic in group theory

Let `G` and `K` be groups with `K` abelian.
A 2-cocycle on `G` with values in `K` is a function

  `σ : G → G → K`

satisfying the following relation for all `x,y,z : G`:

  `(σ x y) * (σ (x * y) z) = (σ x (y * z)) * (σ y z)`.
-/

variable (G K : Type) [Group G] [CommGroup K]

@[ext] structure Cocycle where
  toFun : G → G → K
  relation : ∀ x y z : G, toFun x y * toFun (x*y) z = toFun x (y*z) * toFun y z

instance : CoeFun (Cocycle G K) (fun _ ↦ (G → G → K)) where
  coe σ := σ.toFun

instance : CommGroup (Cocycle G K) where
  one := {
    toFun     := 1
    relation  := sorry
  }
  inv σ := {
    toFun     := fun x ↦ (σ x)⁻¹
    relation  := sorry
  }
  mul σ₁ σ₂ := {
    toFun     := σ₁ * σ₂
    relation  := sorry
  }
  mul_assoc     := sorry
  mul_one       := sorry
  one_mul       := sorry
  mul_comm      := sorry
  mul_left_inv  := sorry




section Cocycle_to_CoveringGroup
/-
Given a 2-cocycle `σ`, we can construct another group called the
"covering group", whose elements are pairs `(g,k)` with `g : G` and `k : K`,
where multiplication is given by

  `(g₁,k₁) * (g₂,k₂) = (g₁ * g₂, k₁ * k₂ * (σ g₁ g₂))`.

# Prove that this is a group.
-/
variable {G K}
@[ext] structure CoveringGroup (σ : Cocycle G K) where
  g : G
  k : K

notation "G_[" σ "]"  => CoveringGroup σ

variable {σ : Cocycle G K}

/-
Prove that `CoveringGroup σ` is a group, with the multiplication defined using the cocycle.
-/
instance : Group G_[σ] where
  mul a b := {
    g := a.g * b.g
    k := a.k * b.k * σ a.g b.g
  }
  one           := sorry
  inv           := sorry
  mul_assoc     := sorry
  mul_left_inv  := sorry
  mul_one       := sorry
  one_mul       := sorry






/-
Define a group homomorphism from the covering group to `G`, which takes
`(g,k)` to `g`.

# Prove that this function is a surjective group homomorphism.
# Prove that the kernel of this homomorphism is isomorphic to `K`.
-/
variable (σ)

def π : G_[σ] →* G := sorry

lemma surjective_pi : Function.Surjective (π σ) := by sorry

def ι : K ≃* (π σ).ker := sorry

lemma ker_π_le_centre : (π σ).ker ≤ Subgroup.center G_[σ] := sorry


/-
Prove that the cocycle corresponding to the cocycle `1` is isomorphic to the product `G × K`.
-/
def CoveringGroup_equiv_prod : G_[(1 : Cocycle G K)] ≃* G × K := sorry


end Cocycle_to_CoveringGroup




section CoveringGroup_to_cocycle

/-
Assume in this section that we have a surjective homomorphism from `G'` to `G`,
whose kernel is isomorphic to `K`.
We shall construct a corresponding cocycle `σ` and an isomorphism `G' ≃* G_[σ]`.
-/
variable [Group G'] (φ : G' →* G) (hφ : Function.Surjective φ) (hφ' : φ.ker ≤ Subgroup.center G')
variable {G}

instance : CommGroup φ.ker := sorry

noncomputable def s : G → G' := Function.invFun φ

lemma φ_comp_s : φ ∘ s φ  = id := sorry

/-
Construct a cocycle corresponding to the covering group `φ : G' →* G`.
-/
noncomputable
def σ : Cocycle G φ.ker where
  toFun x y := {
    val       := (s φ x) * (s φ y) * (s φ (x * y))⁻¹
    property  := sorry
  }
  relation := sorry

/-
Prove that `G'` is isomprphic to `G_[σ φ]`.
-/
def G'_equiv_G_σ : G' ≃* G_[σ φ] := sorry

end CoveringGroup_to_cocycle




section Coboundary

variable {G K}
/-
Given any function `τ : G → K`, we define a new function `∂ τ : G → G → K` by

  `∂ τ g h = (τ h) * (τ g)⁻¹`.

The function `∂ τ` is called the coboundary of `τ`.

Prove that `∂ τ` is a 2-cocycle.
-/
def coboundary (τ : G → K) : Cocycle G K where
  toFun g h := τ g * τ h * τ (g * h)⁻¹
  relation := sorry

notation "∂" => coboundary

/-
Prove that the cocycles `σ` and `σ * ∂ τ` have isomorphic covering groups.
-/

def coveringGroup_equiv (σ : Cocycle G K) (τ : G → K) :
    G_[σ * ∂ τ] ≃* G_[σ] := sorry


end Coboundary



/-
Give an example of a cocycle which is not a coboundary, as described in the pdf.
-/
