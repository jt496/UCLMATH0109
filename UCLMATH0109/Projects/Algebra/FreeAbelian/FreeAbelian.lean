import Mathlib
namespace FreeAbelian
/-

This project is about additive commutative groups. These are commutative groups
with the operation `+`. The inverse of an element `x` is written `-x`, and the identity element
ia written `0`.

If `A` and `B` are additive commutative groups, then Mathlib already knows that `A × B`
is an additive commutative group with elements `⟨a,b⟩` for `a : A` and `b : B`. The group operation
is `⟨a,b⟩ + ⟨a',b'⟩ = ⟨a+a', b+b'⟩`.

The notation `φ : A →+ B` means that `φ` is a homomorphism from `A` to `B`.
Similarly, `φ : A ≃+ B` is an isomorphism (i.e. a homomorphism with a 2-sided inverse).
Both types `A →+ B` and `A ≃+ B` are structures. For example `A →+ B` has three fields:
* `toFun`     -- a function from `A` to `B`,
* `map_add'`  -- a proof that `toFun (a + b) = toFun a + toFun b`,
* `map_zero'` -- a proof that `toFun 0 = 0`.
-/

/-
For a type `α`, we define `α ^ n` to mean the group `α × α × ... × α`.
-/
def Type.pow (α : Type) : ℕ → Type
| 0     => Unit
| n + 1 => Type.pow α n × α
instance : Pow Type ℕ where
  pow := Type.pow

/-
Here are some definitional lemmas describing `α ^ n`.
We have marked these as `simp` lemmas, so that `simp` will
automatically apply them.
-/
@[simp] lemma Type_pow_zero : α ^ 0 = Unit := rfl

@[simp] lemma Type_pow_succ {α : Type} : α ^ (n + 1) = ((α ^ n) × α) := rfl



/-
If `G` is an additive commutative group, then so is `G ^ n`.
-/
instance (G : Type) [AddCommGroup G] (n : ℕ) : AddCommGroup (G ^ n) := by
  induction n with
  | zero      => exact inferInstanceAs (AddCommGroup Unit)
  | succ n ih => exact inferInstanceAs (AddCommGroup (G ^ n × G))

@[simp]
def AddCommGroup_pow_zero [AddCommGroup G] : G ^ 0 ≃+ Unit :=
by
  rfl

@[simp]
def AddCommGroup_pow_succ [AddCommGroup G] : G ^ (n+1) ≃+ (G ^ n) × G :=
by
  rfl

/-
We now define the concept of a free abelian group.
The rules for this are as follows:
* `ZeroGroup` is a free abelian group.
* if `G` is a free abelian group then `G × ℤ` is a free abelian group.
* if `G` is a free abelian group and `G'` is isomorphic to `G` then `G'` is a free
  abelian group.
-/
inductive FreeAbGroup : ∀ (G : Type) [AddCommGroup G] , Prop
-- the zero group is a free abelian group
| zero : FreeAbGroup Unit
-- if `G` is a free abelian group then `G × ℤ` is a free abelian group.
| step (G : Type) [AddCommGroup G] (hG : FreeAbGroup G) : FreeAbGroup (G × ℤ)
-- if `G'` is isomorphic to a free abelian group `G` then `G'` is a free abelian group.
| isomorphism (G G' : Type) [AddCommGroup G] [AddCommGroup G']
    (hG : FreeAbGroup G) (hGH : G ≃+ G') : FreeAbGroup G'

-- You can use the following three functions to prove that something is a free abelian group.
#check FreeAbGroup.zero
#check FreeAbGroup.step
#check FreeAbGroup.isomorphism



/-
Prove that `ℤ ^ n` is a free abelian group.
-/
theorem FreeAbGroup_Int_pow {n : ℕ} : FreeAbGroup (ℤ ^ n) :=
by
  sorry
  
/-
Prove that `G` is a free abelian group if and only
if `G` is isomorphic to `ℤ^n`.
-/
theorem FreeAbGroupIff [AddCommGroup G] :
  FreeAbGroup G ↔ ∃ n:ℕ, Nonempty (G ≃+ ℤ ^ n) :=
by
  sorry



/-
Prove that if there is a surjective homomorphism `φ : G →+ ℤ` then
`G` is isomorphic to `φ.ker × ℤ`.
-/
def equiv_prod_of_ontoInt [AddCommGroup G] (φ : G →+ ℤ) (hφ : Function.Surjective (φ : G → ℤ)) :
  φ.ker × ℤ ≃+ G :=
by
  /-
  Since `φ` is surjective, there must be an element `g : G` such that `φ g = 1`.
  Define a function ker × ℤ → G which takes (x,n) to x + n • g. This has an inverse
  which takes x to (x - (φ x) • g, φ x).

  Prove that these functions are mutually inverse homomorphisms.
  -/
  sorry


/-
Prove that every non-zero subgroup of `ℤ` is isomorphic to `ℤ`.
The symbol `⊥` means the zero subgroup.
-/
open Classical
def AddSubgroupIntEquivInt (H : AddSubgroup ℤ) (hH : H ≠ ⊥) :
  H ≃+ ℤ :=
by
  sorry



/-
Prove that every subgroup of a free abelian group is a free abelian group.
-/
theorem FreeAbSubgroupOfFreeAbGroup {G : Type} [AddCommGroup G] (hG : FreeAbGroup G) (H : AddSubgroup G) :
  FreeAbGroup H :=
by
  sorry


end FreeAbelian
