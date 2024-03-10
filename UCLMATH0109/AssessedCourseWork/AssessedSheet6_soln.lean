import Mathlib
/-

# Notation

This assessment sheet is about additive commutative groups. These are commutative groups
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

We shall also use the notation `Nonempty A`, which means that there is
an element of type `A`. For example, `Nonempty (A ≃+ B)` means that `A` and `B` are isomorphic.
`Nonempty A` is a structure whose only field is an element `val` of type `A`.


# Warning

One thing to be aware of is that if `A` is an additive subgroup of `B`,
then `φ : A →+ C` is a homomorphism from `↑A = (A : Type)` to `C`. Here `↑A` is
a subtype of `B`. Elements of `↑A` are pairs `⟨b,hbA⟩` where `b : B` and `hb`
is a proof that `b ∈ A`.
-/



/-
ZeroGroup is a Type with one element `ZeroGroup.zero`.
-/
inductive ZeroGroup : Type
| zero : ZeroGroup

/-
We'd like to write `0` instead of `ZeroGroup.zero`.
-/
instance : Zero ZeroGroup where
  zero := ZeroGroup.zero


/-
1.  Make `ZeroGroup` into an additive commutative group.
This is done by defining `0 + 0 = 0` and `- 0 = 0`, and checking all of the axioms.
-/
instance : AddCommGroup ZeroGroup where
  add _ _         := 0
  add_assoc _ _ _ := rfl
  zero_add _      := rfl
  add_zero _      := rfl
  neg _           := 0
  add_left_neg _  := rfl
  add_comm _ _    := rfl


/-
2.  Prove that if `H` is a subgroup of `ZeroGroup` then `H` is isomorphic to `ZeroGroup`.
The notation `A ≃+ B` means the isomorphisms from an additive group `A` to and additive group `B`.
-/
def SubgroupOfZeroGroupEquivZeroGroup (H : AddSubgroup ZeroGroup) : H ≃+ ZeroGroup where
  toFun _       := 0
  invFun _      := 0
  left_inv _    := rfl
  right_inv _   := rfl
  map_add' _ _  := rfl


/-
For a type `α`, we define `α ^ n`
to mean the group `ZeroGroup × α × α × ... × α`.
-/
def Type.pow (α : Type) : ℕ → Type
| 0     => ZeroGroup
| n + 1 => Type.pow α n × α
instance : Pow Type ℕ where
  pow := Type.pow

/-
Here are some definitional lemmas describing `α ^ n`.
We have marked these as `simp` lemmas, so that `simp` will
automatically apply them.
-/
@[simp] lemma Type_pow_zero : α ^ 0 = ZeroGroup := rfl
@[simp] lemma Type_pow_succ {α : Type} : α ^ (n + 1) = ((α ^ n) × α) := rfl



/-
If `G` is an additive commutative group, then so is `G ^ n`.
-/
instance (G : Type) [AddCommGroup G] (n : ℕ) : AddCommGroup (G ^ n) :=
by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, Type_pow_zero]
    infer_instance
  | succ n ih =>
    simp only [Type_pow_succ]
    infer_instance

@[simp]
def AddCommGroup_pow_zero [AddCommGroup G] : G ^ 0 ≃+ ZeroGroup :=
by
  rfl

@[simp]
def AddCommGroup_pow_succ [AddCommGroup G] : G ^ (n+1) ≃+ (G ^ n) × G :=
by
  rfl

/-
3.  Prove that if `A` is isomorphic to `B` then `A × C` is isomorphic to `B × C`.
-/
def prod_equiv_prod_left (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (hAB : A ≃+ B) : A × C ≃+ B × C where
    toFun     := fun ⟨a,c⟩ => ⟨hAB a, c ⟩
    invFun    := fun ⟨b,c⟩ => ⟨hAB.invFun b, c⟩
    left_inv  := by intro; simp
    right_inv := by intro; simp
    map_add'  := by simp



/-
4.  Prove that if `H` is a subgroup of `G` and `G'` is isomorphic to `G`
then there is a subgroup `H'` of `G'` which is isomorphic to `H`.

*Now might be a good time to reread the warning above.*
-/
lemma Subgroup_equiv [AddCommGroup G] [AddCommGroup G'] (Φ : G ≃+ G')
  (H : AddSubgroup G) : ∃ H' : AddSubgroup G', Nonempty (H ≃+ H') :=
by
  let H' : AddSubgroup G' := {
    carrier := {h' | Φ.symm h' ∈ H}
    add_mem' := by
      intro _ _ hx hy
      dsimp at hx hy
      simp [add_mem hx hy]
    zero_mem' := by
      simp [zero_mem]
    neg_mem' := by
      intro _ hx
      dsimp
      rw [map_neg]
      apply neg_mem hx
  }
  use H'
  constructor
  exact {
    toFun     := fun ⟨g,hg⟩ ↦ ⟨Φ g, by simp [hg]⟩
    invFun    := fun ⟨_,hg'⟩ ↦ ⟨_,hg'⟩
    left_inv  := by intro; simp
    right_inv := by intro; simp
    map_add'  := by intros; simp
  }




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
| zero : FreeAbGroup ZeroGroup
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
5. Prove that `ℤ ^ n` is a free abelian group.
-/
theorem FreeAbGroup_Int_pow {n : ℕ} : FreeAbGroup (ℤ ^ n) :=
by
  induction n with
  | zero      => exact FreeAbGroup.zero
  | succ _ ih => dsimp; exact FreeAbGroup.step _ ih





/-
# Notation

The notation `Nonempty A` means that th Type `A` has an element / term.
For example, `Nonempty (G ≃+ H)` means that there is an isomorphism from `G` to `H`,
i.e. `G` and `H` are isomorphic.

To see how to use this notation, have a quick look at the following example.
-/
example (hA : Nonempty A) (f : A → B) : Nonempty B :=
by
  obtain ⟨a⟩ := hA
  exact ⟨f a⟩


/-
6.  Prove that `G` is a free abelian group if and only
if `G` is isomorphic to `ℤ^n`.
-/
theorem FreeAbGroupIff [AddCommGroup G] :
  FreeAbGroup G ↔ ∃ n:ℕ, Nonempty (G ≃+ ℤ ^ n) :=
by
  constructor
  · intro hG
    induction hG with
    | zero =>
      use 0
      dsimp
      exact ⟨1⟩
    | step G _ ih =>
      obtain ⟨n,⟨φ⟩⟩ := ih
      use n+1
      dsimp
      exact ⟨prod_equiv_prod_left _ _ _ φ⟩
    | isomorphism G G' _ hGH ih =>
      obtain ⟨n,⟨φ⟩⟩ := ih
      use n
      exact ⟨AddEquiv.trans hGH.symm φ⟩
  · intro h
    obtain ⟨_,⟨φ⟩⟩ := h
    apply FreeAbGroup.isomorphism (hGH := φ.symm)
    exact FreeAbGroup_Int_pow



/-
7.  Prove that if there is a surjective homomorphism `φ : G →+ ℤ` then
`G` is isomorphic to `φ.ker × ℤ`.
-/
lemma equiv_prod_of_ontoInt [AddCommGroup G] (φ : G →+ ℤ) (hφ : Function.Surjective (φ : G → ℤ)) :
  φ.ker × ℤ ≃+ G :=
by
  specialize hφ 1
  set g := hφ.choose with g_def
  have g_spec := hφ.choose_spec
  exact {
    toFun := fun ⟨x,n⟩ ↦ x + n • g
    invFun := fun x ↦ ⟨⟨x - φ x • g, by simp [AddMonoidHom.mem_ker, g_spec]⟩, φ x⟩
    left_inv := by
      intro ⟨⟨_,h⟩,_⟩
      rw [AddMonoidHom.mem_ker] at h
      dsimp
      ext <;>
      · simp [g_spec, h]
    right_inv := by intro; simp
    map_add' := by
      intros
      dsimp
      rw [←g_def, add_zsmul, add_assoc, add_assoc]
      congr 1
      rw [add_comm, add_assoc]
      congr 1
      apply add_comm
  }
