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
  add _ _         := sorry
  add_assoc _ _ _ := sorry
  zero_add _      := sorry
  add_zero _      := sorry
  neg _           := sorry
  add_left_neg _  := sorry
  add_comm _ _    := sorry


/-
2.  Prove that if `H` is a subgroup of `ZeroGroup` then `H` is isomorphic to `ZeroGroup`.
The notation `A ≃+ B` means the isomorphisms from an additive group `A` to and additive group `B`.
-/
def SubgroupOfZeroGroupEquivZeroGroup (H : AddSubgroup ZeroGroup) : H ≃+ ZeroGroup where
  toFun _       := sorry
  invFun _      := sorry
  left_inv _    := sorry
  right_inv _   := sorry
  map_add' _ _  := sorry


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
    toFun     := fun ⟨a,c⟩ => sorry -- the function from `A × C` to `B × C`.
    invFun    := fun ⟨b,c⟩ => sorry -- the inverse function.
    left_inv  := sorry --prove that one is a left inverse of the other
    right_inv := sorry --prove that one is a right inverse of the other
    map_add'  := sorry --prove that the function is a homomorphism.



/-
4.  Prove that if `H` is a subgroup of `G` and `G'` is isomorphic to `G`
then there is a subgroup `H'` of `G'` which is isomorphic to `H`.

*Now might be a good time to reread the warning above.*
-/
lemma Subgroup_equiv [AddCommGroup G] [AddCommGroup G'] (Φ : G ≃+ G')
  (H : AddSubgroup G) : ∃ H' : AddSubgroup G', Nonempty (H ≃+ H') :=
by
  --We'll first define an appropriate subgroup `H'` of `G'`
  let H' : AddSubgroup G' := {
    carrier := {h' | Φ.symm h' ∈ H} -- The elements of `H'` are those whose pre-image is in `H`.
    add_mem' := sorry
    zero_mem' := sorry
    neg_mem' := sorry
  }
  use H'
  /-We next define an isomorphism between `H` and `H'`.-/
  constructor
  exact {
    toFun := by
      intro ⟨g,hg⟩ -- you are introducing al element of the subtype `{x // x ∈ H}`.
      -- such an element is a pair `⟨g,hg⟩` where `g : G` and `hg` is a proof that `g ∈ H`.
      -- You may want to filter the infoview, so that it does not display all of the let-values.
      sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
    map_add' := sorry
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
  -- Prove this by induction.
  sorry





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
    /-
    By definition, a free abelian group is constructed as either the zero group,
    or `G × ℤ`, where `G` is a free abelian group, or `G'`, where `G' ≃+ G` and `G`
    is a free abelian group. That's why the folloing kind of induction works.
    -/
    induction hG with
    | zero => sorry
    | step G _ ih => sorry
    | isomorphism G G' _ hGH ih => sorry
  · sorry



/-
7.  Prove that if there is a surjective homomorphism `φ : G →+ ℤ` then
`G` is isomorphic to `φ.ker × ℤ`.
-/
lemma equiv_prod_of_ontoInt [AddCommGroup G] (φ : G →+ ℤ) (hφ : Function.Surjective (φ : G → ℤ)) :
  φ.ker × ℤ ≃+ G :=
by
  /-
  Since `φ` is surjective, there must be an element `g : G` such that `φ g = 1`.
  Define a function ker × ℤ → G which takes (x,n) to x + n • g. This has an inverse
  which takes x to (x - (φ x) • g, φ x).

  Prove that these functions are mutually inverse homomorphisms.
  -/
  sorry
