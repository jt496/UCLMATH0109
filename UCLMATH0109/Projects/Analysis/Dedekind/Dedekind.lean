import Mathlib.Tactic

/-

A `Dedekind cut` is a partition of the rationals `(A , Aᶜ)` such that both A and Aᶜ are
nonempty with the following properties:

1)  A is a down-set: if x < y and y ∈ A then x ∈ A;

2)  A has no maximum element: if x ∈ A there exists y ∈ A with x < y.

One way of constructing the real numbers from ℚ is as Dedekind cuts.

We identify a real number `r` with the cut `(A, Aᶜ)` where `A = {x ∈ ℚ | x < r}`

In this project we explore some of the properties of this construction including:
Addition; Embedding of rationals; Linear ordering; Archimedean property;
Dense ordering; Lattice structure; Completeness; Subtraction; Negation; Absolute value
-/
/--
Dedekind cut
-/
@[ext] -- two Dedekind cuts D = E iff D.A = E.A
structure Dedekind
 where
  A         : Set ℚ
  nonempty  : A.Nonempty
  nonempty'  : Aᶜ.Nonempty
  down      : ∀ ⦃x y⦄, x < y → y ∈ A → x ∈ A
  no_max    : ∀ ⦃x⦄, x ∈ A → ∃ y ∈ A, x < y

namespace Dedekind
notation "𝔻" => Dedekind


section basics

variable {D : 𝔻}
variable {x y : ℚ}

/-- If `D = (A , Aᶜ)` is a Dedekind cut with `x ∈ A` and `y ∈ Aᶜ` then `x < y`-/
lemma lt_of_cut (hx : x ∈ D.A) (hy : y ∈ D.Aᶜ) : x < y :=
by
  sorry

/-- If `D = (A, Aᶜ)` is a Dedekind cut then `Aᶜ` is an `up-set` -/
lemma up  : ∀ ⦃x y⦄, x < y → x ∈ D.Aᶜ → y ∈ D.Aᶜ :=
by
  sorry

#check D.A         -- D.A : Set ℚ
#check D.nonempty  -- D.nonempty : Set.Nonempty D.A
#check D.nonempty' -- D.nonempty' : Set.Nonempty D.Aᶜ
#check D.down      -- D.down : ∀ ⦃x y : ℚ⦄, x < y → y ∈ D.A → x ∈ D.A
#check D.no_max    -- D.no_max : ∀ ⦃x : ℚ⦄, x ∈ D.A → ∃ y, y ∈ D.A ∧ x < y


end basics

section order


/-- We can order Dedekind cuts with `D ≤ E` iff `D.A ⊆ E.A` -/
instance : LE 𝔻 where
le := fun D E => D.A ⊆ E.A

/-- We can define `<` on Dedekind cuts by `D < E` iff `D ≤ E` and `D ≠ E`-/
instance : LT 𝔻 where
lt := fun D E => D ≤ E ∧ ¬ E ≤ D

variable {D E : 𝔻}
lemma le' : D ≤ E ↔ D.A ⊆ E.A :=
by
  sorry

/-- `D < E` iff `D.A` is a proper-subset of `E.A` -/
lemma lt' : D < E ↔  D.A ⊂ E.A :=
by
  sorry

/-- So D < E iff ∃ x ∈ E.A \ D.A-/
lemma lt_iff_exists : D < E ↔ ∃ x, x ∈ E.A \ D.A:=
by
  sorry

/-
`≤` and `<` on Dedekind cuts define a `LinearOrder`.

First we establish that this is a `Preorder`.

This extends the instances of ≤ and < that we have already provided.

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a


-/
instance : Preorder 𝔻 where
le_refl := sorry
le_trans := sorry

/-
Next we prove that we have a `PartialOrder`.

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
-/
instance : PartialOrder 𝔻 where
le_antisymm := sorry

/-
Given two Dedekind cuts D and E there is no algorithm for deciding whether `D ≤ E`.

However Lean likes things to be decidable and so in this case we need to use the
`classical` tactic that allows us to pretend that any proposition is decidable.
Notice that we marked this instance `noncomputable` for precisely this reason.
-/

noncomputable
instance decidableLE : DecidableRel (fun (D : 𝔻) (E : 𝔻) => D ≤ E):=
by
  classical
  infer_instance

/-
Finally we prove that it is a `LinearOrder`
-/

noncomputable -- this is noncomputable since it uses `decidableLE` which is noncomputable
instance : LinearOrder 𝔻 where
le_total := sorry

decidableLE := decidableLE

end order


section rationals

/--
𝔻 contains a copy of the rational numbers given by the embedding `rat`
-/
def rat (q : ℚ): 𝔻 :=
by
  use {x : ℚ | x < q}
  · sorry
  · sorry
  · sorry
  · sorry


@[simp]
lemma rat' (q : ℚ) : (rat q).A = {x : ℚ | x < q} :=
by
  sorry

/-- The map `rat` is an order embedding: i.e. it is injective and `rat p ≤ rat q ↔ p ≤ q`-/
def Rat : ℚ ↪o 𝔻 where
toFun := rat
inj' :=
by
  sorry
map_rel_iff' :=
by
  sorry


end rationals


section addition

instance : Add 𝔻 where
add :=
by
  intro D E
  use {x | ∃ d ∈ D.A, ∃ e ∈ E.A,  x = d + e}
  · sorry
  · sorry
  · sorry
  · sorry


variable (D E : 𝔻) (q : ℚ)

@[simp]
lemma add'  : (D + E).A = {x | ∃ d ∈ D.A, ∃ e ∈ E.A, x = d + e}:=
by
  sorry

@[simp]
lemma add_rat : (D + rat q).A = {x |  ∃ d ∈ D.A, ∃ y < q, x = d + y  }:=
by
  sorry

instance : Zero 𝔻 where
zero := rat 0

@[simp]
lemma zero' : 0 = rat 0:=
by
  sorry


@[simp]
lemma add_zero (D : 𝔻) : D + 0 = D:=
by
  sorry

lemma add_comm (D E : 𝔻) : D + E = E + D:=
by
  sorry

@[simp]
lemma zero_add (D : 𝔻) : 0 + D = D :=
by
  sorry


lemma add_assoc (D E F : 𝔻) : D + E + F = D + (E + F) :=
by
  sorry

lemma add_le_add_left (D E : 𝔻):  D ≤ E → ∀ (C : 𝔻), C + D ≤ C + E :=
by
  sorry



/-- Under addition we have a Linearly Ordered Additive Commutative Monoid -/
noncomputable
instance : LinearOrderedAddCommMonoid 𝔻 where
add_assoc := add_assoc
add_zero := add_zero
zero_add := zero_add
add_comm := add_comm
add_le_add_left :=add_le_add_left

end addition



section dense

/-- 𝔻 is densely ordered: if D < E then exists F satifying D < F and F < E-/
instance : DenselyOrdered 𝔻 where
dense :=
by
  sorry

end dense



section completeness

/-
The one we've all been waiting for.. if `S : Set 𝔻` is nonempty and bounded above
then it has a supremum
-/

open BigOperators

noncomputable
instance : SupSet 𝔻 where
sSup :=
by
  intro S
  by_cases h : S.Nonempty ∧ BddAbove S
  · use  ⋃ d ∈ S, d.A
    · sorry
    · sorry
    · sorry
    · sorry
-- If S is ∅ or not bounded above we still need to return something sensible
  · exact 0


@[simp]
lemma sSup' (S : Set 𝔻) (h1 : S.Nonempty) (h2: BddAbove S) : (sSup S).A = (⋃ d ∈ S, d.A) :=
by
  sorry


lemma sSup_default (S : Set 𝔻)  (hnb: ¬ BddAbove S) : sSup S = sSup ∅ :=
by
  sorry

/--
`𝔻` is complete: any nonempty set that is bounded above has a least upper bound-/
theorem complete_lub (S : Set 𝔻) (hne: S.Nonempty) (hupb: BddAbove S) :
 IsLUB S (sSup S) :=
by
  sorry

/-
We are halfway to proving that 𝔻 is a conditionally complete lattice

(The other half involves doing everything in terms of `sInf` as well.)
-/
theorem le_csSup (S : Set 𝔻) (a : 𝔻) (hbd: BddAbove S) (ha : a ∈ S):  a ≤ sSup S:=
by
  sorry

theorem  csSup_le (S : Set 𝔻) (a : 𝔻) (hne: S.Nonempty) (ha : a ∈ upperBounds S) : sSup S ≤ a :=
by
  sorry

/-
`sInf` is slightly more complicated since we can't just define this to be `⋂ d ∈ S, d.A`.

For example, if `S = {rat (1/n) | n ∈ ℕ}` then
  `⋂ d ∈ S, d.A = { x : ℚ | ∀ n, x < 1/n}`
  `             = { x : ℚ | x ≤ 0}`
which has a maximum element 0 so isn't a cut.

We could defer the definition until we have defined additive inverses of Dedekind cuts
and then define `-S = {-D | D ∈ S}` and `sInf S = -sSup (-S)` but instead we do it directly.
-/
noncomputable
instance : InfSet 𝔻 where
sInf :=
by
  intro S
  by_cases h : S.Nonempty ∧ ∃ l, ∀ d ∈ S, l ≤ d
  · use  (⋂ d ∈ S, d.A)\(upperBounds (⋂ d ∈ S, d.A))
    · sorry
    · sorry
    · sorry
    · sorry
  · exact 0 -- If S is ∅ or not bounded above we still need to return something

@[simp]
lemma sInf' (S : Set 𝔻) (h1 : S.Nonempty) (h2: BddBelow S) : (sInf S).A = (⋂ d ∈ S, d.A)\(upperBounds (⋂ d ∈ S, d.A)) :=
by
  sorry

lemma sInf_default (S : Set 𝔻)  (hnb: ¬ BddBelow S) : sInf S = sInf ∅ :=
by
  sorry

theorem complete_glb (S : Set 𝔻) (L : 𝔻) (hne: S.Nonempty) (hlb: L ∈ lowerBounds S) : IsGLB S (sInf S) :=
by
  sorry


/-
Lean can work out that 𝔻 is a lattice
-/
noncomputable
instance : Lattice 𝔻 := by infer_instance

noncomputable
instance : ConditionallyCompleteLattice 𝔻 := sorry

noncomputable
instance : ConditionallyCompleteLinearOrder 𝔻 :=sorry

end completeness



/-
Possible extensions:
1) Prove that 𝔻 has the Archmidean property
2) Define subtraction and negation on 𝔻 and show that with these 𝔻 forms a LinearOrderedAddCommGroup
-/


section archimedean

/-
Since we have an additive monoid Lean can infer that there
is a scalar multiplication by ℕ on 𝔻:

`n • D = D + D + ⋯ + D` (n copies of D)
-/
variable {n : ℕ} {D : 𝔻}
#check n • D -- n • D : 𝔻

#check exists_nat_gt -- Use the Archimedean property of ℚ


/-- An ordered commutative monoid is Archimedean if
`∀ x y, 0 < y → ∃ n : ℕ, x ≤ n • y` -/
instance : Archimedean 𝔻 := sorry

end archimedean


section subtraction

def sub : 𝔻 → 𝔻 → 𝔻 :=sorry

instance : Sub 𝔻  where
sub := sub

end subtraction



section addgroup

instance : Neg 𝔻 where
neg := fun D =>  (0 : 𝔻) - D

/--  `𝔻 is a Linearly ordered commutative group under addition -/
noncomputable
instance : LinearOrderedAddCommGroup 𝔻 := sorry

end addgroup
