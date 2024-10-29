import Mathlib.Tactic

/-

A `Dedekind cut` is a partition of the rationals `(A , Aᶜ)` such that both A and Aᶜ are
nonempty with the following properties:

1)  A is a down-set: if x < y and y ∈ A then x ∈ A;

2)  A has no maximum element: if x ∈ A there exists y ∈ A with x < y.

One way of constructing the real numbers from ℚ is as Dedekind cuts.

We identify a real number `r` with the cut `(A, Aᶜ)` where `A = {x ∈ ℚ | x < r}`

See `AssessedSheet4.pdf` for more details.

-/
/--
Dedekind cut
-/
@[ext] -- two Dedekind cuts D = E iff D.A = E.A
structure Dedekind where
  A         : Set ℚ
  nonempty  : A.Nonempty
  nonempty' : Aᶜ.Nonempty
  down      : ∀ ⦃x y⦄, x < y → y ∈ A → x ∈ A
  no_max    : ∀ ⦃x⦄, x ∈ A → ∃ y ∈ A, x < y

-- the @[ext] label produces the following two results for free:
#check Dedekind.ext
#check Dedekind.ext_iff

namespace Dedekind
notation "𝔻" => Dedekind

/- All our results will now be in the Dedekind namespace -/
/-
We open a named section to explain what we are trying to prove (we will prove
some basic results in this section hence the name).
-/
section basics
variable {D : 𝔻}
variable {x y : ℚ}
/-
The use of a section allows us to introduce variables into the local context
 that will vanish once the section ends.
-/

/-- If `D = (A , Aᶜ)` is a Dedekind cut with `x ∈ A` and `y ∈ Aᶜ` then `x < y`-/
lemma lt_of_cut (hx : x ∈ D.A) (hy : y ∈ D.Aᶜ) : x < y :=by
  sorry


#check D.A         -- D.A : Set ℚ
#check D.nonempty  -- D.nonempty : Set.Nonempty D.A
#check D.nonempty' -- D.nonempty' : Set.Nonempty D.Aᶜ
#check D.down      -- D.down : ∀ ⦃x y : ℚ⦄, x < y → y ∈ D.A → x ∈ D.A
#check D.no_max    -- D.no_max : ∀ ⦃x : ℚ⦄, x ∈ D.A → ∃ y, y ∈ D.A ∧ x < y


/-- We can order Dedekind cuts with `D ≤ E` iff `D.A ⊆ E.A` -/
instance : LE 𝔻 where
  le := fun D E => D.A ⊆ E.A

lemma le' : D ≤ E ↔ D.A ⊆ E.A :=by rfl

/-- We can define `<` on Dedekind cuts by `D < E` iff `D ≤ E` and `D ≠ E`-/
instance : LT 𝔻 where
  lt := fun D E => D ≤ E ∧ ¬ E ≤ D

/-- `D < E` iff `D.A` is a proper-subset of `E.A` -/
lemma lt' : D < E ↔ D.A ⊂ E.A :=by sorry

/-- D < E iff ∃ x ∈ E.A \ D.A -/
lemma lt_iff_exists : D < E ↔ ∃ x, x ∈ E.A \ D.A:=by
  sorry

end basics

/-
We now establish that Dedekind cuts form a `Preorder`.

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

-/

instance : Preorder 𝔻 where
  le_refl :=by
    sorry
  le_trans :=by
    sorry
/--
𝔻 contains a copy of the rational numbers given by the embedding `rat`
-/
def rat (q : ℚ) : 𝔻 :=by
  use {x : ℚ | x < q}
  · sorry
  · sorry
  · sorry
  · sorry

@[simp]
lemma rat' (q : ℚ) : (rat q).A = {x : ℚ | x < q} := rfl

/-- The map `rat` is an order embedding: i.e. it is injective and `rat p ≤ rat q ↔ p ≤ q`-/
def Rat : ℚ ↪o 𝔻 where
  toFun := rat
  inj' :=by
    sorry
  map_rel_iff' :=by
    sorry

instance : Zero 𝔻 where
zero := rat 0

/--
There is a Dedekind cut corresponding to √2
-/
def root_two : 𝔻 :=by
  use { x : ℚ | x^2 < 2 ∨ x < 0}
  · sorry
  · sorry
  · sorry
  · sorry

/-
If `S : Set 𝔻` is nonempty and bounded above then it has a supremum defined
by taking the union of cuts in S.
-/
noncomputable
instance : SupSet 𝔻 where
  sSup :=by
    intro S
    by_cases h : S.Nonempty ∧ BddAbove S
    · use  ⋃ d ∈ S, d.A
      · obtain ⟨D,hs⟩:=h.1
        obtain ⟨d,hd⟩:=D.nonempty
        use d
        exact Set.mem_biUnion hs hd
      · sorry
      · sorry
      · sorry
-- If S is ∅ or not bounded above we still need to return something sensible
    · exact 0


#check dif_pos -- These can be used to simplify a function defined using `by_cases` or `if then else`
#check dif_neg

lemma sSup' (S : Set 𝔻) (h1 : S.Nonempty) (h2: BddAbove S) : (sSup S).A = (⋃ d ∈ S, d.A) :=by
  sorry


#check IsLeast
#check upperBounds
#check IsLUB

/--
`𝔻` is complete: any nonempty set of Dedekinds cuts that is bounded above
  has a least upper bound-/
theorem complete_lub (S : Set 𝔻) (hne: S.Nonempty) (hupb: BddAbove S) :
  IsLUB S (sSup S) :=by
    sorry
