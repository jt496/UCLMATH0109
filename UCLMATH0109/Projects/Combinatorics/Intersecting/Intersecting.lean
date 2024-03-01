import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Finset

namespace Intersecting

/-
If `A : Finset α` then `Finset.card A` is its cardinality and we will use |A| as notation
for this.
-/
local notation "|" x "|" => Finset.card x
/-
If we want to talk about a type `α : Type` that is finite we do this with a Fintype instance
[Fintype α]. The size of α is then `Fintype.card α` and we use ‖α‖ as notation for this
-/
local notation "‖" x "‖" => Fintype.card x
/-
We also introduce the notation `𝒫 α` for the powerset of α
-/
local notation:100 "𝒫" arg:100 => powerset (univ : Finset arg)

variable {α : Type _}  [DecidableEq α]

/-
See pdf for details of the results in this project.
-/

/-- A family of Finsets `𝒜` is Intersecting if any two sets
  in the family are not disjoint -/
def Intersecting (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒜 → ∀ ⦃B⦄, B ∈ 𝒜 → ¬Disjoint A B

variable {𝒜  : Finset (Finset α)}

/-- rw lemma for Intersecting -/
@[simp]
lemma intersecting_iff : Intersecting 𝒜 ↔ ∀ ⦃A⦄, A ∈ 𝒜 →∀ ⦃B⦄, B ∈ 𝒜 → ¬Disjoint A B :=
by
  sorry

#check disjoint_left
#check not_disjoint_iff
#check mem_inter

/-- 𝒜 is intersecting iff the intersection of any pair of sets in 𝒜 contains an element-/
lemma intersecting_iff_exists : Intersecting 𝒜 ↔ ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∃ x, x ∈ A ∩ B :=
by
  sorry

/-- The empty set does not belong at any intersecting family-/
lemma empty_not_mem_intersecting (h : Intersecting 𝒜) : ∅ ∉ 𝒜:=
by
  sorry


/-
If A : Finset α then its complement Aᶜ may not be finite.
However it will be finite if α is itself finite.
-/
variable  [Fintype α]

/-
So from now on α is finite so if `A : Finset α` then `Aᶜ : Finset α`

We will now introduce some potentially confusing notation.

If `𝒜 : Finset (Finset α)` we will use 𝒜ᶜ to denote the family of all
complements of members of 𝒜, i.e.

`𝒜ᶜ = { Aᶜ | A ∈ 𝒜}`

[We define this notation with the instance below. If we remove this instance
then Lean will interpret 𝒜ᶜ as the complement, in Finset (Finset α),
of the family 𝒜, i.e. as  {B | B ∉ 𝒜}.]
-/
instance : HasCompl (Finset (Finset α)) :=
⟨fun 𝒜 => 𝒜.image fun A => Aᶜ⟩


/-- definitional lemma for 𝒜ᶜ = {Aᶜ | A ∈ 𝒜} -/
@[simp]
lemma compl : 𝒜ᶜ = 𝒜.image fun A => Aᶜ :=
by
  sorry

#check mem_image

/-- B ∈ 𝒜 iff ∃ A ∈ 𝒜 such that Aᶜ = B -/
@[simp]
lemma mem_compl : B ∈ 𝒜ᶜ ↔ ∃ A ∈ 𝒜, Aᶜ = B :=
by
  sorry

#check compl_compl

lemma mem_compl_iff : B ∈ 𝒜ᶜ ↔ Bᶜ ∈ 𝒜 :=
by
  sorry

#check card_image_of_injOn
#check compl_inj_iff

/-- the family of complements has the same size as the family -/
lemma card_comp_fam : |𝒜ᶜ| = |𝒜| :=
by
  sorry

#check disjoint_compl_right

/-- If 𝒜 is intersecting and A ∈ 𝒜 then Aᶜ ∉ 𝒜  -/
lemma mem_imp_compl_not_mem (h : Intersecting 𝒜) (hA : A ∈ 𝒜) : Aᶜ ∉ 𝒜 :=
by
  sorry

/-- if `𝒜` is intersecting then it is disjoint from `𝒜ᶜ` -/
lemma int_imp_comp_disj  (hI : Intersecting 𝒜) : Disjoint 𝒜 𝒜ᶜ :=
by
  sorry

#check card_univ
#check subset_univ
#check mem_powerset
#check card_le_of_subset
#check card_powerset

/-- a family of Finset α  has size at most `2^‖α‖`-/
lemma card_family : |𝒜| ≤ 2 ^ ‖α‖ :=
by
  sorry

/-
This `Inhabited` instance tells Lean that α has `default` term  and in particular is Nonempty
-/
variable [Inhabited α]

#check Fintype.card_ne_zero

lemma card_of_nonempty : ‖α‖ - 1 + 1 = ‖α‖ :=
by
  sorry

/-- An intersecting family of subsets of `α` has size at most `2^(‖α‖-1)`-/
theorem card_le_of_int (hI : Intersecting 𝒜) : |𝒜| ≤ 2 ^ (‖α‖ - 1) :=
by
  sorry

/--
A family is maximal intersecting iff it is intersecting and it is a not
a proper subfamily of any other intersecting family.
-/
def MaximalIntersecting (𝒜 : Finset (Finset α)) : Prop :=
 Intersecting 𝒜  ∧ ∀ ⦃ℬ⦄, 𝒜 ⊆ ℬ → Intersecting ℬ →  𝒜 = ℬ

/-- A maximal intersecting family is intersecting-/
@[simp]
lemma int_of_max_int (h : MaximalIntersecting 𝒜) : Intersecting 𝒜  :=
by
  sorry


/--
 If a maximal intersecting family 𝒜 is properly contained in ℬ then ℬ is not
 intersecting-/
@[simp]
lemma not_int_of_gt_max_int (h : MaximalIntersecting 𝒜) (hB :𝒜 ⊂ ℬ) : ¬Intersecting ℬ :=
by
  sorry


#check ssubset_insert

/--If we add any new set to a maximal intersecting family then it is no longer intersecting -/
@[simp]
lemma not_int_of_insert_not_mem (hMI : MaximalIntersecting 𝒜) (hA: A ∉ 𝒜) : ¬Intersecting (insert A 𝒜 ) :=
by
  sorry



#check mem_insert
#check disjoint_self
/-- 𝒜 is intersecting but 𝒜 ∪ {A} is not then either A = ∅ of A is disjoint from some
member of 𝒜  -/
@[simp]
lemma exists_of_not_int_insert (hI : Intersecting 𝒜) (hnI: ¬ Intersecting (insert A 𝒜)) :
A = ∅ ∨ (∃ B, B ∈ 𝒜 ∧ Disjoint A B) :=
by
  sorry

#check not_isEmpty_iff
#check instNonempty
#check univ_eq_empty_iff
#check Disjoint.mono_left

/-- If 𝒜 is a maximal intersecting family then it contains the universal set -/
lemma univ_mem_max_int (h: MaximalIntersecting 𝒜) : univ ∈ 𝒜 :=
by
  sorry

/-- Any maximal intersecting family is closed upwards -/
lemma max_intersecting_mono (h : MaximalIntersecting 𝒜) (hA : A ∈ 𝒜) (hB: A ⊆ B) : B ∈ 𝒜  :=
by
  sorry

#check insert_eq_self
#check le_compl_iff_disjoint_left
#check exists_of_ssubset

/--If 𝒜 is maximal intersecting then it contain one of A,Aᶜ for any A ⊆ univ   -/
theorem max_intersecting_iff (hI : Intersecting 𝒜): MaximalIntersecting 𝒜 ↔ ∀ A ∈ 𝒫 α, A ∈ 𝒜 ∨ Aᶜ ∈ 𝒜 :=
by
  sorry

/- If 𝒜 is maximal intersecting in α then 𝒫 (α) = 𝒜 ∪ 𝒜ᶜ -/
theorem max_int_union_compl (h: MaximalIntersecting 𝒜) : 𝒫 α = 𝒜 ∪ 𝒜ᶜ :=
by
  sorry

#check card_union_eq

/-- Any maximal intersecting family of sets from a finite non-empty set α has size 2^(‖α‖-1) -/
theorem card_maximal_int (h: MaximalIntersecting 𝒜)  : |𝒜| = 2^(‖α‖ - 1) :=
by
  sorry

/-
We have proved lots of results about maximal intersecting families but we have yet to show
that any actually exist!

The final result below is a computable instance of a default maximal intersecting family
(we use here the fact that `α` is `Inhabited` so it contains a `default` term).
-/
#check Inhabited
#check (default : α) -- This is from the `Inhabited α` instance

instance inhabited_max_int : Inhabited { 𝒜 : Finset (Finset α) // MaximalIntersecting 𝒜 } :=
by
  sorry


end Intersecting


/-!
Possible extension: prove the following special case of the Erdos--Ko-Rado theorem.

If 𝒜 is an intersecting family of k-sets from a set of size 2k and k ≥ 1 then
  |𝒜| ≤ (2k - 1).choose (k - 1)
-/
