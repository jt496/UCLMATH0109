import Mathlib

namespace IntersectingFamilies
open Finset

/-
# This project is on intersecting families of set.
# See the pdf for details.
-/

/-
If `A : Finset α` then `Finset.card A` is its cardinality. We will use |A| as notation for this.
-/
local notation "|" x "|" => Finset.card x
/-
If we want to talk about a type `α : Type` that is finite we do this with a Fintype instance
[Fintype α]. The size of `α` is `Fintype.card α` and we use ‖α‖ as notation for this.
-/
local notation "‖" x "‖" => Fintype.card x

section alpha
variable {α : Type*} [DecidableEq α]

/-- A family of Finsets `𝒜` is Intersecting if any two sets in the family are not disjoint-/
@[reducible]
def Intersecting (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ 𝒜 → ∀ ⦃B⦄, B ∈ 𝒜 → ¬Disjoint A B

variable {𝒜  : Finset (Finset α)}

/-- definitional lemma for Intersecting -/
@[simp]
lemma intersecting_iff : Intersecting 𝒜 ↔ ∀ ⦃A⦄, A ∈ 𝒜 →∀ ⦃B⦄, B ∈ 𝒜 → ¬Disjoint A B := by sorry

#check disjoint_left
#check not_disjoint_iff
#check mem_inter

/-
If A : Finset α then its complement Aᶜ may not be finite.
However Aᶜ will be finite if α is itself finite. (we will also assume α is nonempty.)
-/

variable  [Fintype α] [Nonempty α]
/-
So from now on α is finite so if `A : Finset α` then `Aᶜ : Finset α`

We will now introduce some potentially confusing notation.

If `𝒜 : Finset (Finset α)` (i.e. 𝒜 is finite family of finite subsets of elements of α)
we will use `𝒜ᶜ` to denote the family of all complements of members of 𝒜, i.e.

    `𝒜ᶜ = { Aᶜ | A ∈ 𝒜}`

[We define this notation with the instance below. If you remove this instance
then Lean will interpret 𝒜ᶜ as the complement, in Finset (Finset α),
of the family 𝒜, i.e. as  {B | B ∉ 𝒜}.]
-/
instance : HasCompl (Finset (Finset α)) := ⟨fun 𝒜 => 𝒜.image fun A => Aᶜ⟩

/-- definitional lemma for 𝒜ᶜ = {Aᶜ | A ∈ 𝒜} -/
@[simp]
lemma compl : 𝒜ᶜ = 𝒜.image fun A => Aᶜ := by sorry


/-
The following results may be useful in your formalization.

One useful operation on Finsets is `insert a s` which, if `s : Finset X`
and `a : X`, forms the Finset `s` with `a` inserted. This is the same as
`s ∪ {a}` but you will probably find `insert` much easier to work with.
 -/
#check mem_insert
#check insert_eq_self

/-- An intersecting family of subsets of `α` has size at most `2 ^ (‖α‖ - 1)`-/
theorem card_le_of_intersecting (hI : Intersecting 𝒜) : |𝒜| ≤ 2 ^ (‖α‖ - 1) :=by
  sorry


/--
A family is maximally intersecting iff it is intersecting and it is a not
a proper subfamily of any other intersecting family.
-/
def MaximallyIntersecting (𝒜 : Finset (Finset α)) : Prop :=
 Intersecting 𝒜  ∧ ∀ ⦃ℬ⦄, 𝒜 ⊆ ℬ → Intersecting ℬ →  𝒜 = ℬ

/-- Any maximally intersecting family of sets from a finite non-empty set α has size 2 ^ (‖α‖ - 1) -/
theorem card_maximal_int (h: MaximallyIntersecting 𝒜)  : |𝒜| = 2 ^ (‖α‖ - 1) := by sorry




end alpha

section Fin

/-
Possible extension: describe a function `max` that maps an intersecting family `𝒜` of subsets of
`{0,1,...,n}` to a maximally intersecting family containing `𝒜`
-/
variable {n : ℕ}
#check Fin.last n -- the largest element of the set {0,1,...,n}

/-- `up 𝒜` is the family of all supersets of members of 𝒜 -/
@[reducible]
def up (𝒜 : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin (n + 1))) :=
  (univ : Finset (Fin (n + 1))).powerset.filter (fun B => ∃ A ∈ 𝒜, A ⊆ B)

/-
Note that if 𝒜 is intersecting then so is `up 𝒜` so any maximally intersecting family
containing `𝒜` also contains `up 𝒜`.
-/

/-- We say the set A is `big` iff it contains at least as many elements as its complement, and if
 |A| = |Aᶜ| then `n ∈ A` -/
@[reducible]
def big (A : Finset (Fin (n + 1))) : Prop :=  |Aᶜ| ≤ |A| ∧ (|Aᶜ| = |A| → (Fin.last n ∈ A))

/-
Note that if `A` and `B` are both `big` then they cannot be disjoint.
-/

/-- `others 𝒜` - take the `big` one from each pair (B,Bᶜ) such that both B and Bᶜ meet every set in 𝒜 -/
@[reducible]
def others (𝒜 : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin (n + 1))) :=
  (univ : Finset (Fin (n + 1))).powerset.filter (fun B => big B ∧ ∀ A, A ∈ 𝒜 → ¬ A ⊆ B ∧ ¬ A ⊆ Bᶜ)

/-- A maximally intersecting family containing 𝒜 (if 𝒜 is intersecting) -/
@[reducible]
def max (𝒜 : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin (n + 1))) := (up 𝒜) ∪ (others 𝒜)


/-- If 𝒜 is intersecting then `max 𝒜` is a maximally intersecting family containing 𝒜 -/
theorem max_intersecting_isMaximal {𝒜 : Finset (Finset (Fin (n + 1)))} (h : Intersecting 𝒜) : 𝒜 ⊆ (max 𝒜) ∧ MaximallyIntersecting (max 𝒜) :=by
  sorry

/-
We can now use the `max` function to compute examples of maximally intersecting families containing
any given intersecting family.
-/

@[reducible]
def Fano : (Finset (Finset (Fin 7))) := {{0,1,2},{2,3,4},{4,5,0},{1,6,4},{2,6,5},{0,6,3},{1,3,5}}

@[reducible]
def Dictator (n : ℕ): (Finset (Finset (Fin (n + 1)))) := {{0}}


#eval (Intersecting Fano)
#eval (max Fano)
#eval (max Fano).card
#eval (up Fano).card
#eval (others Fano).card
#eval (others (Dictator 7)).card
#eval (up (Dictator 7)).card

end Fin
end IntersectingFamilies
