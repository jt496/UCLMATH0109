import Mathlib
open scoped ENNReal -- ℝ≥0∞ (`\enn`) the positive reals with `+∞`
open Set Setoid
namespace NoSuchMeasure

/-- This instance allows us to use the notation
`s +ᵥ x`, where `s : Set ℝ` and `x : ℝ` -/
instance : HVAdd (Set ℝ) ℝ (Set ℝ) where hVAdd :=
  fun s z => {x | ∃ y, y ∈ s ∧ x = z + y}
/-!
# Vitali's example to prove that any sensible definition of a measure on ℝ
# cannot be defined for all subsets of ℝ
# Read the project pdf for details.
-/


/-
A real number `r : ℝ` is rational iff `∃ (q : ℚ), (q : ℝ) = r`.
In Lean this is expressed as `r ∈ range ((↑) : ℚ → ℝ)` where `(↑): ℚ → ℝ`
is the cast from `ℚ to ℝ`
-/
/-- eqv x y iff x - y is rational -/
@[simp]
def eqv : ℝ → ℝ → Prop := fun x y => (x - y)  ∈ range ((↑) : ℚ → ℝ)

-- State and prove lemmas that `eqv` is reflexive/symmetric/transitive and
-- then complete the instance below.


/-- eqv is an equivalence relation -/
instance Vitali : Setoid ℝ where
  r := eqv
  iseqv:=⟨by sorry, by sorry, by sorry⟩

/-
This Setoid instance registers the fact that `eqv` is an equivalence relation
on ℝ, and allows us to write `x ≈ y` for `eqv x y`

It also gives us access to lots of results about equivalence relations.

For example the equivalence classes are a `Set (Set ℝ)` (a family of subsets of ℝ)
-/
#check Vitali.classes
/-
def classes (r : Setoid α) : Set (Set α) :=
  { s | ∃ y, s = { x | r.Rel x y } }
-/


/-
We now want to define the set of reals 𝒱  by picking an element from each
equivalence class in [0,2⁻¹].

We do this using the function `half_rep` below. Before we can define this function
we need to prove a lemma that says that each equivalence class contains an element
from [0,2⁻¹]. See the lemma `exists_half_rep` below.
-/

/-- If c is an equvivalence class then it contains an element in [0,2⁻¹] -/
lemma exists_half_rep (hc : c ∈ Vitali.classes) : ∃ y, y ∈ c ∧ y ∈ Icc 0 (2⁻¹):=by
  sorry

/-- Use the axiom of choice to obtain an element of an equivalence class in [0,2⁻¹]-/
noncomputable
def half_rep : Vitali.classes → ℝ :=
    fun c => (exists_half_rep c.prop).choose

/-
Notice that the domain of this function is a Set not a Type,
so Lean coerces it into a Type `↑(Vitali.classes)`

This is the `Subtype` of `Set (Set ℝ)` consisting of terms of type `Set ℝ` that are
equivalence classes of the equvialence relation Vitali.

What this means is that if we have a term `c : Vitali.classes`, then `c` is a pair
`c = ⟨c.val, c.prop⟩` where `c.val : Set ℝ` and `c.prop` is a proof that
`c.val ∈ Vitali.classes`. So `c.prop : c.val ∈ Vitali.classes`
-/
section subtypes
variable (c : Vitali.classes)
#check c.val --
#check c.prop -- c.val ∈ Vitali.classes)
end subtypes

/-
 When proving two terms `c d : Vitali.classes` are equal it is sufficient to
 prove that the underlying sets are equal, i.e. `c.val = d.val → c = d`
 This fact is `Subtype.ext`
 -/
#check Subtype.ext

#check Exists.choose_spec

/-- The Vitali set 𝒱 is defined by choosing an element from each equivalence
   class in `[0, 2⁻¹]` -/
@[simp]
def 𝒱 : Set ℝ := range half_rep

/-
Look at the pdf and write out the statements (A)-(D) in Lean.
You will almost certainly want to state and prove other intermediate lemmas
about ` 𝒱 `
-/

/-- Since ℕ and ℚ are both countably infinite sets there is an equvialence (i.e. a bijection)
from ℕ to ℚ -/
noncomputable
def NtoQ : (ℕ ≃ ℚ) := by
  sorry
#check NtoQ.injective  -- NtoQ is injective
#check NtoQ.surjective -- NtoQ is surjective

/-
`ℝ≥0∞` is the extended positive reals (`\enn`). This is `ℝ≥0` (the nonnegative reals)
with an extra element `∞` (also known as `top` or  `⊤`) that is greater than every element of ℝ.
-/

/-- A Vitali-measure is -/
structure IsVitaliMeasure (μ : Set ℝ → ℝ≥0∞) : Prop where
-- μ is monotone on subsets
mono : ∀ s t, s ⊆ t → μ s ≤ μ t
-- μ [0, 1] = 1
unit : μ (Icc 0 1) = 1
-- μ is translation invariant
-- (here `s +ᵥ x` denotes translation of a set `s` by `x`)
translate_inv : ∀ s : Set ℝ, ∀ x : ℝ, μ (s +ᵥ x) = μ s
-- μ is countably-additive i.e. the measure of any countable union of pairwise
-- disjoint sets is the sum of the measures of the sets
ctble_add : ∀ (F : ℕ → Set ℝ), (∀ {i j}, i ≠ j →
    Disjoint (F i)  (F j)) → μ (⋃ n, F n) = ∑' n, μ (F n)
-- Note ` ∑' ` is called `tsum` in Mathlib



#check iUnion_congr_of_surjective
#check tsum_zero
#check ENNReal.tsum_const_eq_top_of_ne_zero -- A sum of non-zero constant terms is infinite

/-- No such measure exists -/
theorem no_such_measure : ¬ IsVitaliMeasure μ :=by
  sorry

end NoSuchMeasure
