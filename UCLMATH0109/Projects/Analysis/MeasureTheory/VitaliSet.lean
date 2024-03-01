import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic

/-!
# Vitali's example to prove that any sensible definition of a measure on ℝ
# cannot be defined for all subsets of ℝ

First note that `ℝ≥0∞` is the extended positive reals. This is `ℝ≥0` (the nonnegative reals)
with an extra element `∞` (also known as `top` or  `⊤`) that is greater than every element of ℝ.

We will say that `μ : Set ℝ → ℝ≥0∞` is a Vitali-measure iff
  (1) it is monotone, so `s ⊆ t → μ s ≤ μ t`
  (2) it gives the unit interval the length you expect: `μ [0, 1] = 1`
  (3) it is translation invariant, so for any `s : Set ℝ` and `x : ℝ`
    we have `μ (s +ᵥ x) = μ s` (where `s +ᵥ x := {y | ∃ z, z ∈ s ∧ y = z + x}`)
  (4) it is countably additive: ie if `F : ℕ → Set ℝ` is a countable sequence
      of sets in ℝ that are pairwise disjoint, then `μ (⋃ n, F n) = ∑' n, μ (F n)`

(Note that the `∑' ` in (4) is the Mathlib `tsum` which is quite easy to work with in `ℝ≥0∞` since
any such sum is a sum of nonnegative terms and thus always converges, either to a nonnegative real or `∞`.)

We start by defining an equivalence relation on `ℝ` by `x ≈ y` iff `x - y is rational`
Note that this can seem confusing in Lean since `ℚ` is not contained in `ℝ`, instead
we need to use the fact that any rational number can be `cast` into a real number.
So `x - y is rational ↔ ∃ (q : ℚ), such that x - y = (q : ℝ)`

Our aim is to construct 𝒱, a set of reals, with the property that

(A) 𝒱 ⊆ [0, 2⁻¹]
(B) ⋃ (q : ℚ), 𝒱 +ᵥ q = ℝ
(C) If (p q : ℚ) and p ≠ q then `𝒱 +ᵥ p` and `𝒱 +ᵥ q` are disjoint

(A) implies that if `n : ℕ` then 𝒱 + 1/(n+2) ⊆ [0,1]

Hence (C), (1)-(4) and summing over ℕ we have

#  ∑'n,  μ 𝒱  =  ∑' n, μ (𝒱 +ᵥ 1/(n+2)) = μ(⋃ n, 𝒱 +ᵥ 1/(n+2)) ≤ μ [0,1] = 1.

Since the LHS is an infinite sum of constant nonnegative terms we deduce that `μ 𝒱 = 0`

Next we use the fact that `ℚ` is countable, (B), (C), (3) and (4) to deduce that

# μ ℝ = μ (⋃ q:ℚ, 𝒱 +ᵥ q) = ∑' q, μ (𝒱 +ᵥ q) = ∑' q, μ 𝒱  = ∑' 0 = 0

Which is impossible since `[0,1] ⊆ ℝ` and `μ [0,1] = 1`.

See pdf for more details.
-/


open Set Setoid
namespace Vitali

/-
A real number `r : ℝ` is rational iff `∃ (q : ℚ), (q : ℝ) = r`.
In Lean this is expressed as `r ∈ range ((↑) : ℚ → ℝ)` where `(↑): ℚ → ℝ` is the
cast from `ℚ to ℝ`
-/

/-- x ≈ y iff x - y is rational -/
@[simp]
def eqv : ℝ → ℝ → Prop := fun x y => (x - y)  ∈ range ((↑) : ℚ → ℝ)

/-- eqv is reflexive -/
@[simp]
lemma eqv_refl : Reflexive eqv :=
by
  sorry

/-- eqv is symmetric -/
@[simp]
lemma eqv_symm : Symmetric eqv :=
by
  sorry

/-- eqv is transitive -/
@[simp]
lemma eqv_trans : Transitive eqv :=
by
  sorry

/-- eqv is an equivalence relation -/
instance Vitali : Setoid ℝ where
  r := eqv
  iseqv:= by sorry

/-
This instance registers the fact that `eqv` is an equivalence relation (Setoid)
on ℝ, and allows us to write `x ≈ y` for `eqv x y`

It also gives us access to lots of results about equivalence relations.

For example the equivalence classes are a `Set (Set ℝ)` (a family of subsets of ℝ)
-/
#check Vitali.classes
/-
def classes (r : Setoid α) : Set (Set α) :=
  { s | ∃ y, s = { x | r.Rel x y } }
-/

#check mem_classes
#check eq_of_mem_classes
#check rel_iff_exists_classes

/-- We can now write `x ≈ y` for `eqv x y`-/
@[simp]
lemma Vitali' : x ≈ y ↔ eqv x y :=by sorry

/-- The equivalence classes are -/
@[simp]
lemma classes' : c ∈ Vitali.classes ↔ ∃ y, c = {x | x ≈ y}:=by sorry

#print Int.fract

/-- Any real x is related to its fractional part, defined by Int.fract x = x - ⌊x⌋ -/
@[simp]
lemma eqv_intFract (x : ℝ) : x ≈ Int.fract x :=
by
  sorry

/-- If x ≈ y and q : ℚ  then x ≈ (y - q) -/
lemma rel_add  {x y : ℝ} (q : ℚ) (h : x ≈ y) : x ≈ y + q:=
by
  sorry


#check exists_rat_btwn

/-- If x : ℝ and a < b then x is related to an element of (a,b) -/
lemma rel_dense (x : ℝ) (hab: a < b) : ∃ y, x ≈ y ∧ y ∈ Ioo a b :=
by
  sorry

/-- If c is an equvivalence class then it contains an element in [0,2⁻¹] -/
lemma exists_half_rep (hc : c ∈ Vitali.classes) : ∃ y, y ∈ c ∧ y ∈ Icc 0 (2⁻¹):=
by
  sorry

/-
We now want to define the set of reals 𝒱  by picking an element from each
equivalence class in [0,2⁻¹].

We do this using the function `half_rep` below.

Notice that the domain of this function is a Set not a Type,
so Lean coerces it into a Type `↑(classes Vitali)`

This is the `Subtype` of `Set (Set ℝ)` consisting of terms of type `Set ℝ` that are
equivalence classes of the equvialence relation Vitali.

What this means is that if we have a term `c : Vitali.classes`, then `c` is a pair
`c = ⟨c.val, c.prop⟩` where `c.val : Set ℝ` and `c.prop` is a proof that
`c.val ∈ Vitali.classes`. So `c.prop : c.val ∈ Vitali.classes`

The only result about `Subtype` that you may need is that when proving two terms
`c d : Vitali.classes` are equal it is sufficient to prove that the underlying
sets are equal, i.e. `c.val = d.val → c = d`-/
#check Subtype.ext

/-- Use `choice` to obtain an element of an equivalence class in [0,2⁻¹]-/
noncomputable
def half_rep : Vitali.classes → ℝ :=
by
  classical
  intro c
  exact (exists_half_rep c.prop).choose

#check Classical.choose_spec

/-- half_rep c belongs to c -/
@[simp]
lemma half_rep_mem (c : Vitali.classes) : (half_rep c) ∈ (c : Set ℝ) :=
by
  sorry

/-- half_rep c belongs to [0,2⁻¹] -/
@[simp]
lemma half_rep_in_Icc (c : Vitali.classes) : half_rep c ∈ Icc 0 (2⁻¹):=
by
  sorry

/-- The Vitali set 𝒱 is defined by choosing an element from each equivalence class in `[0, 2⁻¹]` -/
@[simp]
def 𝒱 : Set ℝ := range half_rep

@[simp]
lemma mem_V: x ∈ 𝒱 ↔ ∃ c, half_rep c = x:=by sorry

/-- 𝒱 ⊆ [0,2⁻¹]-/
lemma V_subset_Icc : 𝒱 ⊆ Icc 0 (2⁻¹):=
by
  sorry

#check rel_iff_exists_classes
#check eq_of_mem_classes
#check Subtype.ext_val

/-- If x, y ∈ 𝒱 and x ≈ y then x = y -/
lemma mem_rel_eq_Vitali (hx : x ∈ 𝒱) (hy : y ∈ 𝒱) (hxy: Vitali.Rel x y) : x = y:=
by
  sorry

#check mem_classes

/-- If y ∈  ℝ then there exists a ∈ 𝒱 such that y ≈ a  -/
lemma exists_mem_equiv (y : ℝ) : ∃ a, a ∈ 𝒱 ∧ Vitali.Rel y a :=
by
  sorry

/-- S.translate z is S +ᵥ z the z-translate of a set S -/
def Set.translate (s : Set ℝ) (z : ℝ) : Set ℝ := {x | ∃ y, y ∈ s ∧ x = z + y}

/-- This instance allows us to use the notation `S +ᵥ x` for `S.translate x` -/
instance : HVAdd (Set ℝ) ℝ (Set ℝ) where hVAdd := Set.translate

@[simp]
lemma mem_translate {s: Set ℝ} {z : ℝ} : x ∈ s +ᵥ z ↔ ∃ y, y ∈ s ∧ x = z + y:=by sorry

/-- 0 ≤ (n+2)⁻¹ ≤ 2⁻¹ for any n : ℕ -/
lemma inv_nat_add_two (n : ℕ) : ((n + 2) : ℝ)⁻¹ ∈ Icc 0 (2⁻¹) :=
by
  sorry

/-- 𝒱 +ᵥ (n+2)⁻¹ ⊆ [0,1] -/
lemma V_translate_inv_nat (n : ℕ): 𝒱 +ᵥ (((n : ℝ) + 2)⁻¹) ⊆ Icc 0 1:=
by
  sorry

/-- The Union of (𝒱 +ᵥ q) over ℚ is ℝ -/
lemma V_iUnion : ⋃ q : ℚ,  𝒱 +ᵥ (q : ℝ)  = univ :=
by
  sorry

#check not_disjoint_iff_nonempty_inter
#check  Rat.cast_inj

/-- The (𝒱 +ᵥ p) are pairwise disjoint (for p ≠ q ∈ ℚ) -/
lemma V_disjoint_add_rat_ne {p q : ℚ} (hne: p ≠ q): Disjoint (𝒱 +ᵥ (p : ℝ)) (𝒱 +ᵥ (q : ℝ)):=
by
  sorry

#check Nat.cast_inj
#check Rat.cast_coe_nat

/-- The special case of the previous result, when p = (i+2)⁻¹, q = (j+2)⁻¹ and i ≠ j  will be useful later-/
lemma ctble_Disjoint {i j : ℕ} (hij : i ≠ j): Disjoint (𝒱 +ᵥ (i + 2 : ℝ)⁻¹) (𝒱 +ᵥ (j + 2 : ℝ)⁻¹) :=
by
  sorry

/-- Since ℕ and ℚ are both countably infinite sets there is an equivalence from ℕ to ℚ -/
noncomputable
def NtoQ : (ℕ ≃ ℚ):=
by
  sorry

open scoped ENNReal

structure IsVitaliMeasure (μ : Set ℝ → ℝ≥0∞) : Prop where
-- μ is monotone on subsets
mono : ∀ s t, s ⊆ t → μ s ≤ μ t
-- μ [0, 1] = 1
unit_length : μ (Icc 0 1) = 1
-- μ is translation invariant
translate_invariant : ∀ s : Set ℝ, ∀ x : ℝ, μ (s +ᵥ x) = μ s
-- μ is countably-additive i.e. the measure of any countable union of pairwise
-- disjoint sets is the sum of the measures of the sets
ctble_add : ∀ (F : ℕ → Set ℝ), (∀ {i j}, i ≠ j → Disjoint (F i)  (F j)) → μ (⋃ n, F n) = ∑' n, μ (F n)

#check iUnion_congr_of_surjective
#check tsum_zero
#check ENNReal.tsum_const_eq_top_of_ne_zero

/-- No such measure exists -/
theorem no_such_measure : ¬ IsVitaliMeasure μ :=
by
  sorry

/-
Possible extension: explore what happens if we weaken the condition of countably additive to
finitely additive.
-/
