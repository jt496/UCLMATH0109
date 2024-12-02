import Mathlib

open LinearMap Submodule


/-

# Useful tactics:

# ext, ring, simp?, exact?, calc, norm_cast, push_cast, linarith

-/

/--
`Sequence` is the set of sequences of real numbers.
This is a vector space, where addition and scalar multiplication of
sequences is defined pointwise.
-/

abbrev Sequence := ℕ → ℝ

/--
For a sequence `s`, we define `diff s` to be the sequence `t` defined by`
  `t n = s (n + 1) - s n`.
-/
@[reducible]
def diffFun (s : Sequence) : Sequence :=
  fun n ↦ s (n + 1) - s n

/-
# 1. 1 mark
Prove the following definitional lemma for `diff`.
-/
@[simp]
lemma diffFun_apply (s : Sequence) (n : ℕ) : diffFun s n = s (n + 1) - s n := by
  sorry

/-
# 2. 4 marks
Make `diffFun` into a linear map `diff`.
-/
def diff : Sequence →ₗ[ℝ] Sequence where
  toFun := diffFun
  map_add' := by
    sorry
  map_smul' := by
    sorry

/-
# 3. 1 mark
Prove the following definitional lemma for `diff`.
-/
@[simp]
lemma diff_apply (s : Sequence) : diff s n = s (n + 1) - s n := by
  sorry

/-
# 4. 2 marks
Prove that `diff 1 = 0`, where `1` is the constant sequence `1,1,1,1,...`
and `0` is the constant sequence `0,0,0,0,...`.
Remember that this is an equation of functions.
-/
lemma diff_one : diff 1 = 0 := by
  sorry

/-
# 5. 2 marks.
-/
example : diff (fun n ↦ n) = 1 := by
  sorry

/-
# 6. 2 marks.
-/
example : diff (fun n ↦ n^2) = (fun n : ℕ ↦ (2*n + 1 : ℝ)) := by
  sorry


#check mem_span_singleton
#check mem_ker
#check map_smul
#check smul_zero
#check sub_eq_zero

/-
# 7. 5 marks.
Prove that the kernel of the linear map `diff` is equal to the span of the sequence `1`.
-/
lemma ker_diff : ker diff = span (R := ℝ) {1} := by
  sorry

/--
 xₙ → a as n → ∞ iff for any ε > 0 there exists N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε
-/
@[simp]
def sLim (x : Sequence) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

/-
# 8. 5 marks.
`If xₙ → 0 as nₙ → ∞ then xₙ₊₁ - xₙ → 0 as nₙ → ∞.`
Proof: Let ε > 0 be given. Using the definition of xₙ → a obtain N ∈ ℕ such that
for all n ≥ N we have |xₙ - a| < ε/2.

For all n ≥ N we have:
|xₙ₊₁ - xₙ| = |xₙ₊₁ - a + a - xₙ|
            ≤ |xₙ₊₁ - a| + |a - xₙ|
            < ε/2 + ε/2
            = ε.
-/
/-- `If xₙ → 0 as nₙ → ∞ then xₙ₊₁ - xₙ → 0 as nₙ → ∞.` (See above for sketch of the proof.)-/
lemma sLim_diff (x : Sequence) (a : ℝ) (ha : sLim x a) :  sLim (diff x) 0 := by
  sorry
