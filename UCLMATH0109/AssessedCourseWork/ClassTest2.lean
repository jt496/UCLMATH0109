import Mathlib

/-- xₙ → a iff for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/-- The standard definition of continuity of f at a -/
def CtsAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε


/-
Prove that the real sequence 1/(n+1) → 0 as n → ∞
-/
-- # 5 marks
lemma tends_to_zero : limₙ (fun n => (n+1)⁻¹) 0 :=
by
  sorry



/-
Let `f : ℝ → ℝ` and `a : ℝ`.
Prove that `f(x)` is continuous at `x = a` iff for every sequence `xₙ` that converges to `a`,
the sequence `f(xₙ)` converges to `f(a)`.

# Sketch of proof:
(=>)
If f is continuous at x = a then given `ε > 0` there exists `δ > 0` such
`|x - a| < δ` implies `|f(x) - f(a)| < ε`.
So given a sequence `xₙ`, that converges to `a` we can use the
definition of `xₙ → a` with `ε = δ` to prove that `f(xₙ) → f(a)`

(<=)
Suppose that for every sequence `xₙ` converging to `a` we have `f(xₙ) → f(a)`.
We need to prove that `f(x)` is continuous at `x = a`.

Let ε > 0 be given and proceed by contradiction.

We have  `hcontra : ∀ δ > 0, ∃ x, |x - a| < δ ∧ ε ≤ |f(x) - f(a)|`

Using `hcontra` we can choose a sequence `xₙ : ℕ → ℝ` satisfying

 (1) `|xₙ - a| < (n + 1)⁻¹` and (2) `ε ≤ |f(xₙ) - f(a)|`

 (We can do this by setting `δ = (n + 1)⁻¹` in `hcontra`)

We can show, using (1), that `xₙ → a` hence, by our initial assumption, `f(xₙ) → f(a)`.

But then we can prove the contradiction `ε < ε` using (2).
-/
-- # 10 marks
example : CtsAt f a ↔
∀ (x : ℕ → ℝ),  limₙ x a → limₙ (f ∘ x) (f a) :=
by
  sorry

/-
`OneGroup` is a Type with just one element. That element is called `OneGroup.one`.
-/
inductive OneGroup : Type
| one : OneGroup

open OneGroup -- we may now write `one` instead of `OneGroup.one`.

/-
Define an instance which allows us to write `1` for the
only element of `OneGroup`.
-/
instance : One OneGroup := ⟨one⟩

/-
Define a group structure on OneGroup.
-/
instance : Group OneGroup where
  mul _ _         := 1
  mul_assoc _ _ _ := rfl
  one_mul _       := rfl
  mul_one _       := rfl
  inv _           := 1
  mul_left_inv _  := rfl



/-
From now on, we let `G` be an arbitrary group.
-/
variable [Group G]

/-
# 2 marks
Given any group `G`, define a group homomorphism from `OneGroup` to `G`.
-/
def oneHom : OneGroup →* G := sorry

/-
# 4 marks
Prove that `one_hom` is the only group homomorphism from `OneGroup` to `G`.
-/
lemma oneHom_unique : ∀ φ : OneGroup →* G, φ = oneHom :=
by
  sorry

/-
# 2 marks
Define a homomorphism `homOne` from `G` to `OneGroup`.
-/
def homOne : G →* OneGroup := sorry

/-
# 2 marks
Prove that `homOne` is the only homomorphism from `G` to `OneGroup`.
-/
lemma homOne_unique : ∀ φ : G →* OneGroup, φ = homOne :=
by
  sorry

/-
# 5 marks
Prove that if `G` has at least `2` elements, then there is
a function `f : OneGroup → G` which is not a group homomorphism.
-/
example (hG : ∃ x y : G, x ≠ y) :
  ∃ f : OneGroup → G, ¬∃ φ : OneGroup →* G, f = φ :=
by
  sorry
