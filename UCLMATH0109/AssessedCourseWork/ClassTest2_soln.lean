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
lemma tends_to_zero : limₙ (fun n => (n + 1)⁻¹) 0 :=
by
  intro ε hε
  obtain ⟨N,hN⟩: ∃ (N:ℕ),  ε⁻¹ < N:= by exact exists_nat_gt ε⁻¹
  use N
  intro n hn
  rw [sub_zero, abs_of_pos Nat.inv_pos_of_nat, inv_lt _ hε]
  · apply  hN.trans
    norm_cast
    exact Nat.lt_succ.2 hn
  · norm_cast
    exact Nat.succ_pos n


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
  constructor
  · intro h x hx ε hε
    obtain ⟨d,hd1,hd2⟩:= h ε hε
    obtain ⟨N,hN⟩:= hx d hd1
    use N
    intro n hn
    apply hd2 _ <| hN _ hn
  · intro h
    intro ε hε
    by_contra hcontra
    push_neg at hcontra
    let x : ℕ → ℝ
    · intro n
      specialize hcontra (n + 1)⁻¹ (Nat.inv_pos_of_nat)
      exact hcontra.choose
    have x_spec: ∀ n, |x n - a| < ((n : ℝ) + 1)⁻¹ ∧ ε ≤ |f (x n) - f a|
    · intro n ; exact (hcontra (n + 1)⁻¹ (Nat.inv_pos_of_nat)).choose_spec
    have hxa : limₙ x a
    · intro μ hμ
      obtain ⟨K,hK⟩:= tends_to_zero μ hμ
      use K
      intro n hn
      simp only [sub_zero] at hK
      apply (x_spec _).1.trans
      convert hK n hn using 1
      rw [abs_of_pos Nat.inv_pos_of_nat]
    obtain ⟨M,hM⟩:= h x hxa ε hε
    apply lt_irrefl ε (lt_of_le_of_lt (x_spec M).2 (hM M le_rfl))




inductive OneGroup : Type
| one : OneGroup

namespace OneGroup

instance : One OneGroup := ⟨one⟩

instance : Group OneGroup where
  mul _ _         := 1
  mul_assoc _ _ _ := rfl
  one_mul _       := rfl
  mul_one _       := rfl
  inv _           := 1
  mul_left_inv _  := rfl

/-
# 2 marks
Given any group `G`, define a group homomorphism from `OneGroup` to `G`.
-/
def oneHom [Group G] : OneGroup →* G := {
    toFun := 1
    map_one' := rfl
    map_mul' := by
      intro x y
      dsimp
      simp
  }

/-
# 4 marks
Prove that `one_hom` is the only group homomorphism from `OneGroup` to `G`.
-/
lemma oneHom_unique [Group G] : ∀ φ : OneGroup →* G, φ = oneHom :=
by
  intro φ
  ext x
  cases x with
  | one =>
    rw [map_one]
    rfl

/-
# 2 marks
Define a homomorphism `homOne` from `G` to `OneGroup`.
-/
def homOne [Group G] : G →* OneGroup := {
  toFun := 1
  map_one' := rfl
  map_mul' := by tauto
}


/-
# 2 marks
Prove that `homOne` is the only homomorphism from `G` to `OneGroup`.
-/
lemma homOne_unique [Group G] : ∀ φ : G →* OneGroup, φ = homOne :=
by
  intro
  tauto

/-
# 5 marks
Prove that if `G` has at least `2` elements, then there is
a function `f : OneGroup → G` which is not a group homomorphism.
-/
example [Group G] (hG : ∃ x y : G, x ≠ y) :
  ∃ f : OneGroup → G, ¬∃ φ : OneGroup →* G, f = φ :=
by
  obtain ⟨x, y, hxy⟩ := hG
  contrapose! hxy
  obtain ⟨φ,hφ⟩ := hxy (fun _ ↦ x)
  obtain ⟨ψ,hψ⟩ := hxy (fun _ ↦ y)
  calc
    x = φ 1 := by rw [←hφ]
    _ = 1   := by simp
    _ = ψ 1 := by simp
    _ = y   := by rw [←hψ]
