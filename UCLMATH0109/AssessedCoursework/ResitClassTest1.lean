import Mathlib.Tactic
open Nat
/-
The are 6 questions in this test, with a total of 26 marks.
-/
-- # 1. (3 marks)
example (P Q : Prop) : (P ↔ Q) ↔ (¬Q ↔ ¬P) := by
  sorry

-- # 2. (3 marks)
example (P Q R : Prop): (P → Q ∨ R) ∧ (P ∧ ¬ Q) → R :=by
  sorry

#print Symmetric  -- A relation S is symmetric iff `∀ x y, S x y → S y x`
#print AntiSymmetric -- A relation S is antisymmetric iff `∀ x y, S x y → S y x → x = y`

-- # 3. (3 marks)
example  (R S : α → α → Prop) (hRS : ∀ x y, R x y → S x y) (Ssymm : Symmetric S) (Santi : AntiSymmetric S) :
    R x y → x = y := by
  sorry

@[reducible]
def EventuallyConstant (x : ℕ → ℝ) := ∃ N, ∃ C, ∀ n, N ≤ n → x n = C

lemma EventuallyConstant_def (x : ℕ → ℝ) : EventuallyConstant x ↔ ∃ N, ∃ C, ∀ n, N ≤ n → x n = C := by rfl

-- # 4. (3 marks)
/-- The constant sequence is eventually constant -/
lemma EventuallyConstant_of_constant (C : ℝ) : EventuallyConstant (fun _ => C) := by
  sorry

-- # 5. (5 marks)
/-- the product of two eventually constant sequences is eventually constant -/
lemma EventuallyConstant_mul (hx : EventuallyConstant x) (hy : EventuallyConstant y) :
    EventuallyConstant (x * y) := by
  sorry

-- # 6. (9 marks)
/-- Any sequence that is eventually constant is bounded above. -/
lemma Bounded_of_EventuallyConstant (x : ℕ → ℝ) (hx : EventuallyConstant x) :
    ∃ B, ∀ n, x n ≤ B:= by
  obtain ⟨N,C,hC⟩:= hx
  induction N generalizing x C with
  | zero =>
    sorry
  | succ N ih =>
    sorry
