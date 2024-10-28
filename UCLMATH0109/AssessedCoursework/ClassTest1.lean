import Mathlib.Tactic
open Nat
/-
# In-class test : total 26 marks
-/


-- 01 (2 marks)
example (P Q : Prop) : Q → (Q ↔ P) → P:= by
  sorry

-- 02 (2 marks)
example (P Q R : Prop) :( P → Q → R) ∧ (P ∧ (Q ∨ R)) → R :=by
  sorry

#print Symmetric  -- A relation R is symmetric iff `∀ x y, R x y → R y x`
#print Transitive -- A relation R is transitive iff `∀ x y z, R x y → R y z → R x z`

-- 03 (3 marks)
example  (R S : α → α → Prop) (hswap : ∀ a b, R a b → S b a) (Rtrans : Transitive R)
  (Ssymm : Symmetric S) : (∃ y, R x y ∧ R y z) → S x z := by
  sorry

-- 04 (4 marks)
example (x y : ℕ) (h₁ : x + y = 5) (h₂ : 2 * x < y) : x = 0 ∨ x = 1 :=by
  sorry

def Lucas : ℕ → ℕ
| 0 => 2
| 1 => 1
| n + 2 => Lucas n + Lucas (n + 1)

lemma Lucas_step : Lucas (n + 2) = Lucas n + Lucas (n + 1) := by rfl

def Fibonacci : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => Fibonacci n + Fibonacci (n + 1)

lemma Fibonacci_step (n : ℕ) : Fibonacci (n + 2) = Fibonacci n + Fibonacci (n + 1) :=by
  rfl




#check twoStepInduction

-- 06 (3 marks)
lemma Lucas_Fibonacci (n : ℕ) : Lucas (n + 1) = Fibonacci n + Fibonacci (n + 2) := by
  induction n using twoStepInduction with
  | H1 => sorry
  | H2 => sorry
  | H3 n ih1 ih2 =>
    sorry

-- 07 (4 marks)
lemma Lucas_bound (n : ℕ) : Lucas n ≤ 2^(n + 1) := by
  sorry

def Bounded (x : ℕ → ℝ) := ∃ B, ∀ n, x n < B

lemma Bounded_iff (x : ℕ → ℝ) : Bounded x ↔ ∃ B, ∀ n, x n < B := by rfl

-- 07 (8 marks)
example (x : ℕ → ℝ) (h₁ : Monotone x) (h₂ : ¬ Bounded x) (ε : ℝ) (hε : 0 < ε) :
   ∃ N, ∀ n, N < n → |(x n)⁻¹| ≤ ε :=by
 sorry
