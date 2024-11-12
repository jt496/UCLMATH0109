import Mathlib.Tactic
open Nat
/-
# In-class test : total 26 marks
-/
-- 01 (2 marks)
example (P Q : Prop) : Q → (Q ↔ P) → P:= by
  intro hQ hQP
  apply hQP.1 hQ

-- 02 (2 marks)
example (P Q R : Prop) :( P → Q → R) ∧ (P ∧ (Q ∨ R)) → R :=by
  intro ⟨hpqr,hp,pqr⟩
  cases pqr with
  | inl hq => exact hpqr hp hq
  | inr hr => exact hr

#print Symmetric  -- A relation R is symmetric iff `∀ x y, R x y → R y x`
#print Transitive -- A relation R is transitive iff `∀ x y z, R x y → R y z → R x z`

-- 03 (3 marks)
example  (R S : α → α → Prop) (hswap : ∀ a b, R a b → S b a) (Rtrans : Transitive R)
  (Ssymm : Symmetric S) : (∃ y, R x y ∧ R y z) → S x z := by
  intro ⟨y,hrxy,hryz⟩
  apply Ssymm
  apply hswap
  apply Rtrans hrxy hryz


-- 04 (4 marks)
example (x y : ℕ) (h₁ : x + y = 5) (h₂ : 2 * x < y) : x = 0 ∨ x = 1 := by
  have : x ≤ 1 := by linarith
  exact le_one_iff_eq_zero_or_eq_one.mp this


def Lucas : ℕ → ℕ
| 0 => 2
| 1 => 1
| n + 2 => Lucas n + Lucas (n + 1)

lemma Lucas_step : Lucas (n + 2) = Lucas n + Lucas (n + 1) := by rfl

def Fibonacci : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => Fibonacci n + Fibonacci (n + 1)

lemma Fibonacci_step (n : ℕ) : Fibonacci (n + 2) = Fibonacci n + Fibonacci (n + 1) := by
  rfl


#check twoStepInduction

-- 05 (3 marks)
lemma Lucas_Fibonacci (n : ℕ) : Lucas (n + 1) = Fibonacci n + Fibonacci (n + 2) := by
  induction n using twoStepInduction with
  | H1 => rfl
  | H2 => rfl
  | H3 n ih1 ih2 =>
    rw [Lucas_step,ih1,ih2,Fibonacci_step (n+2),Fibonacci_step n]
    ring

-- 06 (4 marks)
lemma Lucas_bound (n : ℕ) : Lucas n ≤ 2^(n + 1) := by
  induction n using twoStepInduction with
  | H1 => rfl
  | H2 => decide
  | H3 n ih1 ih2 =>
    rw [Lucas_step]
    have h1: 2^(n+1) + 2^(n+2) = 2^(n+1) * 3 := by ring
    calc
    _ ≤ 2^(n+1) + 2^(n+2)   := Nat.add_le_add ih1 ih2
    _ = 2^(n+1) * 3         := by rw [h1]
    _ ≤ _                   := by rw [pow_succ _ (n+2),pow_succ _ (n+1)]; linarith

def Bounded (x : ℕ → ℝ) := ∃ B, ∀ n, x n < B

lemma Bounded_iff (x : ℕ → ℝ) : Bounded x ↔ ∃ B, ∀ n, x n < B := by rfl

-- 07 (8 marks)
example (x : ℕ → ℝ) (h₁ : Monotone x) (h₂ : ¬ Bounded x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, N < n → |(x n)⁻¹| ≤ ε :=by
  rw [Bounded_iff] at h₂
  push_neg at h₂
  obtain ⟨N,hN⟩ := h₂ ε⁻¹
  have hε': 0 < ε⁻¹ := inv_pos_of_pos hε
  have hnnoneg: ∀ n, N ≤ n → 0 < x n
  · intro n hn
    exact lt_of_lt_of_le hε' (hN.trans (h₁ hn))
  use N
  intro n hn
  calc
    _ = (x n)⁻¹   := by rw [abs_inv, abs_eq_self.mpr (hnnoneg n hn.le).le]
    _ ≤ ε         := inv_le_of_inv_le hε (hN.trans (h₁ hn.le))
