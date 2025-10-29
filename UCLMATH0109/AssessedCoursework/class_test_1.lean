import Mathlib.Tactic

-- 01  (1 mark)
example (P Q : Prop) : P ∧ Q ∧ ¬ P → ¬ Q := by
  sorry

-- 02 (1 mark)
example (a b c : ℕ) (h : b ≤ a) : a - b + c = c + a - b:= by
  sorry

-- 03  (2 marks)
example (n : ℕ) : n = 0 ∨ ∃ k : ℕ, k < n := by
  sorry

-- 04  (3 marks)
example (n : ℕ) (P : ℕ → Prop) (h₁ : ∀ k, P (2 * k) → P (2 * k + 1)) :
    P (6 * n) → P (6 * n + 1) := by
  sorry

-- 05 (3 marks)
lemma helper (n : ℕ) : 2 * (n + 1) - 1 = 2 * n + 1 := by
  sorry

-- 06  (4 marks)
def oddSquares : ℕ → ℕ
| 0 => 0
| n + 1 => 3 * (2 * n + 1)^2 + oddSquares n

/- State and prove the theorem that for any `n : ℕ`,
 `oddSquares n = n * (2 * n - 1)*(2 * n + 1)`. -/


/-- A function `f : ℝ → ℝ` is continuous at `a : ℝ` iff ... -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a| < δ → |f x - f a| < ε


-- 07 (6 marks)
example (n : ℕ): Cts (fun x => x ^ n) 0 := by
  sorry
