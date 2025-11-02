import Mathlib.Tactic


-- 01 (1 mark)
example (P Q : Prop) : P ∧ Q ∧ ¬ P → ¬ Q := by
  intro ⟨_, _, _⟩
  contradiction

-- 02 (1 mark)
example (a b c : ℕ) (h : b ≤ a) : a - b + c = c + a - b:= by
  rw [add_comm, Nat.add_sub_assoc h c]

-- 03 (2 marks)
example (n : ℕ) : n = 0 ∨ ∃ k : ℕ, k < n := by
  cases n with
  | zero =>
    left
    rfl
  | succ n =>
    right
    use 0, Nat.zero_lt_succ _


-- 04 (3 marks)
example (n : ℕ) (P : ℕ → Prop) (h₁ : ∀ k, P (2 * k) → P (2 * k + 1)) :
    P (6 * n) → P (6 * n + 1) := by
  specialize h₁ (3 * n)
  rwa [←mul_assoc] at h₁

-- 05 (3 marks)
lemma helper (n : ℕ) : 2 * (n + 1) - 1 = 2 * n + 1 := by
  rfl

def oddSquares : ℕ → ℕ
| 0 => 0
| n + 1 => 3 * (2 * n + 1)^2 + oddSquares n

/- 06  (4 marks)
State and prove the theorem that for any `n : ℕ`,
 `oddSquares n = n * (2 * n - 1)*(2 * n + 1)`.
-/
lemma oddSq_eq (n : ℕ) : oddSquares n = n * (2 * n - 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    --- in order to get rid of the awkward subtraction we need to do the case `n = 1` separately
    cases n with
    | zero => rfl
    | succ n =>
      rw [helper, oddSquares, ih, helper]
      ring

/-- A function `f : ℝ → ℝ` is continuous at `a : ℝ` iff ... -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε


-- 07 (6 marks)
example (n : ℕ) : Cts (fun x => x ^ n) 0 := by
  intro e he
 --- the case `n = 0` is easy and different to `n ≠ 0`
  cases n with
  | zero =>
    use e, he, by norm_num [he]
  | succ _ =>
    -- we can take `δ = ε` unless `ε > 1` in which case we use `δ = 1`
    use min e 1
    constructor
    · apply lt_min he zero_lt_one
    · intro x hx
      norm_num at hx ⊢
      calc
        _ ≤ |x|   := pow_le_of_le_one (abs_nonneg _) hx.2.le (Nat.succ_ne_zero _)
        _ < _     := hx.1
