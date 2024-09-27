import Mathlib.Tactic
/-

  # Assessed Sheet 1

-/

-- Questions on functions and `Type`s
-- 01
example (A : Type) : A → A → A :=
by
  sorry

-- 02
example (A B C: Type) (f : A → B) (g : B → C) : A → C :=
by
  sorry

-- 03
example (A B A' B' : Type) (f : A → A') (g : B' → B) : (A' → B') → (A → B) :=
by
  sorry

-- 04
example (A B C : Type) : (A → B → C → C) → (C → A → B → B ) → (B → C → A → A) :=
by
  sorry

-- Questions on `Prop`s
-- 05
example (P : Prop) : P → P → P :=
by
  sorry

-- 06
example : P ∧ Q ∧ R → P ∧ R := by
  sorry

-- 07
example : P ∨ Q ∨ R → ¬Q → P ∨ R := by
  sorry

-- 08
example : ¬¬¬¬¬¬P → ¬¬P :=
by
  sorry

-- 09
example : ¬ (P ∨ ¬Q) ∨ R → (Q → P → R) :=
by
  sorry

-- 10
example : P → P ∧ P ∨ P :=
by
  sorry

-- 11
example : P ∧ Q ∧ R → Q ∧ R ∧ P :=
by
  sorry

-- 12
example : P → Q → P ∧ Q → True :=
by
  sorry

-- 13
example : P → Q ∨ P → False → Q :=
by
  sorry

-- Questions on quantifiers
-- 14
example : ∃ n : ℕ, 2*n = 10 :=
by
  sorry

-- 15
example (a : X) : ∃ x, x = a :=
by
  sorry

-- 16
example : ∃ n : ℕ, ∀ m, n ≠ m + 1 :=
by
  sorry

-- 17
example : ¬∃ n : ℕ, ∀ m, n ≠ m :=
by
  sorry

-- 18
example (P : ℕ → Prop) (h : ¬ ∃ n, ∀ a b, n < a → n  < b → P a → P b ) :
  ∀ n, ∃ m, n < m ∧ (P n ↔ ¬ P m) :=
by
  sorry
