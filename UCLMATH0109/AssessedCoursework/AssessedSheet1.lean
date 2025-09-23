import Mathlib.Tactic
/-

  # Assessed Sheet 1

-/

-- Questions on functions and `Type`s
-- 01
example (α : Type) : α → α → α :=by
  sorry

-- 02
example (α β γ : Type) (f : α → β) (g : β → γ) : α → γ :=by
  sorry

-- 03
example (α β α' β' : Type) (f : α → α') (g : β' → β) : (α' → β') → (α → β) :=by
  sorry

-- 04
example (α β γ : Type) : (α → β → γ → γ) → (γ → α → β → β ) → (β → γ → α → α) :=by
  sorry

-- 05 Fill in the first sorry in this example to be a function from `α` to `β` and then complete it
example (α β γ : Type) (f : α → γ) (g : γ → β) : sorry :=by
  sorry

-- Questions on `Prop`s
-- 06
example (P : Prop) : P → P → P :=by
  sorry

-- Rather than repeating `P Q R : Prop` etc in every question, we can declare them as variables here.
variable (P Q R : Prop)

-- 06
example : P ∧ Q ∧ R → R ∧ P :=by
  sorry

-- 07
example : P ∨ Q ∨ R → ¬P → R ∨ Q :=by
  sorry

-- 08 Fill in the first sorry to state `not (not (not P)) implies not P` then complete the proof.
example : sorry :=by
  sorry

-- 09
example : ¬(P ∨ ¬Q) ∨ R → (Q → P → R) :=by
  sorry

-- 10
example : P → P ∧ P ∨ P :=by
  sorry

-- 11
example : P ∧ Q ∧ R → Q ∧ R ∧ P :=by
  sorry

-- 12
example : P → Q → P ∧ Q → True :=by
  sorry

-- 13 State and prove `P and False` implies `Q`
example : sorry :=by
  sorry

-- Questions on quantifiers
-- 14
example : ∃ n : ℕ, 3 * n = 12 :=by
  sorry

-- 15
example (a : X) : ∃ x, x = a :=by
  sorry

-- 16
example : ∃ n : ℕ, ∀ m, n ≠ m + 1 :=by
  sorry

-- 17
example : ¬∃ n : ℕ, ∀ m, n ≠ m :=by
  sorry

-- 18
example (P : ℕ → Prop) (h₂ : ∀ n, P n → P (2 * n)) (h₁ : P 1) : P 32 :=by
  sorry

#check Nat.lt_add_one -- ∀ (n : ℕ), n < n + 1

-- 19 State and prove: `for every natural number n there exists a natural number m that n < m`
-- (To complete the proof you could use `exact Nat.lt_add_one n` which says that `n < n + 1`)
example : sorry :=by
  sorry


-- 20
example (P : ℕ → Prop) (h : ¬∃ n, ∀ a b, n < a → n < b → P a → P b ) :
  ∀ n, ∃ m, n < m ∧ (P n ↔ ¬P m) :=by
  sorry
