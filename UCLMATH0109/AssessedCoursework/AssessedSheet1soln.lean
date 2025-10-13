import Mathlib.Tactic
/-

  # Assessed Sheet 1

-/

-- Questions on functions and `Type`s
-- 01
example (α : Type) : α → α → α :=by
  intro _ a
  exact a

-- 02
example (α β γ : Type) (f : α → β) (g : β → γ) : α → γ :=by
  intro a
  exact g (f a)

-- 03
example (α β α' β' : Type) (f : α → α') (g : β' → β) : (α' → β') → (α → β) :=by
  intro f' a
  exact g (f' (f a))

-- 04
example (α β γ : Type) : (α → β → γ → γ) → (γ → α → β → β ) → (β → γ → α → α) :=by
  intro _ _ _ _ a
  exact a

-- 05 Fill in the first sorry in this example to be a function from `α` to `β` and then complete it
example (α β γ : Type) (f : α → γ) (g : γ → β) : α → β :=by
  intro a
  exact g (f a)

-- Questions on `Prop`s
-- 06
example (P : Prop) : P → P → P :=by
  intro _ hp
  exact hp

-- Rather than repeating `P Q R : Prop` etc in every question, we can declare them as variables here.
variable (P Q R : Prop)

-- 06
example : P ∧ Q ∧ R → R ∧ P :=by
  intro ⟨hp, _, hr⟩
  exact ⟨hr, hp⟩


-- 07
example : P ∨ Q ∨ R → ¬P → R ∨ Q :=by
  intro h hp
  cases h with
  | inl _ => contradiction
  | inr h =>
    cases h with
    | inl _ => right; assumption
    | inr _ => left; assumption

-- 08 Fill in the first sorry to state `not (not (not P)) implies not P` then complete the proof.
example : ¬¬¬ P → ¬ P :=by
  intro h3p _
  apply h3p
  intro _
  contradiction

-- 09
example : ¬(P ∨ ¬Q) ∨ R → (Q → P → R) :=by
  intro h _ hp
  cases h with
  | inl h =>
    push_neg at h
    obtain ⟨_,_⟩ := h
    contradiction
  | inr h => exact h

-- 10
example : P → P ∧ P ∨ P :=by
  intro hp
  right; exact hp

-- 11
example : P ∧ Q ∧ R → Q ∧ R ∧ P :=by
  intro ⟨hp, hq, hr⟩
  exact ⟨hq, hr, hp⟩

-- 12
example : P → Q → P ∧ Q → True :=by
  intro _ _ _
  trivial

-- 13 State and prove `P and False` implies `Q`
example : P ∧ False → Q :=by
  intro ⟨_,_⟩
  contradiction

-- Questions on quantifiers
-- 14
example : ∃ n : ℕ, 3 * n = 12 :=by
  use 4

-- 15
example (a : X) : ∃ x, x = a :=by
  use a

-- 16
example : ∃ n : ℕ, ∀ m, n ≠ m + 1 :=by
  use 0
  intro _ _
  contradiction

-- 17
example : ¬∃ n : ℕ, ∀ m, n ≠ m :=by
  push_neg
  intro n
  use n

-- 18
example (P : ℕ → Prop) (h₂ : ∀ n, P n → P (2 * n)) (h₁ : P 1) : P 32 :=by
  exact h₂ 16 (h₂ 8 (h₂ 4 (h₂ 2 (h₂ 1 h₁))))



-- 19 State and prove: `for every natural number n there exists a natural number m that n < m`
-- (To complete the proof you could use `exact Nat.lt_add_one n` which says that `n < n + 1`)
example : ∀ n : ℕ, ∃ m : ℕ, n < m :=by
  intro n
  use n + 1
  exact Nat.lt_add_one n

-- 20
example (P : ℕ → Prop) (h : ¬∃ n, ∀ a b, n < a → n < b → P a → P b ) :
  ∀ n, ∃ m, n < m ∧ (P n ↔ ¬P m) :=by
  intro n
  push_neg at h
  obtain ⟨a, b, ha, hb , hpa, hpb⟩ := h n
  by_cases h : P n
  · use b, hb
    constructor
    · intro _
      assumption
    · intro _
      assumption
  · use a, ha
    constructor
    · intro _
      contradiction
    · intro _
      contradiction
