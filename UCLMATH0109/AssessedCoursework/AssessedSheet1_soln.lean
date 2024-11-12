import Mathlib.Tactic
/-
# Assessed Sheet 1 Solutions
-/


-- Questions on functions and `Type`s
-- 01
example (A : Type) : A → A → A :=
by
  intro a _
  exact a

example (A : Type) : A → A → A :=
by
  exact fun a _ ↦ a

example (A : Type) : A → A → A :=
by
  exact fun _ ↦ id


-- 02
example (A B C: Type) (f : A → B) (g : B → C) : A → C :=
by
  intro a
  exact g (f a)

example (A B C: Type) (f : A → B) (g : B → C) : A → C :=
by
  exact g ∘ f

-- 03
example (A B A' B' : Type) (f : A → A') (g : B' → B) : (A' → B') → (A → B) :=
by
  intro h a
  exact g (h (f a))

-- 04
example (A B C : Type) : (A → B → C → C) → (C → A → B → B ) → (B → C → A → A) :=
by
  intro _ _ _ _ a
  exact a

example (A B C : Type) : (A → B → C → C) → (C → A → B → B ) → (B → C → A → A) :=
by
  intros
  assumption

-- Questions on `Prop`s
-- 05
example (P : Prop) : P → P → P :=
by
  intros
  assumption

-- 06
example : P ∧ Q ∧ R → P ∧ R := by
  intro h
  constructor
  · exact h.1
  · exact h.2.2

example : P ∧ Q ∧ R → P ∧ R := by
  intro ⟨hp,_,hr⟩
  exact ⟨hp,hr⟩

example : P ∧ Q ∧ R → P ∧ R := by
  exact fun h ↦ ⟨h.1,h.2.2⟩

-- 07
example : P ∨ Q ∨ R → ¬Q → P ∨ R := by
  intro h hnq
  cases h with
  | inl _ =>
    left
    assumption
  | inr h =>
    cases h with
    | inl _ => contradiction
    | inr _ => right; assumption

-- 08
example : ¬¬¬¬¬¬P → ¬¬P :=
by
  push_neg
  intro
  assumption

-- 09
example : ¬ (P ∨ ¬Q) ∨ R → (Q → P → R) :=
by
  intro h _ _
  cases h with
  | inl h =>
    push_neg at h
    obtain ⟨hnp,_⟩ := h
    contradiction
  | inr h =>
    exact h

-- 10
example : P → P ∧ P ∨ P :=
by
  intro
  right
  assumption

-- 11
example : P ∧ Q ∧ R → Q ∧ R ∧ P :=
by
  intro h
  constructor
  · exact h.2.1
  · constructor
    · exact h.2.2
    · exact h.1

example : P ∧ Q ∧ R → Q ∧ R ∧ P :=
by
  intro ⟨hp,hq,hr⟩
  exact ⟨hq,hr,hp⟩

example : P ∧ Q ∧ R → Q ∧ R ∧ P :=
by
  exact fun h ↦ ⟨h.2.1,h.2.2,h.1⟩



-- 12
example : P → Q → P ∧ Q → True :=
by
  intros
  trivial


-- 13
example : P → Q ∨ P → False → Q :=
by
  intros
  contradiction


-- Questions on quantifiers

-- 14
example : ∃ n : ℕ, 2*n = 10 :=
by
  use 5


-- 15
example (a : X) : ∃ x, x = a :=
by
  use a


-- 16
example : ∃ n :ℕ, ∀ m, n ≠ m + 1 :=
by
  use 0
  intro _ _
  contradiction

-- 17
example : ¬∃ n : ℕ, ∀ m, n ≠ m :=
by
  push_neg
  intro n
  use n


-- 18*
example (P : ℕ → Prop) (h : ¬ ∃ n, ∀ a b, n < a → n  < b → P a → P b ) :
  ∀ n, ∃ m, n < m ∧ (P n ↔ ¬ P m) :=
by
  push_neg at h
  intro n
  obtain ⟨a,b,hna,hnb,_,hpb⟩:=h n
  by_cases  P n
  · use b,hnb
    constructor; all_goals intro ; assumption
  · use a,hna
    constructor; all_goals intro; contradiction
