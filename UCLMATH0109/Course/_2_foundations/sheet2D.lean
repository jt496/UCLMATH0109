import Mathlib.Tactic

variable (A: Type) (P Q R: A → Prop)

-- 01
example : (∀x, ∃y, P y → P x) :=
by
  intro x
  sorry

-- 02
example (h : ∃ x, ¬ P x) : ¬ ∀ a, P a:=
by
  sorry


/-
We used the tactic `push_neg` to push negations inside a goal.

We can also use it to simplify a negated hypothesis `h : ¬ P` 
with `push_neg at h`
-/

-- 03 
example (h : ¬ ∀ a, ¬P a)  : ∃ x, P x:=
by
  push_neg at h 
  sorry

-- 04 
example : (∀ x, P x → Q x) → (∀y, Q y → R y) → (∀z, R z → P z) → (∀a, R a ↔ P a):=
by
  intro hpq hqr hrp a
  sorry
  
/-
If our hypothesis is `h: ∃x, ∃y,...` then `obtain ⟨x, y, hxy⟩ := h` will give us `x` and `y` 

If our goal is `⊢ ∃y, ∃x, ...` we can first tell Lean what to use for `y` and then the 
goal will change to `⊢ ∃ x,...`  so we can then tell it what to use for `x`
-/
-- 05 
example  (h : ∃x, ∃y, P x → P y) : (∃x, ∃y, P y → P x):=
by
  sorry

-- 06
example : (∀ x, P x) → (∃x, ¬ Q x) → ∃ (a b : A), ¬ (P a → Q b):=
by
  sorry

-- 07
example: (∃x, ¬Q x) → (∃ y, Q y) → 
  ∃ a b, ∀ z, P z → Q a ∧ ¬(P z → Q b) :=
by
  sorry

-- 08 
example : (∀x, ∃y, ¬(P x → P y)) → (∃u, P u) →   (∃v, ¬ P v) :=
by
  sorry

-- 09
example : (¬∀a, (P a → Q a)) ↔ ∃x, (¬Q x ∧ P x):=
by
  sorry

variable (C : A → A → Prop)
-- 10 The no barber theorem 
-- Hint : Use `by_cases` on something..
example : ¬∃ b, ∀ a, C b a ↔ ¬ C a a :=
by
  intro hb
  sorry
