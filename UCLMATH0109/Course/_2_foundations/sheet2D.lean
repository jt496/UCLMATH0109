import Mathlib.Tactic

variable (A: Type) (P Q R: A → Prop)
-- 01
example : (∀x, ∃y, P y → P x) :=
by
  intros x
  use x 
  intro hx
  exact hx


-- 02
example (h : ∃ x, ¬ P x) : ¬ ∀ a, P a:=
by
  intro hf
-- In the same way that `h : P ∧ Q` consists of two things, 
-- a proof of P and a proof of Q, so `∃x, P x` consists of two
-- things `x` and a proof of `P x`.  
  obtain ⟨x,hx⟩:=h 
  apply hx
  apply hf


/-
We used the tactic `push_neg` to push negations inside a goal.

We can also use this to simplify a negated hypothesis `h : ¬ P` 
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
  constructor
  · apply hrp
  · intro hpa
    specialize hpq a
    sorry
/-
If our hypothesis is `h: ∃x, ∃y,...` then `cases h with x hx` will give us `x` and
 `hx : ∃y ,...` we can then do `cases hx with y hy`.

If our goal is `⊢ ∃y, ∃x, ...` we can first tell Lean what to use for `y` and then the 
goal will change to `⊢ ∃ x,...`  so we can then tell it what to use for `x` -/
-- 05 
example  (h : ∃x, ∃y, P x → P y) : (∃x, ∃y, P y → P x):=
by
  obtain ⟨x , hx⟩:=h
  obtain ⟨y,hxy⟩:= hx
  use y
  use x 


-- 06
example : (∀ x, P x) → (∃x,¬ Q x) → ∃ (a b : A), ¬ (P a → Q b):=
by
  intros hp hq  
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
example : ¬∃ b, ∀ a, C b a ↔ ¬ C a a :=
by
  intro hb
  sorry

