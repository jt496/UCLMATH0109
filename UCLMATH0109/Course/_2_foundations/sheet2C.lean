import Mathlib.Tactic

-- 01 De Morgan's 1st law
example : ¬ (P ∨ Q) ↔  ¬P ∧ ¬ Q:=
by
  constructor
  · intro hnpq
    constructor
    · intro hp; apply hnpq
      left; exact hp
    · sorry
  intro hnpq hpq
  obtain ⟨hnp,hnq⟩:=hnpq
  cases hpq with
  | inl hp =>
    sorry
  | inr hq =>
    sorry

/-
In the next three examples you will need to use `by_cases` in one of the two
implications
-/

-- 02 De Morgan's 2nd law (you will need to use `by_cases` in the first implication)
example : ¬ (P ∧ Q) ↔  ¬P ∨ ¬ Q:=
by
  constructor
  · intro hnpq
    by_cases hp : P
    · sorry
    · sorry
  · intros h hpq
    sorry

-- 03
example : (P → Q) ↔ Q ∨ ¬P:=
by
  sorry

-- 04 this can be done without `by_cases`
example : ¬(P ↔ ¬P) :=
by
  sorry

-- 05 contrapositive
example : P → Q ↔ ¬ Q → ¬P :=
by
  sorry


/-
Lean has a built-in tactic `contrapose` that converts any goal `P → Q`
into its contrapositive

Lean also has a tactic `push_neg` for pushing negations inside expressions.

Remember this tactic for when we introduce quantifiers!
-/
-- 06
example (P Q R : Prop): (P → Q ∨ R) → (P → Q) ∨ (P → R):=
by
  contrapose
  -- Goal is: `⊢ ¬((P → Q) ∨ (P → R)) → ¬(P → Q ∨ R)`
  push_neg
  -- Goal is now : `⊢ (P ∧ ¬Q) ∧ P ∧ ¬R → P ∧ ¬Q ∧ ¬R`
  intro h
  sorry

-- 07
example (P Q : Prop): ((P → Q) → P) → P:=
by
  sorry

-- 08
example : ¬(P → Q) ↔ P ∧ ¬Q:=
by
  sorry
