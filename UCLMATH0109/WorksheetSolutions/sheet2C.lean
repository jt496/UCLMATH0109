import Mathlib.Tactic

-- 01 De Morgan's 1st law
example : ¬ (P ∨ Q) ↔  ¬P ∧ ¬ Q:=
by
  constructor
  · intro hnpq
    constructor
    · intro hp; apply hnpq
      left; exact hp
    · intro hq
      apply hnpq
      right
      exact hq
  intro hnpq hpq
  obtain ⟨hnp,hnq⟩:=hnpq
  cases hpq with
  | inl hp =>
    contradiction
  | inr hq =>
    contradiction

/-
In the next two examples you will need to use `by_cases` in one of the two
implications
-/

-- 02 De Morgan's 2nd law (you will need to use `by_cases` in the first implication)
example : ¬ (P ∧ Q) ↔  ¬P ∨ ¬ Q:=
by
  constructor
  · intro hnpq
    by_cases hp : P
    · right
      intro hq
      apply hnpq
      exact ⟨hp,hq⟩
    · left; exact hp
  · intros h hpq
    cases h with
    | inl h =>
      apply h hpq.1
    | inr h =>
      apply h hpq.2


-- 03
example : (P → Q) ↔ Q ∨ ¬P:=
by
  constructor
  · intro hpq
    by_cases h : P
    · left
      apply hpq h
    · right
      exact h
  · intro hpnq hp
    cases hpnq with
    | inl h =>
      exact h
    | inr h =>
      contradiction


-- 04 this can be done without `by_cases` but only with perseverance...
example : ¬(P ↔ ¬P) :=
by
  intro h
  obtain ⟨h1,h2⟩:=h
  apply h1
  · apply h2
    intro hp
    apply h1 hp hp
  · apply h2
    intro hp
    apply h1 hp hp

-- 05 contrapositive (requires `by_cases` in our direction)
example : P → Q ↔ ¬ Q → ¬P :=
by
  constructor
  · intro hpq hnq hp
    apply hnq
    apply hpq hp
  · intro hnqnp hp
    by_cases h : Q
    · exact h
    · exfalso
      apply hnqnp h hp


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
  intro ⟨⟨hp,hnq⟩,_,hnr⟩
  exact ⟨hp,hnq,hnr⟩

-- 07
example (P Q : Prop): ((P → Q) → P) → P:=
by
  intro h
  by_cases hp: P
  · exact hp
  · apply h
    intro p
    contradiction

-- 08
example : ¬(P → Q) ↔ P ∧ ¬Q:=
by
  constructor
  · contrapose
    push_neg
    intro hpq hp
    apply hpq hp
  · intro ⟨hp,hnq⟩ hpq
    apply hnq (hpq hp)
