import Mathlib.Tactic

/-!

# Propositions

The following are all examples of propositions:

`1 + 1 = 2`, `3 + 3 < 5`,
`∀n, ∃ p₁ p₂, such that p₁ and p₂ are prime and 2n = p₁ + p₂` 

Much of pure mathematics is concerned with stating and proving propositions.

The main goal of this course is to learn how to express the statements and proofs
of propositions in Lean.


# Prop - Lean for proposition

`Prop` is the type of mathematical statements (propositions). 

So `(P : Prop)` is Lean for `P is a proposition`.

This means that `P` is a valid mathematical statement which may be true or false. 


# Proof of (P : Prop) is (hp : P)

If `(P : Prop)` then a proof of P in Lean is a term `hp` of type `P`, 
ie `(hp : P)`. 
-/

example (P : Prop) (hp : P) : P :=
by
  exact hp


/-
# Logical connectives

We will want to build new propositions from old. 

If `P` and `Q` are propositions then 

  `P or Q`
  `P and Q` 
  `P implies Q`        
  `not P`

are also propositions. 

We will now introduce all of the basic logical connectives and their
associcated Lean notation and tactics.

# Or : P ∨ Q (tactics: left / right / cases)

The proposition `P or Q` is written `P ∨ Q`. 
 
 `P ∨ Q` is true iff P is true or Q is true.

If our goal is `⊢ P ∨ Q` then we can close this by giving a proof of
 `P` or a proof of `Q`. 

We indicate which by using `left` for `P`and `right` for Q.
-/

example (P Q : Prop) (hp : P) : Q ∨ P :=
by
  right
  exact hp


example (hq : Q) : Q ∨ P :=
by
  sorry


/-
Given `hpq : P ∨ Q` in the local context we can use `cases hpq with hp hq` 
to constructor our goal into two subgoals, one in which `hp : P` and the other
in which `hq : Q`
-/

example (hpq : P ∨ Q) : Q ∨ P :=
by
  cases hpq with
  | inl h => 
    right
    exact h
  | inr h => 
    sorry


/-
# And : P ∧ Q (tactics: constructor / dot notation)
 
The proposition `P and Q` is written `P ∧ Q`. 

`P ∧ Q` is true iff P and Q are both true.

To prove `P ∧ Q` we need to supply proofs of both `P` and `Q`.

The `constructor` tactic converts the goal `⊢ P ∧ Q` into two goals `⊢ P` and `⊢ Q` 

We can then use ` · ` to focus on each goal in turn.
-/

example (hp : P) (hq: Q) : P ∧ Q:=
by
  constructor
  · exact hp
  · exact hq
/-

If we have a hypothesis `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`

We can also use `obtain ⟨hp,hq⟩:=h` to convert `h: P ∧ Q` into `hp : P` and `hq : Q`  

-/

example (h: P ∧ Q) : Q ∧ P :=
by
  obtain ⟨hp, hq⟩ :=h
  constructor
  · exact hq 
  · exact hp

/-
# Implies: P → Q  (tactics: intro / apply)

If `P` and `Q` are both Props then Lean uses function notation `P → Q` for the
proposition `P implies Q`.  This may look strange at first but it makes perfect sense when
 we consider what we mean by `P implies Q` and how functions work.

 `P implies Q` means that whenever we have a proof of P we can obtain a proof of Q. 

A function `f : P → Q` is just a rule for converting any term `hp : P` into a term `f hp`
type Q, `f hp : Q`.

When `P` and `Q` are Props, `hp : P` means that `hp` is a proof of P so `f` is a rule 
for converting proofs of P into proofs of Q. 

In Lean, if our goal is `P → Q`, then we can start our proof with `intro hp`, which
introduces the hypothesis `hp : P`  into the local context, ie we assume P 
is true.
-/

example : P ∧ Q → P :=
by
  intro hpq
  exact hpq.1

/-
Given a proof of `P implies Q` and a proof of `P` we can deduce that `Q` is also true.

In Lean if we have a hypothesis `h : P → Q` in the local context and our goal is `⊢ Q`
 then we can use `apply h` to change our goal to `⊢ P`.
-/

example (P Q : Prop) (hpq : P → Q) (hp : P) : Q :=
by
  apply hpq
  exact hp


/-
# If and only if (iff) : P ↔ Q (tactics: constructor / obtain / dot notation)

Lean notation for `P iff Q` is `P ↔ Q`. This means that `P` and `Q` are equivalent
(ie they have the same truth value).

We can treat `P ↔ Q` like an `and` statement. 

If our goal is `⊢ P ↔ Q` then `constructor` will convert this into two goals: `⊢ P → Q` and `⊢ Q → P`

We can use `obtain ⟨hpq,hqp⟩:=h` to convert `h : P ↔ Q` into `hpq: P → Q` and `hqp : Q → P`

If we have `h: P ↔ Q` in the local context then `h.1 : P → Q` and `h.2 : Q → P`

-/

example : (P ↔ Q) ↔ (P → Q) ∧ (Q → P):=
by
  constructor
  · intro hpq 
    constructor
    · exact hpq.1
    · exact hpq.2
  · sorry
/-
# Now do sheet2B.lean 
-/
