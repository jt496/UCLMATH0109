import Mathlib.Tactic

/-
Use the tactics described in _2_foundations/B_or_and_imp.lean
to complete the following proofs.
-/


-- 01 `∧` is symmetric
example (h : P ∧ Q) : Q ∧ P :=
by
  constructor
  · exact h.2
  · exact h.1

-- 02 `∨` is symmetric
example (h : P ∨ Q) : Q ∨ P :=
by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq


-- 03
example (h: (P ∨ Q) ∧ (P ∨ R)) : P ∨ (Q ∧ R):=
by
  obtain ⟨hpq, hpr⟩:=h
  cases hpq with
  | inl hp =>
    left
    exact hp
  | inr hq =>
    cases hpr with
    | inl hp =>
      left
      exact hp
    | inr hr =>
      right
      constructor
      · exact hq
      · exact hr


/-
Each of `∧, ∨, →` is a binary operation on `Prop` (Why?).

In order to understand compound propositions such as  `P ∧ Q → P ∧ R → P ∨ Q ∨ R`
(without using lots of brackets) we need to know how Lean parses such expressions.

Let's start with the single operation `→` and work out how Lean makes sense of the
expression: `P → Q → R`

There are two possiblities for how this could be defined:

  **left-associative**, so `P → Q → R` would be defined as `(P → Q) → R` or
  **right-associative**, so `P → Q → R` would be defined as `P → (Q → R)`?

But which is it?

You will face many similar situations and the key to deciphering such
expressions is to use the `#check` command and/or the `Infoview`.
-/
variable (P Q R S : Prop)
#check (P → Q) → R -- (P → Q) → R : Prop
#check P → (Q → R) -- P → Q → R : Prop -- Look no brackets!
/-
So `→` is right-associative, since when we add brackets on the right Lean
removes them in the Infoview. This tells us that they were not required.
-/
#check P → (Q → (R → S)) -- P → Q → R → S : Prop

-- 04 `→` is transitive
theorem imp_is_trans : (P → Q) → (Q → R) → (P → R):=
by
-- We can `intro` multiple terms at the same time
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

/-
Our last proof was a `theorem` rather than an `example` so what's the difference?

An `example` is anonymous (i.e. it has no name) so we can't refer to it.
A `theorem` needs to have a name (and it must be unique)

(We can also have a `lemma` which, as far as Lean is concerned, is a theorem.)

With a theorem or lemma we can use `#check` to see what its statement says.
-/
#check imp_is_trans
/-
In our next example our goal is to prove `P → Q → P ∧ Q`.

Since this involves two binary operations, `→` and `∧`, we have another potential
source of confusion.

If you can't see why there could a possible problem, consider the sum

    `2 + 4 + 6 / 3 = 8`

We know this evaluates to `8` because of the BIDMAS rules which say that you do `/`
before `+` (formally we say `/` has **higher precedence** than `+`).

We don't usually write `2 + 4 + (6 / 3) = 8` because the brackets are not needed
once you know the rules of BIDMAS.

Lean follows the same basic convention. Each binary operation is either left- or
right-associative, and it also has a value associated to it that allows Lean to know
which to do first (i.e. the operation with the higher value has higher precedence).

So which has higher precedence `→` or `∧`? Again, we can work it out systematically.

This time we will use the Infoview (rather than #check)
-/
-- 05
example : P → Q → P ∧ Q:=
by
/-
Click here. Now move you cursor to hover over the Infoview.
The goal is `⊢ P → Q → P ∧ Q`
If you hover over the `∧` in the goal you will see that the drop-down
information says `P ∧ Q : Prop`, so there are implied brackets `(P ∧ Q)`.

We deduce that Lean gives `∧` higher precedence than `→` (it did `∧` first).

If you now hover over each of the `→` symbols in the goal you can deduce that Lean
parses this expression as `P → (Q → (P ∧ Q))`

Lean follows the convention that it only displays brackets if they are required
(i.e. if they change the default meaning of an expression)
-/
  intro hp hq
  constructor
  · exact hp
  · exact hq

/-
In the next example our goal is `⊢ P ∨ Q ∨ R` so we first need to know whether
`∨` is left- or right-associative.
-/

-- 06
example (hpq: P ∨ Q) (hqr: Q ∨ R) : P ∨ Q ∨ R :=
by -- Place your cursor here and then hover over the
-- two `v` symbols in the Infoview goal `⊢ P ∨ Q ∨ R`
-- Can you work out where the brackets should go?
  cases hpq with
  | inl hp =>
    left
    exact hp
  | inr hq =>
    cases hqr with
    | inl hq =>
      right
      left
      exact hq
    | inr hr =>
      right
      right
      exact hr

variable (P Q R : Prop)
-- So `∨` is right-associative
#check P ∨ (Q ∨ R) -- P ∨ Q ∨ R : Prop
/-
Most of the binary operations you will have seen previously are associative:
for example `1 + (2 + 3) = (1 + 2) + 3` in `ℕ` and `a*(b*c) = (a*b)*c` in a group.

In fact `∨` and `∧` are both associative, but these are theorems not definitions!
-/
-- 07 `v` is associative
theorem or_is_assoc : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R):=
by
  constructor
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left; exact h
      | inr h =>
        right;left;
        exact h
    | inr h =>
      right
      right
      exact h
  · intro hpqr
    cases hpqr with
    | inl hp =>
      left
      left
      exact hp
    | inr hqr =>
      cases hqr with
      | inl hq =>
        left
        right
        exact hq
      | inr hr =>
        right
        exact hr


/-
  `∧` is also defined to be right-associative
-/
#check P ∧ (Q ∧ R) -- P ∧ Q ∧ R : Prop


-- 08'  `∧` is associative
theorem and_is_assoc : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R):=
by
  constructor
  · intro hpqr
    obtain ⟨hpq,hr⟩:=hpqr
    obtain ⟨hp,hq⟩:=hpq
    constructor
    · exact hp
    · constructor
      · exact hq
      · exact hr
  · intro hpqr
    obtain ⟨hp,hqr⟩:=hpqr
    obtain ⟨hq,hr⟩:=hqr
    constructor
    · constructor
      · exact hp
      · exact hq
    · exact hr

-- The last proof was quite long, but can be shortened as follows:
-- 08'
theorem and_is_assoc' : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R):=
by
  constructor
  · -- we can combine the syntax of `intro` and `obtain` as follows:
    intro ⟨⟨hp,hq⟩,hr⟩ -- now have `hp : P` `hq : Q` `hr : R`
    exact ⟨hp,hq,hr⟩
  · intro ⟨hp,hq,hr⟩
    exact ⟨⟨hp,hq⟩,hr⟩

/-
The next example is something we will use a lot.

As mathematicians we have lots of theorems that say things
like `if P and Q  are both true then R is true`.

Typically in Lean we express this as the equivalent proposition:
`P → Q → R`
-/
-- 09
example : (P ∧ Q → R) ↔ (P → Q → R) :=
by
  constructor
  · intro h
    intro hp hq
    apply h
    --- Our goal is `⊢ P ∧ Q` and we have `hp : P` and `hq : Q`
    --- Rather than using `constructor` we can use `exact ⟨hp,hq⟩`
    --- (This is like `obtain` but in reverse)
    exact ⟨hp,hq⟩
  · intro hpqr ⟨hp,hq⟩ -- we can use the `obtain` syntax in an `intro`
    apply hpqr hp hq


-- 10
example : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R):=
by
  constructor
  · intro hpqr
    constructor
    · intro hp
      apply hpqr
      left
      exact hp
    · intro hq
      apply hpqr
      right
      exact hq
  · intro ⟨hpr,hqr⟩ hpq
    cases hpq with
    | inl hp => apply hpr hp
    | inr hq => apply hqr hq
