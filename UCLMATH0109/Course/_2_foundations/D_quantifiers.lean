import Mathlib.Tactic
variable (A : Type)
--variable (a b c : A)
variable (P Q : A → Prop)

/-
So far we have just been considering propositional logic. 

If want to define the limit of a sequence of real numbers, or the axioms of a group 
we need to be able to quantify over a type. 

Recall that if `A` and `B` are types then `A → B` is the type of functions
from A to B.

A `predicate` on a type A is a function `P : A → Prop`

So for each `a : A` we have a  `P a : Prop`.

Mathematics is full of predicates, for example `n is even` is a predicate on `ℕ`

# Quantifiers 

# Universal ∀ (tactics: intro / apply / specialize)

Given a predicate `P : A → Prop` the universal quantifier `∀x, P x` says that for 
every term x of type A, the proposition `P x` is true.

If we have `h : ∀a, P a` in the local context and our goal is `⊢ P b`, where `b : A`
 then `apply h` will close the goal. -/
 
-- 01
example (h : ∀a, P a) : P b:=
by
  apply h

/-
If we have the goal `⊢ ∀ x, Q x` then we can start our proof with `intro x`

If we want to use `h : ∀a, P a` for a particular value of `b : A`, then we can use 
`specialize h b` to change `h` to `h : P b`
-/
-- 02
example (hp : ∀a, P a) (hq : ∀a, Q a) : ∀x, (P x ∧ Q x) :=
by
  intro x
  specialize hp x 
  -- Now have `hp : P x` in the local context
  specialize hq x
  constructor 
  · exact hp
  · exact hq


/-
# Existential ∃  (tactics: use / obtain)

If `P : A → Prop` is a predicate, then the existential quantifier `∃x, P x` says that 
there exists a term x of type A, such that the proposition `P x` is true.

If our goal is `⊢ ∃x, P x`  and we know that `a : A` is a term satisfying `P a`
then we can tell Lean to `use a` to close the goal. 
-/
-- 03
example (x : A) (hx: P x) : ∃ a, P a:=
by
  use x 
 
/-
If we have `h : ∃x, P x` in the local context then `obtain ⟨x,hx⟩ := h`
will give us `x : A` and `hx : P x` in our local context.

[Notice how similar this is to `obtain ⟨hp,hq⟩ := h` when `h : P ∧ Q`]

-/
-- 04
example (h : ∃ a, P a) : ∃ b, P b ∨ Q b:=
by
  obtain ⟨a, ha⟩ := h
  -- Now have `a : A` and `ha : P a` in the local context
  use a
  left; exact ha



/-
# Negated quantifiers (tactics: push_neg / by_contra)

We saw that `push_neg` can simplify goals such as `⊢ ¬¬P`.

More generally we can use `push_neg` to move negations inside a goal.

We can also use it to simplify a hypothesis `h` with `push_neg at h`

Lean also has a proof by contradiction tactic: `by_contra h`, 
this takes the negation of the goal and adds it as a hypothesis to the 
local context and changes the goal to `False`
-/

-- 05
example (hpq: ∀x y, P x → Q y) : (∀z, Q z) ∨ (∀z,¬ P z) :=
by
  by_contra h 
  -- Goal is now `⊢ False`, and we have a new hypothesis
  -- `h : ¬((∀ (z : A), Q z) ∨ ∀ (z : A), ¬P z)` 
  -- We can simplify `h` by pushing the negation inside 
  push_neg at h
  -- Now have `h : (∃ (z : A), ¬Q z) ∧ ∃ (z : A), P z`
  obtain ⟨hq,hp⟩:=h
  obtain ⟨b, hb⟩:= hq
  obtain ⟨a, ha⟩:= hp
  apply hb (hpq a b ha)





/-
# Now do exercises in sheet2D.lean
-/