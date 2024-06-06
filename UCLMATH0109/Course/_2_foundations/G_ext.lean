import Mathlib.Tactic
/-
# Functions: fun => notation

We have already seen how to define functions using tactics, however it
will be useful to also know the function notation that Lean uses to display
functions in the Infoview.
-/

-- tactic definition
def double1 : ℕ → ℕ :=
by
  intro n
  exact 2 * n

-- fun => notation
def double2 : ℕ → ℕ := fun n => 2 * n

-- As far as Lean is concerned these are identical
#print double1
#print double2


-- 01 Since the definitions of these functions agree the proof of equality is easy-/
example : double1 = double2 :=
by
  sorry

/-
# Extensionality

What does it mean to say that two functions `f g : A → B` are equal?

`Function extensionality` is the principle that `f = g` iff `∀a, f a = g a`

Equality of functions does not require their internal definitions to be identical, they
simply need to agree on all inputs.

The Lean tactic we need is `ext`
-/

def double3 : ℕ → ℕ := fun n => n + n

-- 02
example : double3 = double1 :=
by
  ext x
  rw [double3,double1,two_mul]

def f : ℕ → ℕ := fun n => 2 * n + 1

def g : ℕ → ℕ := fun n => 1 + n*2

-- 03
example : f = g :=
by
  ext x
  rw [f,g]
  rw [mul_comm,add_comm]


/-
Extensionality applies to many other mathematical objects, such as ℚ, ℂ, matrices and polynomials.

We will focus on the example of sets.

# Sets

If `A : Type` then we can form the type of subsets of A, called `Set A`

Two sets are equal iff they contain exactly the same elements.

Applying the `ext` tactic allows us to prove set identities using the tactics introduced to
prove basic results in logic.
-/

-- 04
example (A : Type) (s t: Set A) (heq : ∀x, x ∈ s ↔ x ∈ t) : s = t :=
by
  ext; apply heq

/-
If `x : A` and `s t : Set A` then `x ∈ s` is the Prop `x is a member of s`

Proving set identities is just logic in disguise.

    `x ∈ s ∪ t` is `x ∈ s ∨ x ∈ t`
    `x ∈ s ∩ t` is `x ∈ s ∧ x ∈ t`
    `x ∉ s` is `¬ x ∈ s` which is `x ∈ s → False`
    `x ∈ sᶜ` is another way of writing `x ∉ s`
    `x ∈ s \ t` is `x ∈ s ∧ x ∉ t`

    `s ⊆ t` is `∀x, x ∈ s → x ∈ t`

Note that `A` is not a term of type `Set A`. We use `univ` to refer to
the `Set A` that is `all of A`. We also have the empty set `∅`

    `x ∈ univ` is the Prop `True`
    `x ∈ ∅` is the Prop `False`
-/

-- 05
example (A : Type) (s t : Set A) : s ∪ t = t ∪ s :=
by
  ext x
  constructor
  · intro hst
    cases hst with
    | inl h =>
      right; exact h
    | inr h =>
      left; exact h;
  · sorry

-- 06
example (A : Type) (s t : Set A): s ∩ t = t ∩ s:=
by
  ext
  constructor
  · intro hx; exact ⟨hx.2,hx.1⟩
  · intro hx; exact ⟨hx.2,hx.1⟩


-- 07
example (A : Type) (s t u : Set A) (hst : s ⊆ t) (htu: t ⊆ u) : s ⊆ u :=
by
  intro x hx
  apply htu
  apply hst
  exact hx

open Set
-- 07
example (A : Type) (x : A) :  x ∈ univ :=
by
  trivial

/-
You might think all empty sets are the same, but Lean would disagree.

In the next example Lean can't infer the type of `∅` so we need to tell it
by writing `(∅ : Set A)`
-/
-- 08
example (A : Type) (x : A) (hx : x ∈ (∅ : Set A)) : False :=
by
  exact hx


-- 09
example (A : Type) (s : Set A) : s ∩ univ = s  :=
by
  ext a
  constructor
  · intro h
    sorry
  · sorry

/-
Recall the `by_cases` tactic.
-/
-- 10
example (A : Type) (s : Set A) : s ∪ sᶜ = univ:=
by
  ext x
  constructor
  · intro
    trivial
  · intro
    by_cases hs : x ∈ s
    · left
      exact hs
    · right
      exact hs


/-
Now try sheet2G.lean
-/
