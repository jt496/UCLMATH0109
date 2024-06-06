import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Basic

open Set

-- 01
example (A : Type) (s t: Set A) : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
by
  ext x
  constructor
  · intro h
    cases h with
    | inl h =>
      constructor
      · left; exact h.1
      · sorry
    | inr h =>
      sorry
  · sorry


-- 02
example  (A : Type) (s t u: Set A) : (s ∪ t) ∪ u = s ∪ (t ∪ u):=
by
  ext x
  sorry


/- Another way of proving that two sets are equal is to use the anti-symmetry of ⊆
 i.e. `A ⊆ B → B ⊆ A → A = B` -/
-- 03
example (A : Type) (s t: Set A) : s ∪ t = t ∪ s:=
by
  apply subset_antisymm
  · sorry
  · sorry

-- 04 intersection is right-distributive
example (A : Type) (s t u : Set A) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u):=
by
--You could use `ext` but can you guess the name for the one-line proof?
  sorry

-- 05 Remember we can also use `ext` to prove identities between functions
example (f g : ℝ → ℝ) (hf: ∀x, f x = 2 * g x) (hg: ∀ x, g x = 0) : f = g :=
by
  ext x
  sorry

-- `ext` also allows to prove equalities between other types, such as complex numbers, matrices, etc.
-- Here `z.re` and `z.im` are the real and imaginary parts of a complex number `z`
-- 06
example (z w : ℂ) (hre : z.re = w.re) (him : z.im = w.im) : z = w:=
by
  ext
  · sorry
  · sorry


-- `ext` for matrices reduces the problem of proving two matrices are equal to proving that their elements agree
-- 07
example (M₁ M₂ : Matrix (Fin m) (Fin n) ℝ) (h : ∀ i j, M₁ i j = M₂ i j): M₁ = M₂ :=
by
  ext i j
  sorry

-- Sometimes `ext` does too much, for example if we want to prove that two complex matrices are equal
-- We can use `ext1` to apply one extensionality lemma at a time.
-- 08
example (M₁ M₂ : Matrix (Fin m) (Fin n) ℂ) (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ :=
by
--  ext; -- this will apply extensionality recursively so goes further than we need
  ext1 i
  ext1 j
  sorry
