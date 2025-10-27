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
      · intro hx
        apply h.2 -- h : x ∈ s \ t is `x ∈ s and x ∉ t` so `h.2` is `¬ (x ∈ t)`
        exact hx.2
    | inr h =>
      constructor
      · right
        exact h.1
      · intro ⟨hs,_⟩
        apply h.2 hs
  · intro ⟨h1,h2⟩
    cases h1 with
    | inl h =>
      left
      constructor
      · exact h
      · intro ht
        apply h2 ⟨h,ht⟩
    | inr h =>
      right
      constructor
      · exact h
      · intro hs
        apply h2 ⟨hs,h⟩


-- 02
example  (A : Type) (s t u: Set A) : (s ∪ t) ∪ u = s ∪ (t ∪ u):=
by
  ext x
  constructor
  · intro hstu
    cases hstu with
    | inl h =>
      cases h with
      | inl h => left; exact h
      | inr h => right; left; exact h
    | inr h => right; right; exact h
  · intro hstu
    cases hstu with
    | inl h =>
      left; left; exact h
    | inr h =>
      cases h with
      | inl h => left; right; exact h
      | inr h => right; exact h

/- Another way of proving that two sets are equal is to use the anti-symmetry of ⊆
 i.e. `A ⊆ B → B ⊆ A → A = B` -/
-- 03
example (A : Type) (s t: Set A) : s ∪ t = t ∪ s:=
by
  apply subset_antisymm
  · intro x hx
    cases hx with
    | inl h =>
      right; exact h
    | inr h =>
      left; exact h
  · intro x hx
    cases hx with
    | inl h => right; exact h
    | inr h => left; exact h

-- 04 intersection is right-distributive
example (A : Type) (s t u : Set A) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u):=
by
--You could use `ext` but can you guess the name for the one-line proof?
  exact union_inter_distrib_right s t u

-- 05 Remember we can also use `ext` to prove identities between functions
example (f g : ℝ → ℝ) (hf: ∀x, f x = 2 * g x) (hg: ∀ x, g x = 0) : f = g :=
by
  ext x
  rw [hf,hg,mul_zero]

-- `ext` also allows to prove equalities between other types, such as complex numbers, matrices, etc.
-- Here `z.re` and `z.im` are the real and imaginary parts of a complex number `z`
-- 06
example (z w : ℂ) (hre : z.re = w.re) (him : z.im = w.im) : z = w:=
by
  apply Complex.ext
  · exact hre
  · exact him


-- `ext` for matrices reduces the problem of proving two matrices are equal to proving that their elements agree
-- 07
example (M₁ M₂ : Matrix (Fin m) (Fin n) ℝ) (h : ∀ i j, M₁ i j = M₂ i j): M₁ = M₂ :=
by
  ext i j
  rw [h]

-- Sometimes `ext` does too much, for example if we want to prove that two complex matrices are equal
-- We can use `ext1` to apply one extensionality lemma at a time.
-- 08
example (M₁ M₂ : Matrix (Fin m) (Fin n) ℂ) (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ :=
by
  ext i j
  rw [h]
