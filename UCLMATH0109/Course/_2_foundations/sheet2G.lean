import Mathlib.Tactic

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


--- Unions and Intersections of families of sets
open scoped BigOperators


-- 05
example (A ι : Type) (F : ι → Set A) (x : A) : x ∈ ⋃ i, F i ↔ ∃ i, x ∈ F i:=
by
  exact mem_iUnion
