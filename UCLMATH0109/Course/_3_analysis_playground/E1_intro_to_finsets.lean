import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

variable (α β : Type)
/-
Finite sets, such as {0, 1, 2,..., n} have a special type in Lean,
they are called `Finsets`.

If `s : Finset α` then `s` is a finite set of terms of type α.

In many respects we can treat them like `Set α`.
-/

variable (s t : Finset ℕ) (n : ℕ)
variable (f g : ℕ → ℝ)

-- Most standard set notation is still valid
#check n ∈ s
#check s ⊆ t
#check s ∩ t
#check s ∪ t
#check s \ t
--#check sᶜ -- fails since the complement of a `Finset ℕ` is never finite
-- In general there is no `univ : Finset α` (unless `α` is itself finite) similiarly there is no `sᶜ`.

-- We  `open` the `Finset` namespace so that we can write `range` instead of `Finset.range` etc.

open Finset

#check s.Nonempty       -- ∃x , x ∈ s
#check Disjoint s t     -- s ∩ t = ∅

#check range n          -- {0,1,...,n - 1} as a Finset ℕ
#check ({n} : Finset ℕ) -- {n} as a Finset ℕ
#check insert n s       -- s ∪ {n}
#check s.erase n        -- s \ {n}
#check s.image f        -- {f x | x ∈ s}

#check s.card           -- |s| the number of elements in s
--  We can `filter` a set to obtain the subset with a given property.
#check s.filter Even    -- { x | x ∈ s and x is even}


/-
A `Finset α` has an underlying description of the set as a `List α`. But this shouldn't be important
when working with them in most situations.

[Ignore the rest of this comment unless you really want to understand the details.]

A `List α` is an ordered sequence of terms of type α, e.g. `[0,1,0,2,3] : List ℕ`

We can define an equivalence relation on `List α`, by `l ∼ k` iff there is a permutation
mapping `l` to `k` by reordering.

For example, `[1, 3, 4, 3] ∼ [3, 3, 4, 1]`.

A `Finset α` is the equivalence class under `∼` of a `List α` together with a proof
that it has no duplicate elements.
-/

#reduce range 5 -- {0, 1, 2, 3, 4}

/- {0,1,..,a - 1} ⊆ {0,1,..,b - 1} -/
example (a b : ℕ) (h: a ≤ b) : range a ⊆ range b  :=
by
  exact range_subset.mpr h

/-
One obvious use of Finsets is for finite sums and products.

In order to be able to use ∑ and ∏ notation we need to `open scoped BigOperators`

If `s` is a `Finset α`, and `f : α → β` a function then
  `∑ i ∈ s, f i`  is the sum of `f` over `s`,
-/
open scoped BigOperators

/-- 2 * (0 + 1 + 2 + ... + n) = n * (n + 1) -/
lemma sum_nat (n : ℕ) : 2 * ∑ i ∈ range n.succ, i = n * (n + 1):=
by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [sum_range_succ,mul_add, ih]
    ring


/-- 6 * (0² + 1² + 2² + ... + n²) = n * (n + 1) * (2 * n + 1)-/
lemma sum_nat_sq (n : ℕ) : 6 * ∑ i ∈ range n.succ, i^2 = n * (n + 1) * (2 * n + 1):=
by
-- Try to mimic the previous proof
  sorry

/-- If a product of a finite set of natural numbers is zero then one of its elements is zero -/
lemma prod_zero (s : Finset ℕ) (h : ∏ a ∈ s, a = 0 ) : ∃ x, x ∈ s ∧ x = 0:=
by
  exact prod_eq_zero_iff.mp h


/-- If f (n) = g (n + 1) - g(n), then the sum of f over {0,1,...,n} is g(n+1)- g(0) -/
lemma sum_cancel (hf: ∀ n, f n = g (n+1) - g n) : ∑ i ∈ range n.succ, f i = g (n+1) - g 0 :=
by
  induction n with
  | zero =>
    rw [sum_range_one, hf]
  | succ n ih =>
    rw [sum_range_succ, ih, hf]
    ring


/-
If `s : Finset α` and `f : α → β` then `s.image f` is the `Finset β` that is the
image of s under f i.e. the finite set `{f x | x ∈ s}`
-/
lemma image_is (f : ℕ → ℝ) (s: Finset ℕ) : x ∈ s.image f ↔ ∃ n ∈ s, f n = x :=
by
  exact mem_image

/-
A `s : Finset α` is Nonempty if it contains an element i.e. `∃ x, x ∈ s`
-/
example (s : Finset α) (hx : x ∈ s) : s.Nonempty:=
by
  use x

/-
We can use standard set notation with Finsets, but we no longer have the direct
correspondance between set and logic notation.
-/

/-- If x ∈ s ∪ t then s is Nonempty or t is Nonempty -/
example (s t: Finset ℝ) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
--  cases hx -- fails since s and t are Finsets not Sets
  rw [mem_union] at hx
  cases hx with
  | inl h =>
    left
    use x
  | inr h =>
    right
    use x



/-- If s ∩ t is nonempty then s and (t ∪ u) are not disjoint -/
example (s t u: Finset ℕ) : (s ∩ t).Nonempty → ¬ Disjoint s (t ∪ u)  :=
by
  intro h
  refine Nonempty.not_disjoint ?_
  apply h.mono
  refine inter_subset_inter_left ?h
  exact subset_union_left
  -- If you check the definition of `Disjoint` it doesn't look very helpful but
  -- a theorem relating `Disjoint a b` and `Nonempty (a ∩ b)` can easily be found
  -- apply?


/-- The image of a Nonempty set is Nonempty -/
example (s : Finset ℕ) (hne: s.Nonempty) (f : ℕ → ℝ) : (s.image f).Nonempty:=
by
  exact Nonempty.image hne f

/-
There are two different `maximum` functions defined for `s : Finset P` when `P` is
any LinearOrder such as `ℕ` or `ℝ`
-/
#check Finset.max'
-- this requires a proof that s is Nonempty and then returns a value in `P`
#check Finset.max
-- this returns a value in `WithBot P` which we can think of as `P` with an extra
-- element that is < everything in `P`.

/-
We will use `max'` for now.
-/

/--Every `s : Finset ℕ` is bounded above, but the proof depends on whether or
not s is Nonempty -/
example (s : Finset ℕ) : ∃ n , ∀ x ∈ s, x ≤ n :=
by
  by_cases h : s.Nonempty
  · -- Since s is Nonempty it has a max'
    use s.max' h
    exact fun x a => le_max' s x a
  · -- Since s is empty it is trivially bounded above by 0
    use 0
    intro x hx
    exfalso
    apply h
    use x

/-
An arbitrary union of finite sets need not be finite, but a finite union of finite sets is always finite.

If `S : α → Finset β` and `I : Finset α` then `I.biUnion S` is the finite union of the Finsets indexed by I.
-/

example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) : x ∈ I.biUnion S ↔  ∃ i ∈ I, x ∈ (S i):=
by
  exact mem_biUnion

/-
The cardinality of `s : Finset α` is `s.card`
-/


/--The cardinality of a finite union of pairwise disjoint finite sets is the sum of
  the cardinalities of the sets.-/
example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) (hdisj: ∀ i, i ∈ I → ∀j, j ∈ I → i ≠ j → Disjoint (S i) (S j)) :
(I.biUnion S).card  = ∑ i ∈ I, (S i).card :=
by
  exact card_biUnion hdisj

/-- If f is bounded above by b on s then the sum of f over s is at most |s| * b -/
example (s : Finset ℕ) (f : ℕ → ℕ) (hf: ∀n, n ∈ s → f n ≤ b) : ∑ n ∈ s, f n ≤ s.card * b:=
by
  rw [card_eq_sum_ones, sum_mul, one_mul]
  exact sum_le_sum hf
