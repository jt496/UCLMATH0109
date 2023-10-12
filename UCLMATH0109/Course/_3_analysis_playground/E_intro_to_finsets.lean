import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

variable (A B : Type)
/-
Finite sets, such as {0, 1, 2,..., n} have a special type in Lean.

They are called `Finsets`

If `s : Finset T` then `s` is a finite set of terms of type T

In many respects we can treat them like `Set T` but they are fundamentally different.
-/

#check Finset

/-
A `Finset` has an underlying description as a `List`. But this shouldn't be important
when working with them in most situations.

(Ignore the next paragraph unless you really want to understand the gory details.

A `List T` is an ordered sequence of terms of type T, e.g. `[0,1,0,2,3] : List ℕ`

We can define an equivalence relation on `List T`, by `l ∼ k` iff there is a permutation mapping 
the elements of `l` to `k` by reordering. 

So for example `[1, 3, 4, 3] ∼ [3, 3, 4, 1]`.

A `Finset T` is the equivalence class under `∼` of a `List T` that has no duplicate elements.)
-/

-- Note we  `open` the `Finset` namespace so that we can write `range` instead of `Finset.range` etc.
open Finset
#reduce range 5 -- {0, 1, 2, 3, 4} 


/-
# TODO a basic set of examples with Finsets developing enough theory to do the next proof.
-/

example (n : ℕ) : range n ⊆ range n.succ  :=
by
  apply range_mono
  exact Nat.le_succ n

/-
One obvious use of Finsets is for finite sums.
In order to be able to use ∑ notation we need to `open scoped BigOperators`
-/
example (a b c: ℕ) (h : 0 < a) (h1: a*b = a*c) : b =c :=
by
  exact Nat.eq_of_mul_eq_mul_left h h1


example (a b : ℕ) (h : 0 < a) : a*b/a = b:=
by
  exact Nat.mul_div_right b h

open scoped BigOperators

lemma sum_nat (n : ℕ) : 2*∑ i in range n.succ, i = n*(n+1):=
by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [sum_range_succ,mul_add,ih,Nat.succ_eq_add_one]
    ring

lemma sum_nat_sq (n : ℕ) : 6*∑ i in range n.succ, i^2 = n*(n+1)*(2*n+1):=
by
-- Try to mimic the previous proof
  sorry

/-
If `s : Finset A` and `f : A → B` then we can form the `Finset B` that is the image of s under f

This is the finite set `{f x | x ∈ s}`
-/

open Classical
lemma image_is (f : A → B) (s: Finset A) : x ∈ s.image f ↔ ∃ n ∈ s, f n = x :=
by
  exact mem_image

/-
A `Finset T` is nonempty if it contains an element.
Any nonempty finset in ℕ or ℝ will contain a min and a max, but 
-/

example (s : Finset A) (hx : x ∈ s) : s.Nonempty:=
by
  use x

example (s t: Finset A) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
--  cases hx -- fails since s, t are Finsets not Sets
  rw [mem_union] at hx
  cases hx with
  | inl h => 
    left; use x
  | inr h => 
    right; use x
 

/-
Any convergent sequence `xₙ → a` is bounded by the maximum of its first 
N terms and |a| + 1 where N is given by setting ε = 1 in the
definition of `xₙ → a`
-/


/-- Any convergent sequence is bounded  -/
theorem sLim_imp_bd (hx : limₙ x a) (n : ℕ): ∃ B, |x n| ≤ B :=
by
  obtain ⟨N, hN⟩ := hx 1 zero_lt_one
  let I : Finset ℕ := range N.succ
  have hne : I.Nonempty := nonempty_range_succ
  let J := I.image (fun n => |x n|)
  let B1 := J.max' (hne.image _)
  use max B1 (|a| + 1)
  apply le_max_iff.2
  by_cases hn : n ≤ N
  · left
    apply le_max'
    apply mem_image_of_mem (fun n => |x n|)  <| mem_range_succ_iff.2 hn
  · right
    apply le_add_of_sub_left_le
    apply le_of_lt
    apply lt_of_le_of_lt <| abs_sub_abs_le_abs_sub (x n) a 
    exact hN n (le_of_not_le hn)