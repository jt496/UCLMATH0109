import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

variable (A B : Type)
/-
Finite sets, such as {0, 1, 2,..., n} have a special type in Lean.

They are called `Finsets`

If `s : Finset T` then `s` is a finite set of terms of type T

In many respects we can treat them like `Set T`.
-/

variable (s t : Finset ℕ) (n : ℕ)
variable (f : ℕ → ℝ)

-- The standard set notation is still valid 
#check n ∈ s         
#check s ⊆ t
#check s ∩ t
#check s ∪ t
#check s \ t

-- We  `open` the `Finset` namespace so that we can write `range` instead of `Finset.range` etc.

open Finset 

#check Disjoint s t     -- s ∩ t = ∅
#check s.Nonempty       -- ∃x , x ∈ s

#check range n          -- {0,1,...,n-1} as a Finset ℕ
#check ({n} : Finset ℕ) -- {n} as a Finset
#check insert n s       -- s ∪ {n}
#check s.erase n        -- s \ {n}
#check s.image f        -- {f x | x ∈ s}

#check s.card           -- |s|

-- In general there is no `univ : Finset T` (unless `T` is itself finite) similiarly there is no `sᶜ`.

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

#reduce range 5 -- {0, 1, 2, 3, 4} 

example (n : ℕ) : range n ⊆ range n.succ  :=
by
  apply range_mono
  exact Nat.le_succ n

/-
One obvious use of Finsets is for finite sums and products.
In order to be able to use ∑ and ∏ notation we need to `open scoped BigOperators`
-/
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


lemma prod_zero (s : Finset ℕ) : ∏ a in s, a = 0 → 0 ∈ s:=
by
  intro h
  obtain ⟨x,hx0,hx1⟩:= prod_eq_zero_iff.1 h
  rwa [hx1] at hx0

  

/-
If `s : Finset A` and `f : A → B` then we can form the `Finset B` that is the image of s under f

This is the finite set `{f x | x ∈ s}`
-/


lemma image_is (f : ℕ → ℝ) (s: Finset ℕ) : x ∈ s.image f ↔ ∃ n ∈ s, f n = x :=
by
  exact mem_image

/-
A `Finset T` is Nonempty if it contains an element.
-/

example (s : Finset A) (hx : x ∈ s) : s.Nonempty:=
by
  use x

/-
We can use standard set notation with Finsets.
-/

example (s t: Finset ℝ) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
--  cases hx -- fails since s, t are Finsets not Sets
  rw [mem_union] at hx
  cases hx with
  | inl h => 
    left; use x
  | inr h => 
    right; use x


example (s t : Finset ℕ) : (s ∩ t).Nonempty → s.Nonempty ∧ t.Nonempty :=
by
  rintro ⟨x,hx⟩
  rw [mem_inter] at hx
  exact ⟨⟨x,hx.1⟩,⟨x,hx.2⟩⟩

/-- The image of a Nonempty set is Nonempty -/
example (s : Finset ℕ) (hne: s.Nonempty) (f: ℕ → ℝ) : Nonempty (s.image f):=
by
  obtain ⟨x,hxs⟩:=hne
  use f x
  exact mem_image_of_mem f hxs


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
For simplicity we will usually use max'
-/

/--Every `s : Finset ℕ` is bounded above, but the proof depends on whether or
not s is Nonempty -/
example (s : Finset ℕ) : ∃ n , ∀ x ∈ s, x ≤ n :=
by
  by_cases s.Nonempty
  · -- Since s is nonempty it has a max'
    use s.max' h
    intro n hn
    exact le_max' s n hn
  · -- Since s is empty it is trivially bounded above by 0
    use 0
    intro n hn
    exfalso
    apply h;
    use n

/-
An arbitrary union of finite sets need not be finite, but a finite union of finite sets is always finite. 

If `S : A → Finset B` and `I : Finset A` then `I.biUnion S` is the finite union of the Finsets indexed by I.
-/

example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) : x ∈ I.biUnion S ↔  ∃ i∈ I, x ∈ (S i):=
by
  exact mem_biUnion

/-
The cardinality of `s : Finset T` is `s.card`

The cardinality of a finite disjoint union of finite sets is the sum of the cardinalities of the sets.
-/

example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) (hdisj: ∀ i, i ∈ I → ∀j, j ∈ I → i ≠ j → Disjoint (S i) (S j)) : 
(I.biUnion S).card  = ∑ i in I, (S i).card :=
by
  exact card_biUnion hdisj


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