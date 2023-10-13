import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

variable (α β : Type)
/-
Finite sets, such as {0, 1, 2,..., n} have a special type in Lean.

They are called `Finsets`

If `s : Finset α` then `s` is a finite set of terms of type T

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
-- #check sᶜ -- fails since the complement of a `Finset ℕ` is never finite

-- We  `open` the `Finset` namespace so that we can write `range` instead of `Finset.range` etc.

open Finset 

#check Disjoint s t     -- s ∩ t = ∅
#check s.Nonempty       -- ∃x , x ∈ s

#check range n          -- {0,1,...,n-1} as a Finset ℕ
#check ({n} : Finset ℕ) -- {n} as a Finset ℕ
#check insert n s       -- s ∪ {n}
#check s.erase n        -- s \ {n}
#check s.image f        -- {f x | x ∈ s}

#check s.card           -- |s| the number of elements in s

-- In general there is no `univ : Finset α` (unless `α` is itself finite) similiarly there is no `sᶜ`.

/-
A `Finset α` has an underlying description of the set as a `List α`. But this shouldn't be important
when working with them in most situations.

[Ignore the rest of this comment unless you really want to understand the details.]

A `List α` is an ordered sequence of terms of type α, e.g. `[0,1,0,2,3] : List ℕ`

We can define an equivalence relation on `List T`, by `l ∼ k` iff there is a permutation mapping 
the elements of `l` to `k` by reordering. 

So for example `[1, 3, 4, 3] ∼ [3, 3, 4, 1]`.

A `Finset α` is the equivalence class under `∼` of a `List α` that has no duplicate elements.
-/

#reduce range 5 -- {0, 1, 2, 3, 4} 

example (n : ℕ) : range n ⊆ range n.succ  :=
by
  apply range_mono
  exact Nat.le_succ n

/-
One obvious use of Finsets is for finite sums and products.

In order to be able to use ∑ and ∏ notation we need to `open scoped BigOperators`

If `s` is a `Finset α`, and `f : α → β` a function then
  `∑ i in s, f i`  is the sum of `f` over `s`,

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

/-- If a product of natural numbers is zero then one of the terms is zero -/
lemma prod_zero (s : Finset ℕ) : ∏ a in s, a = 0 → 0 ∈ s:=
by
  intro h
  obtain ⟨x,hx0,hx1⟩:= prod_eq_zero_iff.1 h
  rwa [hx1] at hx0

/-- If f (n+1) = g (n+1) - g(n), then the sum of f over {0,1,...,n} is g(n+1)- g(0) -/
lemma sum_cancel (hf: ∀ n, f n = g (n+1) - g n) : ∑ i in range n.succ, f i = g (n+1) - g 0 :=
by
  induction n with
  | zero => 
    rw [sum_range_one, hf 0]
  | succ n ih =>
    rw [sum_range_succ,← Nat.succ_eq_add_one, ih, hf n.succ]
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

/-- If x ∈ s ∪ t then s is nonempty or t is nonempty -/
example (s t: Finset ℝ) (hx : x ∈ s ∪ t) : s.Nonempty ∨ t.Nonempty :=
by
--  cases hx -- fails since s, t are Finsets not Sets
  rw [mem_union] at hx
  cases hx with
  | inl h => 
    left; use x
  | inr h => 
    right; use x

/-- If s ∩ t is nonempty then s and (t ∪ u) are not disjoint -/
example (s t u: Finset ℕ) : (s ∩ t).Nonempty → ¬ Disjoint s (t ∪ u)  :=
by
  intro ⟨x,hx⟩
  apply not_disjoint_iff_nonempty_inter.2
  use x
  rw [mem_inter] at *
  refine ⟨hx.1,?_⟩
  apply mem_union_left _ hx.2

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

If `S : α → Finset β` and `I : Finset α` then `I.biUnion S` is the finite union of the Finsets indexed by I.
-/

example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) : x ∈ I.biUnion S ↔  ∃ i∈ I, x ∈ (S i):=
by
  exact mem_biUnion

/-
The cardinality of `s : Finset T` is `s.card`
-/


/--The cardinality of a finite union of pairwise disjoint finite sets is the sum of 
  the cardinalities of the sets.-/
example (S : ℕ  → Finset ℕ ) (I : Finset ℕ) (hdisj: ∀ i, i ∈ I → ∀j, j ∈ I → i ≠ j → Disjoint (S i) (S j)) : 
(I.biUnion S).card  = ∑ i in I, (S i).card :=
by
  exact card_biUnion hdisj


/-- A simple but often useful bound on a sum as product of bound on size of terms and number of terms -/
example (s : Finset ℕ) (hf: ∀n, n ∈ s → f n ≤ b) : ∑ n in s, f n ≤ s.card * b:=
by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
  apply sum_le_sum
  convert hf
  rw [Nat.cast_one,one_mul]

/--
Any convergent sequence `xₙ → a` is bounded by the maximum of its first 
N terms and |a| + 1 where N is given by setting ε = 1 in the
definition of `xₙ → a`
-/
theorem sLim_imp_bd (hx : limₙ x a) (n : ℕ): ∃ B, |x n| ≤ B :=
by
-- Get N : ℕ from definition of limit with ε = 1
  obtain ⟨N, hN⟩ := hx 1 zero_lt_one
-- Let I ={0,1,...,N}
  let I : Finset ℕ := range N.succ
-- I is Nonempty
  have hne : I.Nonempty := nonempty_range_succ
-- J = {x 0, x 1,... ,x N} the image of I under x
  let J := I.image (fun n => |x n|)
-- Let B1 = max J (exists since J is a Nonempty Finset ℕ)
  let B1 := J.max' (hne.image _)
-- We use the bound B = max B1 (|a| + 1) (note this is the max of a pair of Nats)
  use max B1 (|a| + 1)
-- |x n| is always ≤ either B1 or (|a| + 1) depending on n
  apply le_max_iff.2
-- Do the case split on `n ≤ N` or not
  by_cases hn : n ≤ N
  · left
  -- In this case |x n| ≤ B1 because |x n| ∈ J 
    apply le_max'
  -- |x n| ∈ J since n ∈ I and J = I.image (fun n => |x n|)
    apply mem_image_of_mem (fun n => |x n|) 
  -- Now need to prove that n ∈ I which is true since n ≤ N 
    apply mem_range_succ_iff.2 hn
  · right
  -- In this case |x n| ≤ |a| + 1 because N ≤ n   
  -- We rearrange the goal to |x n| ≤ |a| + 1
    apply le_add_of_sub_left_le
  -- Since we will use hN which is < we will prove < which implies ≤
    apply le_of_lt
  -- We now use |x n| - |a| ≤ |x n - a |   
    apply lt_of_le_of_lt <| abs_sub_abs_le_abs_sub (x n) a
  -- Finally hN implies the result since N ≤ n 
    exact hN n (le_of_not_le hn)