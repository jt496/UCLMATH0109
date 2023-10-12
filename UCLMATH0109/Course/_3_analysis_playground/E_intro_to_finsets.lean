import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
open Finset


/-
Finite sets, such as {0, 1, 2,..., n} have a special type in Lean.

They are called `Finsets`

If `s : Finset A` then `s` is a finite set of terms of type A

In many respects we can treat them like `Set A` but they are fundamentally different.


-/

#check Finset

/-
# TODO a basic set of examples with Finsets developing enough theory to do the next proof.
-/

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