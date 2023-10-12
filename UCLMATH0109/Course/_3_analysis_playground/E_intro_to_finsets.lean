import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice
open Finset

/-
Any convergent sequence `xₙ → a` is bounded by the maximum of its first 
N terms and |a| + 1 where N is given by setting ε = 1 in the
definition of `xₙ  → a`
-/

/-- Any convergent sequence is bounded  -/
theorem sLim_imp_bd (hx : limₙ x a) (n : ℕ): ∃ B, |x n| ≤ B :=
by
  obtain ⟨N, hN⟩ := hx 1 zero_lt_one
  let I : Finset ℕ := range N.succ
  have hne : I.Nonempty := ⟨0, mem_range_succ_iff.2 zero_le'⟩
  let J := I.image fun n => |x n|
  let B1 := J.max' (hne.image _)
  use max B1 (|a| + 1)
  by_cases hn : n ≤ N
  · apply le_max_iff.2 (Or.inl _)
    apply le_max'
    refine mem_image_of_mem (fun n => |x n|) ?H2.h
    exact mem_range_succ_iff.mpr hn
  · apply le_max_iff.2 (Or.inr _)
    have := hN n (lt_of_not_le hn).le;
    apply le_of_lt
    apply lt_add_of_sub_left_lt
    apply lt_of_le_of_lt _ this
    exact abs_sub_abs_le_abs_sub (x n) a 
