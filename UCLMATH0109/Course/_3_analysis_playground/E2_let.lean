import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice



open Finset

/--
Any convergent sequence `xₙ → a` is bounded by the maximum of {|x 0|,|x 1|, ... ,|x K|} 
and |a| + 1, where K is given by setting ε = 1 in the definition of `xₙ → a`
-/
theorem sLim_imp_bd (hx : limₙ x a) : ∃ B, ∀ n, |x n| ≤ B :=
by
-- Get K : ℕ from definition of limₙ x a with ε = 1
  obtain ⟨K, hK⟩ := hx 1 zero_lt_one
-- Let I = {0,1,...,K}
  let I := range K.succ
-- I is Nonempty
  have hne : I.Nonempty := by exact nonempty_range_succ
-- J = {|x 0|, |x 1|,... ,|x K|} the image of I under |x|
  let J := I.image |x|
-- Let B1 = max' J (exists since J is a Nonempty Finset ℕ)
  let B1 := J.max' (by exact Nonempty.image hne |x|) 
-- We use the bound B = max B1 (|a| + 1) (note this is the max of a pair of Nats)
  use max B1 (|a| + 1)
-- |x n| is always ≤ either B1 or (|a| + 1) depending on n
  intro n
  refine le_max_iff.mpr ?h.a
-- Do the case split on `n ≤ K` or not
  by_cases hn : n ≤ K 
-- In this case |x n| ≤ B1 because |x n| ∈ J 
  · left  
    apply le_max'
    -- |x n| ∈ J since n ∈ I and J = I.image (fun n => |x n|)
    refine mem_image_of_mem |x| ?_
    exact mem_range_succ_iff.mpr hn
-- Now need to prove that n ∈ I which is true since n ≤ K 
  · right
-- In this case |x n| ≤ |a| + 1 because K ≤ n   
-- We rearrange the goal to |x n| ≤ |a| + 1
    apply le_add_of_sub_left_le
-- Since we will use hK which is < we will prove < which implies ≤
    apply le_of_lt
-- We now use |x n| - |a| ≤ |x n - a |   
    apply lt_of_le_of_lt (by exact IsAbsoluteValue.sub_abv_le_abv_sub abs (x n) a)
-- Finally hK implies the result since K ≤ n 
    apply hK
    exact Nat.le_of_not_le hn
    