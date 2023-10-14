import UCLMATH0109.Course._3_analysis_playground.C_have
import Mathlib.Data.Finset.Lattice



open Finset


/-
Any convergent sequence `xₙ → a` is bounded, i.e. `∃ C, ∀ n, |x n| ≤ C`

We will prove this using Finsets.

Recall `xₙ → a` is `∀ ε, ε > 0 → ∃ K, ∀ n, K ≤ n → |x n - a | < ε`

An obvious way to prove the result is to set `ε = 1` and so obtain `K : ℕ` 
such that `∀ n, K ≤ n → |x n - a| < 1`, 

Let `B  = max' {|x 0|,...,|x K|}`  then we can set `C = max B (|a| + 1)`

To prove that `C` works we need to `intro n` and split `by_cases hn : n ≤ K`
-/


-- The following results may be useful to complete the proof

-- In the case `hn : n ≤ K`
#check le_max_of_le_left   
#check le_max'
#check mem_image_of_mem
#check mem_range_succ_iff

-- In the case `hn : ¬ n ≤ K` 
#check le_max_of_le_right 
#check lt_add_of_sub_left_lt
#check abs_sub_abs_le_abs_sub 






theorem sLim_imp_bd (hx : limₙ x a) : ∃ C, ∀ n, |x n| ≤ C :=
by
-- Get K : ℕ from definition of limₙ x a with ε = 1
  specialize hx 1
-- Let I = {0,1,...,K}

-- I is Nonempty

-- J = {|x 0|, |x 1|,... ,|x K|} the image of I under |x|

-- Let B = max' J (exists since J is a Nonempty Finset ℕ)

-- We use the bound C = max B (|a| + 1) (note this is the max of a pair of Nats)

-- |x n| is always ≤ either B1 or (|a| + 1) depending on n

-- Do a by_cases split on `n ≤ K` 
 
 -- In this case |x n| ≤ B1 because |x n| ∈ J 
 
 -- Now need to prove that n ∈ I which is true since n ≤ K 
  sorry
    