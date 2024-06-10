import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic
namespace Sheet3E
/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

open Finset
open scoped BigOperators


#check sum_range_succ -- ∑ i in range n.succ f i = ∑ i in range n, f i  + f n
/- Prove this generalized version of the triange inequality by induction. -/
-- 01
example (c : ℕ → ℝ) : |c n - c 0| ≤ ∑ i in range n, |c (i+1) - c i| :=
by
  sorry


/-   # field_simp
While the `ring` tactic works in fields (such as ℝ), it won't use facts that only
hold in a field. When working in a field we can also use the `field_simp` tactic. -/

-- 02
example (a : ℝ) (ha : a + 1 ≠ 0 ) : (a + 1) * (a + 1)⁻¹ = 1:=
by
  sorry

-- 03
example : ∑ n in range N, 1 / ((n+1)*(n+2) : ℝ) = N / (N+1) :=
by
  have partial_frac : ∀ n : ℕ, 1 / ((n+1)*(n+2) : ℝ) = 1/(n+1 : ℝ) - 1/(n+2 : ℝ)
  · intro n
    sorry
  induction N with
  | zero =>
    sorry
  | succ N ih =>
    sorry


/- Recall that if `s` is a Finset then `s.card` is the cardinality of s.
Note this can also be written `card s`-/

-- 04
example (s t : Finset ℕ)  : card (s ∪ t) + card (s ∩ t) = card s + card t :=
by
  sorry


#check add_le_add_right
/-
The next example is easy to solve using a `calc` block if you first find the
correct lemma from Mathlib.-/

-- 05
example (s t u : Finset ℕ) : (s ∪ t ∪ u).card ≤ s.card  + t.card + u.card :=
by
  calc
  _  ≤ (s ∪ t).card + u.card := by sorry
  _  ≤  _                    := by sorry

#check sum_le_sum -- if `f i ≤ g i` for all `i ∈ s` then `∑ i in s, f i ≤ ∑ i in s, g i`

-- 06
example (n : ℕ) (x y : ℕ → ℝ) :
|∑ i in range n, (x i + y i)| ≤ ∑ i in range n, |x i| + ∑ i in range n, |y i|:=by
calc
  _ ≤ ∑ i in range n, |x i + y i|      := by sorry
  _ ≤ ∑ i in range n, (|x i| + |y i|)  := by sorry
  _ = _                                := by sorry



def Bounded (x : ℕ → ℕ) : Prop := ∃ B, ∀ n, x n ≤ B

def EventuallyBounded (x : ℕ → ℕ) : Prop := ∃ B, ∃ N, ∀ n, N ≤ n → x n ≤ B


/- The next result is very similar to the proof in the video `E2_let`.

Look at that file for inspiration!

We recall some useful results -/

#check le_max_of_le_right
#check le_max_of_le_left
#check le_max'
#check mem_image
#check mem_range_succ_iff

-- 07
lemma Bounded_of_EventuallyBounded (h: EventuallyBounded x) : Bounded x :=
by
  sorry

end Sheet3E
