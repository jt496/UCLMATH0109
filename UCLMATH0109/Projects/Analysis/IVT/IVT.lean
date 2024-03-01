import Mathlib.Tactic
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Cts
open UCL

/-
In this project we formalise a standard (1st year analysis) proof of the Intermediate Value Theorem

If f is continuous on [a,b], a < b and f(a) < c < f(b) then there exists d ∈ (a,b) such that f(d) = c


We do this from first principles, (i.e. without using any results from Mathlib.Topology)

We use a standard definition of continuity (given below) and our proof is the obvious one:

Suppose that f is cts on [a,b], with a < b and f(a) < c < f(b)

Let S := {x | x ∈ [a,b] and f(x) < c}. We prove that S is nonempty and bounded above and
hence has a supremum. In Lean this is called `sSup S`. We then prove that f(sSup S) = c.

Work out *all* the details on paper before you start.

-/

open Nat Set

#print CtsOn  -- Standard definition of continuity on a set.
#print CtsOn' -- It may be is easier to use CtsOn' in the proof of the IVT

lemma CtsOn_iff_CtsOn'  : CtsOn f s ↔ CtsOn' f s :=
by
  sorry

#check sub_pos
#check lt_min
#check abs_sub_lt_iff
#check sub_lt_sub_iff_left
#check sub_lt_comm

#check Real.sSup_def
#check upperBounds
#check le_csSup
#check csSup_le
#check not_mem_of_csSup_lt

/-- The intermediate value theorem -/
theorem intermediate_value (hf : CtsOn f (Icc a b)) (hab : a < b) (hfab : f a < c ∧ c < f b) :
    ∃ x, x ∈ Ioo a b ∧ f x = c :=
by
  sorry


theorem fixed_point (hf : CtsOn f (Icc a b)) (hab : a < b) (hr: f '' (Icc a b) = Icc a b) : ∃ x, f x = x :=
by
  sorry

/-
Possible extension: prove the following result.
-/
theorem root (hcts : CtsOn f (Icc (-1 : ℝ) 1)) (hfm1 : f (-1 : ℝ) = 0) (hfp1 : f 1 = 0) (c d : ℕ) : ∃ x, x ∈ Ioo (-1 : ℝ) 1 ∧ f x = x^(2*c + 1) /(1 - x^(d+1)):=
by
  sorry
