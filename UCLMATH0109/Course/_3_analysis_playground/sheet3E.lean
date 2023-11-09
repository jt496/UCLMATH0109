import Mathlib.Data.Finset.Lattice
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

open Finset
open scoped BigOperators

/-
Prove this generalized version of the triange inequality by induction.
01 -/
example (c : ℕ → ℝ) : |c n - c 0| ≤ ∑ i in range n, |c (i+1) - c i| :=
by
  sorry


/-
Prove the following formula
for the partial sums of the series `∑ (1 / ((n+1) * (n+2)))`.
You may find it helpful to prove the `have` statement first.
02 -/
example : ∑ n in range N, 1 / ((n+1)*(n+2) : ℝ) = N / (N+1) :=
by
  have partial_frac : ∀ n : ℕ, 1 / ((n+1)*(n+2) : ℝ) = 1/(n+1 : ℝ) - 1/(n+2 : ℝ)
  · sorry
  sorry

/- Recall that if `s` is a Finset then `s.card` is the cardinality of s.
Note this can also be written `card s`
03 -/
example (s t : Finset ℕ)  : card (s ∪ t) + card (s ∩ t) = card s + card t :=
by
  sorry

/-
The next example is easy to solve using a `calc` block if you first find the
correct lemma from Mathlib.
(To do this you could introduce a `have` statement and use `apply?`.)
04 -/
example (s t u : Finset ℕ) : (s ∪ t ∪ u).card ≤ s.card  + t.card + u.card :=
by
  sorry

/-
For this example first prove it on paper: `apply?` with the correct `have` statements
or in a `calc` block should do it.
05 -/
example (s t : Finset ℕ) (f : ℕ → ℕ) (hs : ∀ i, i ∈ s → f i ≤ n) (ht: ∀ i, i ∈ t → f i ≤ 2*n) :
∑ i in s ∪ t, f i ≤ n * s.card + 2 * n * (t \ s).card :=
by
  have hu: s ∪ t = s ∪ (t \ s) := by sorry
  have hD: Disjoint s (t \ s) := by sorry
  -- try setting out a `calc` block to complete this
  sorry

/-
06 -/
example (n : ℕ) (x y : ℕ → ℝ) :
|∑ i in range n, (x i + y i)| ≤ ∑ i in range n, |x i| + ∑ i in range n, |y i|:=by
calc
  _ ≤ ∑ i in range n, |x i + y i|      := by sorry
  _ ≤ ∑ i in range n, (|x i| + |y i|)  := by sorry
  _ = _                                := by sorry


/-
Ico a b is the closed/open interval [a, b)
If `a b : ℕ` this is `{a,a+1, ..., b-1}
-/

#check mem_Ico
#check sub_zero
#check abs_mul
/- If limₙ xₙ = 0 and ∀ n, |yₙ| ≤ |zₙ * xₙ| then
`∃ N, ∀ M, ∑ i in [N,M), |y i| ≤ ∑ i in [N,M), |z i|`
07 -/
example  (y z : ℕ → ℝ) (hx : limₙ x 0) (hle : ∀ i, |y i| ≤ |(z i)*(x i)|) :
∃ N, ∀ M, ∑ i in Ico N M, |y i| ≤ ∑ i in Ico N M, |z i| :=
by
  sorry



def Bounded (x : ℕ → ℕ) : Prop := ∃ B, ∀ n, x n ≤ B

def EventuallyBounded (x : ℕ → ℕ) : Prop := ∃ B, ∃ N, ∀ n, N ≤ n → x n ≤ B

/-
The next result is very similar to the proof in the video `E2_let`.
08 -/
lemma Bounded_of_EventuallyBounded (h: EventuallyBounded x) : Bounded x :=
by
  sorry


def Omega (x y : ℕ → ℕ) : Prop := ∃ N, ∃ c, ∀ n, N ≤ n → x n ≤ c * (y n)

notation x"= O(" y ")" => Omega x y

#check 1 = O( 1)
-- 09
example (h : a ≤ b): Omega (fun n => n^a) (fun n => n^b) :=
by
  sorry


/-- Hint: try to apply the lemma you proved above `Bounded_of_EventuallyBounded`
10 -/
example (f g : ℕ → ℕ) : Omega f g → Bounded (f/g) :=
by
  sorry
