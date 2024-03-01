import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Irrational

namespace Gdelta

open Nat hiding add_lt_add
open Set Metric

/-

In Analysis 1 you saw an example of a function f : ℝ → ℝ that is continuous at x
iff x is irrational. (The Thomae function.)

A natural follow-up question is to ask what other sets can occur as the
`setOfContinuity` of a function?

1) Let (X,d), (Y,e) be metric spaces and f: X → Y and define

  `setOfContinuity f = {x : X | f is continuous at x }`

Prove that the `setOfContinuity f` is a countable intersection of open sets.


A set s is open in the metric space X iff
∀ (x : α), x ∈ s → ∃ ε, ε > 0 ∧ ball x ε ⊆ s

-/


variable {X Y : Type} {x : X} {ε : ℝ}
variable [MetricSpace X] [MetricSpace Y]
#check isOpen_iff
#check ball -- the open ball
#print ball

/-
  We introduce our own (non-Mathlib) definition of
  `f is continuous at x` called `CtsAt f x`
-/

/-- `CtsAt f x` iff f is continuous at x -/
def CtsAt (f : X → Y) (x : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ a, dist x a < δ → dist (f x) (f a) < ε

/-- the set of points at which f is cts -/
def setOfContinuity (f : X → Y) : Set X := {x | CtsAt f x}

/- Our first aim is to show that the `setOfContinuity` is a countable intersection
of open sets. We introduce first our definition of the open sets that we will use -/

/-- Open sets whose intersection will be the `setOfContinuity` of f -/
def U (f : X → Y) (n : ℕ) : Set X :=
  {x | ∃ δ > 0, ∀ a b, dist x a < δ → dist x b < δ → dist (f a) (f b) < ((n + 1):ℝ)⁻¹}

#check U
#check isOpen_iff
#check half_pos
#check add_halves
#check dist_comm
#check dist_triangle
#check mem_ball

/-- for any function f: X → Y and any n : ℕ, the set `U f n` is open in X-/
lemma U_isOpen {f : X → Y}: IsOpen (U f n) :=
by
  sorry

#check inv_pos_of_nat
#check exists_nat_one_div_lt
#check mem_iInter
#check dist_self

/-- The setOfContinuity is the intersection of the open sets {(U f n))ₙ -/
theorem setOfContinuity_eq_iInter {f : X → Y}: setOfContinuity f = ⋂ n, U f n :=
by
  sorry


/-
2) We now consider the case when X = Y = ℝ and prove the converse :

If U: ℕ → Set ℝ, ∀ n, U n is open and  G = ⋂ n, (U n), then there exists a
function f : ℝ → ℝ such that `setOfContinuity f = G`.

Sketch:  Given `U : ℕ → Set ℝ`, we define `func U : ℝ → ℝ` to be a suitable function,
i.e. with setOfContinuity equal to  G = ⋂n, (U n).

We define  func U as follows:
if x ∈ G then func U x = 0, if x ∉ G then there is a smallest n : ℕ such that x ∉ U n
and we set func U x = 1/(n+1), if x is irrational, and func U x = -1/(n+1) if x is rational.

We then prove various simple results about func U, before proving the two inclusions:

⋂n, U n ⊆ setOfContinuity (func U) : `iInter_ss_setOfContinuity`

setOfContinuity (func U) ⊆ ⋂n, U n : `setOfContinuity_ss_iInter`


Let f = func U. If x ∈ G = ⋂n, U n, then, given ε > 0, there is N such that (N + 1)⁻¹ < ε.
For any n : ℕ  x ∈ U n which is open so there is δₙ > 0 st `ball x δₙ ⊆ U n`,
Let `δ = min {δᵢ | i ≤ N}` then δ > 0 and for all n ≤ N we have `ball x δ ⊆ U n`.
In particular dist x y < δ → (∀ n ≤ N, y ∈ U n) and hence |f y| ≤ (N+1)⁻¹ < ε
so f is cts at x.

Conversely suppose that f is cts at x : ℝ and suppose, for a contradiction, that x ∉ G,
then let N be minimal st x ∉ U N, so |f x| = (N+1)⁻¹. Let ε = (N+1)⁻¹, then, since f
is cts at x, there exists δ > 0 such that |x - y|< δ → |f x - f y| < (N+1)⁻¹

Now we need to consider either x ∉ ℚ, in which case we can find y ∈ ℚ such that
x - δ < y < x (using `exists_rat_btwn`) and obtain a contradiction from |f x - f y| < |f x|
or x ∈ ℚ  in which case we can find y ∉ ℚ such that
x - δ < y < x (using `exists_irrational_btwn`) and obtain a similar contradiction.

In both cases `func_abs_sub` may be useful.  -/
open Classical

variable {U : ℕ → Set ℝ}
variable {x y : ℝ}

/- If we have a predicate P : ℕ → Prop and we have a proof of `hP : ∃ n, P n` then
`Nat.find hP` will return the smallest N : ℕ for which P N holds. -/
#check Nat.find
-- the smallest n such that P n holds
#check Nat.find_spec
-- proof that P holds for the value Nat.find returns
#check Nat.find_min

-- proof that if k < nat.find then P k does not hold
/-- If x ∉ ⋂n (U n) then there is a smallest N such that x ∉ U N and x ∈ U n for all n < N -/
lemma min_n (hnin : x ∉ ⋂ n, U n) : ∃ N, x ∉ U N ∧ ∀ n, n < N → x ∈ U n :=
by
  sorry

/-- The function `func U` as described in the comments above -/
noncomputable
def func (U : ℕ → Set ℝ) : ℝ → ℝ := fun x =>
  if h : x ∈ ⋂ n, U n then 0 else
    if (Irrational x) then ((min_n h).choose + 1)⁻¹
      else -((min_n h).choose + 1 : ℝ)⁻¹

#print func

/-- func U x = 0 for all x ∈ ⋂ n, U n -/
@[simp]
lemma func_in (h : x ∈ ⋂ n, U n) : func U x = 0 :=
by
  sorry

/-- if x ∉ ⋂n, U n and x is irrational then func U x is (N+1)⁻¹, where N is minimal st x ∉ U N-/
@[simp]
lemma func_nin_irrat (hnin : x ∉ ⋂ n, U n) (hir : Irrational x) :
    func U x = (((min_n hnin).choose + 1):ℝ)⁻¹ :=
by
  sorry

/-- if x is irrational then 0 ≤ func U x -/
@[simp]
lemma func_irrat_nonneg (hir : Irrational x) : 0 ≤ func U x :=
by
  sorry

/-- if x ∉ ⋂n, U n and x is rational then func U x is -(N+1)⁻¹, where N is minimal st x ∉ U N-/
@[simp]
lemma func_nin_rat (hnin : x ∉ ⋂ n, U n) (hir : ¬Irrational x) :
    func U x = -(((min_n hnin).choose + 1):ℝ)⁻¹ :=
by
  sorry

/-- if x is rational then func U x ≤ 0 -/
@[simp]
lemma func_rat_nonpos (hir : ¬Irrational x) : func U x ≤ 0 :=
by
  sorry

/-- If x ∉ ⋂n, U n then |func U x| = (N+1)⁻¹-/
@[simp]
lemma func_nin (hnin : x ∉ ⋂ n, U n) : |func U x| = (((min_n hnin).choose + 1):ℝ)⁻¹ :=
by
  sorry

/-- If x ∈ U n for all n < N then |func U x| ≤ (N+1)⁻¹ -/
lemma func_le_abs {N : ℕ} (h : ∀ n, n < N → x ∈ U n) : |func U x| ≤ ((N + 1):ℝ)⁻¹ :=
by
  sorry

open Finset


/-- If ∀ n, is_open (U n),  then func U is cts at every x ∈ ⋂ n, U n -/
theorem iInter_ss_setOfContinuity (hopen : ∀ n, IsOpen (U n)) : (⋂ n, U n) ⊆ setOfContinuity (func U) :=
by
  sorry

/-- if x ∉ ℚ and y ∈ ℚ then max |func U x| |func U y| ≤ |func U x - func U y|  -/
lemma func_abs_sub (hir : Irrational x) (hrat : ¬Irrational y) :
    max (|func U x|) (|func U y|) ≤ |func U x - func U y| :=
by
  sorry



/-
The following may be useful for the next result.
-/
#check exists_irrational_btwn
#check exists_rat_btwn
#check not_subset_iff_exists_mem_not_mem
#check Real.dist_eq
#check le_max_left
#check Rat.not_irrational



/-- The setOfContinuity is a subset of ⋂ n, U n-/
theorem setOfContinuity_ss_iInter : setOfContinuity (func U) ⊆ ⋂ n, U n :=
by
  sorry

/-- The intersection of the open U n is exactly the setOfContinuity of func U -/
theorem iInter_eq_set_of_cts (hopen : ∀ n, IsOpen (U n)) : ⋂ n, U n = setOfContinuity (func U) :=
by
  sorry


end Gdelta


/-!
Possible extension: give an example of a metric space (X,d) and a G-delta set in G ⊆ X such that
no function f : X → ℝ has G as its set of continuity.
-/
