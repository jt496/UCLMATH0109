import Mathlib
#check Nat.dist_comm
open Nat hiding dist_comm dist_self
open Set Metric Classical
variable {X Y : Type}
variable [MetricSpace X] [MetricSpace Y]

/-
# In this project we will explore the properties of the set of points of continuity
# of a function f : X → Y, between metric spaces X and Y.
# Read the project pdf for details. See below for useful results from Mathlib.

-/

-- Facts about rational and irrational numbers
#check exists_irrational_btwn
#check exists_rat_btwn
#check Irrational
#check Rat.not_irrational



/-- the set of points at which f is continuous -/
abbrev SetOfContinuousAt (f : X → Y) : Set X := {x | ContinuousAt f x}

/-- A rw lemma for SetOfContinuous -/
lemma mem_SetOfContinuousAt_iff (f : X → Y) (a : X) : a ∈ SetOfContinuousAt f ↔
∀ ε > 0, ∃ δ > 0, ∀{x : X}, dist x a < δ → dist (f x) (f a) < ε := by
  dsimp; rw [continuousAt_iff]

/- Our first aim is to show that the `SetOfContinuousAt f` is a countable intersection
of open sets. We introduce first our definition of the sets that we will use
and prove that they are indeed open. -/

/-- Open sets whose intersection will be the `SetOfContinuousAt` of f -/
def V (f : X → Y) (n : ℕ) : Set X :=
  {x | ∃ δ > 0, ∀ a b, dist x a < δ → dist x b < δ → dist (f a) (f b) < ((n + 1): ℝ)⁻¹}

/-- The set `U f n` is open -/
lemma V_isOpen {f : X → Y}: IsOpen (V f n) :=by
  sorry

/-- The SetOfContinuousAt is the intersection of the {(V f n))ₙ -/
theorem setOfContinuousAt_eq_iInter {f : X → Y}: SetOfContinuousAt f = ⋂ n, V f n :=by

  sorry

/-
2) We now consider the case when X = Y = ℝ and prove the following converse :

If U : ℕ → Set ℝ, ∀ n, U n is open  then there exists a
function f : ℝ → ℝ such that `SetOfContinuousAt f = ⋂ n, (U n)`.
-/

variable {U : ℕ → Set ℝ}
variable {x y : ℝ}

/-
The following will be useful when proving the lemma `first` that we use to
define the function `func U` below.

If we have a predicate `P : ℕ → Prop` and we have a proof of `hP : ∃ n, P n` then
`Nat.find hP` will return the smallest `N : ℕ` for which `P N` holds.
-/
#check Nat.find -- the smallest n such that P n holds
#check Nat.find_spec -- proof the P holds for the value Nat.find returns
#check Nat.find_min -- proof that if k < Nat.find then P k does not hold

/-- If x ∉ ⋂ₙ (U n) then there is a smallest N such that x ∉ U N and x ∈ U n for all n < N -/
lemma first (hnin : x ∉ ⋂ n, U n) : ∃ N, x ∉ U N ∧ ∀ n, n < N → x ∈ U n :=by
  sorry

/-- The function `func U` as described in the project pdf -/
noncomputable
def func (U : ℕ → Set ℝ) : ℝ → ℝ := fun x =>
  if h : x ∈ ⋂ n, U n then 0 else
    if (Irrational x) then ((first h).choose + 1)⁻¹
      else - ((first h).choose + 1 : ℝ)⁻¹


/-- The intersection of the open U n is exactly the SetOfContinuousAt of func U -/
theorem iInter_eq_set_of_cts (hopen : ∀ n, IsOpen (U n)) : (⋂ n, U n) = SetOfContinuousAt (func U) :=by
  sorry


/-!
Possible extension: give an example of a metric space `(X, d)` and a sequence of open sets `U : ℕ → Set X`
such that no function `f : X → ℝ` has `G = ⋂ n, U n` as its set of continuity.
-/
