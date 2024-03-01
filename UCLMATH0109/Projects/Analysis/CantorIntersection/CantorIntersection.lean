import Mathlib.Tactic.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open Nat hiding add_le_add
open Set Metric

namespace CantorIntersection
/-

This project is about Cantor's Intersection theorem:

# Cantor's intersection theorem (a version of)

If (X,d) is a  complete metric space and {Bₙ} is a decreasing sequence of closed balls
(ie ∀ n, Bₙ₊₁ ⊆ Bₙ) and the radii of the Bₙ tend to zero then ⋂ₙ Bₙ is non-empty

We start by proving this: `Cantor_intersection`

Then we describe an example showing that the condition `radii tend to zero` is necessary in
Cantor's theorem.

More precisely, we define a metric on ℕ given by `Ndist(m,n) = 1 + 1 / (m + n), m ≠ n`
and `Ndist(m,m) = 0` (this is ℝ-valued) and show that:

1) (ℕ, Ndist) is a metric space

2) There exists a strictly decreasing sequence of closed nonempty balls {Bₙ}
  in (ℕ, Ndist) whose intersection is empty:
     `decreasing_Balls` `Ball_succ_is_closed_ball`

3) (ℕ, Ndist) is complete.  `nat_complete`

4) The intersection of these closed balls is empty: `empty_Balls_Inter`

-/
local notation "ℬ" => Metric.closedBall

variable {X : Type}
variable [MetricSpace X]

/-
Our definitions of limits / Cauchy sequence and completeness in metric spaces should be familiar
from Analysis, but these are not from Mathlib.

We will however use the standard Mathlib definitions of metric spaces and in particular closed balls:

def closedBall (x : α) (ε : ℝ) := {y | dist y x ≤ ε}
-/
#check closedBall
/-
We use the local notation `ℬ a ρ` to denote the closed ball centred at a with radius ρ

(X , dist) is a metric space iff X is a Type and dist: X → X → ℝ satisfies
dist_self : ∀ x, dist x x = 0
dist_comm : ∀ x y, dist x y = dist y x
dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
eq_of_dist_eq_zero : ∀ x y, dist x y = 0 → x = y

If only the first 3 axioms hold then we have a `PseudoMetricSpace`

-/

/-- The sequence `x : ℕ → X` tends to `l : X` as n → ∞ iff -/
def TendsTo {X : Type} [MetricSpace X] (x : ℕ → X) (l : X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → dist (x n) l < ε

/-- A sequence is Cauchy in the metric space X iff -/
def IsCauchy {X : Type} [MetricSpace X] (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → m ≤ n → dist (x n) (x m) < ε

/-- A metric space X is complete iff every Cauchy sequence in X converges to a limit in X -/
def Complete (X : Type) [MetricSpace X] : Prop :=
  ∀ (x : ℕ → X), IsCauchy x → ∃ l, TendsTo x l


/-- A sequence is eventually constant iff -/
def EventuallyConst {X : Type} (x : ℕ → X) : Prop :=
  ∃ N, ∀ n, N ≤ n → x n = x N


#check dist_self
#check dist_comm
#check dist_triangle
#check mem_closedBall
#check sub_pos_of_lt
#check le_max_left
#check add_lt_add_of_lt_of_le

/-- If xₙ tends to l and ∃ N, ∀ n, N ≤ n → (x n) ∈ ℬ a ρ then the limit l also lies in ℬ a ρ -/
lemma limit_mem_closedBall {x : ℕ → X} (hl : TendsTo x l) (hin : ∃ N, ∀ n, N ≤ n → x n ∈ ℬ a ρ) : l ∈ ℬ a ρ :=
by
  sorry

#check mem_closedBall_self
#check mem_iInter
#check abs_of_nonneg
#check Real.dist_0_eq_abs

/-- # Cantor's Intersection theorem
If (X,d) is a complete metric space and {ℬₙ} is a decreasing sequence of closed balls
(ie ∀ n, ℬₙ₊₁ ⊆ ℬₙ) and the radii of the ℬₙ are nonnegative and tend to zero then ⋂ₙ ℬₙ is non-empty  -/
theorem Cantor_intersection (hcom : Complete X) {c : ℕ → X}
    (hdec : ∀ n, ℬ (c (n + 1)) (r (n + 1)) ⊆ ℬ (c n) (r n)) (rnonneg : ∀ n, 0 ≤ r n)
    (hz : TendsTo r 0) : (⋂ n, ℬ (c n) (r n)).Nonempty :=
by
  sorry

/-
An example to show that the condition `radii tend to zero` is necessary.
We start by proving some simple inequalities describing a metric on ℕ
-/


/-- If m ∈ ℕ then 0 ≤ 1/m in ℝ (recall that in Lean 1/0 = 0) -/
lemma inv_nonneg_of_nat (m : ℕ) : 0 ≤ 1 / (m : ℝ) :=
by
  sorry

/-- If m ∈ ℕ then 1 / m ≤ 1 -/
lemma div_nat_le_one {m : ℕ}: (1 : ℝ) / m ≤ 1 :=
by
  sorry

/-- Ndist will be the metric on ℕ -/
noncomputable
def Ndist : ℕ → ℕ → ℝ := fun m n => if m = n then 0 else 1 + 1 / (m + n)

/-- Ndist m m = 0 -/
lemma Ndist_self (m : ℕ) : Ndist m m = 0 :=
by
  sorry

/-- Ndist m n = 1 + 1 /(m + n) if m ≠ n -/
lemma Ndist_ne (h : m ≠ n) : Ndist m n = 1 + 1 / (m + n) :=
by
  sorry

/-- Ndist m n = Ndist n m -/
lemma Ndist_comm (m n : ℕ) : Ndist m n = Ndist n m :=
by
  sorry

/-- If m ≠ n then 1 ≤ Ndist m n -/
lemma one_le_Ndist_ne (h : m ≠ n) : 1 ≤ Ndist m n :=
by
  sorry

/-- Ndist is nonnegative -/
lemma Ndist_nonneg (m n : ℕ) : 0 ≤ Ndist m n :=
by
  sorry

/-- Ndist m n ≤ 2 -/
lemma Ndist_le_two (m n : ℕ) : Ndist m n ≤ 2 :=
by
  sorry

/-- the triangle inequality for Ndist-/
lemma Ndist_triangle (k m n : ℕ) : Ndist k n ≤ Ndist k m + Ndist m n :=
by
  sorry

/-- We can endow ℕ with a `Dist` function which we will show below is a metric-/
noncomputable
instance natDist : Dist ℕ := ⟨Ndist⟩

/- A PseudoMetricSpace is a set with a `Dist` function that satisfies all the axioms of
a metric space except that it does not require Dist x y = 0 → x = y -/
/-- Show that `(ℕ, Dist)` is a pseudo metric space-/
noncomputable
instance natPseudoMetricSpace : PseudoMetricSpace ℕ
    where
  dist_self := sorry
  dist_comm := sorry
  dist_triangle := sorry
  edist := fun m n => ENNReal.ofReal (dist m n)
  edist_dist :=
  by
    intro m n; rfl

/-- Check that that the `dist` function in the pseudo-metric space (ℕ , dist) is `Ndist`-/
lemma dist_Ndist : dist = Ndist :=sorry

/-- Add the final axiom to make this a metric space-/
noncomputable
instance natMetricSpace : MetricSpace ℕ
    where
  eq_of_dist_eq_zero := sorry

/-
Recall that a closed ball in  a metric space (X, d) is a set of the form { x | dist x a ≤ r }
for some radius r ≥ 0 and centre a

We now define `Nball n = {n, n+1, ....} ⊆ ℕ`, which we will prove below is a closed ball (ℕ , Ndist)   -/
/-- Define Ball n to be {n, n+1, n+2,...} -/
def Nball (n : ℕ) : Set ℕ := Set.Ici n

/-- rewriting lemma for membership of Nball n -/
@[simp]
lemma mem_Nball {x n : ℕ} : x ∈ Nball n ↔ n ≤ x := by rfl

/-- Every Ball n is non-empty -/
lemma non_empty_Nball (n : ℕ) : (Nball n).Nonempty :=
by
  use n
  rw [mem_Nball]

#check not_subset

/-- The Nballs are strictly decreasing i.e. Nball (n+1) ⊂ Nball n-/
lemma decreasing_Nballs (n : ℕ) : Nball (n + 1) ⊂ Nball n :=
by
  constructor
  · intro k (hk : n + 1 ≤ k); rw [mem_Nball]
    exact (le_succ n).trans hk
  · rw [not_subset]
    use n; simp only [mem_Nball]
    constructor
    · rfl
    · exact not_succ_le_self _

/-
Each Nball n is a closedBall in this metric space.

We prove this first for n = 0 which is easy -/
#check ℬ 0 1

-- this is notation for closedBall
lemma Nball_zero_is_closedBall : Nball 0 = ℬ 0 2 :=
by
  ext n; rw [mem_Nball]
  constructor
  · intros
    rw [closedBall,dist_Ndist]; exact Ndist_le_two _ _
  · intros; exact zero_le'


/-- Now show Ball n is a closed ball for 1 ≤ n -/
lemma Nball_succ_is_closedBall {n : ℕ} (hn : 1 ≤ n) : Nball n = ℬ n (1 + 1 / (2 * n)) :=
by
  sorry

/-- Any Cauchy sequence in (ℕ,dist) is eventually constant-/
theorem Cauchy_imp_event_const (x : ℕ → ℕ) (hc: IsCauchy x ): EventuallyConst x :=
by
  sorry

/-- Hence (ℕ, Ndist) is Complete -/
theorem Nat_Complete : Complete ℕ :=
by
  sorry

/-
We have checked that (ℕ,Ndist) is a complete metric space that `Nball` is a
strictly decreasing sequence of non-empty closed balls with nonnegative radii.
But the radii do not tend to zero and the conclusion of Cantor's intersection theorem
 fails to hold : their intersection is empty.
-/

/-- The intersection of all the Nballs is empty -/
theorem Nballs_iInter_empty : (⋂ n, Nball n) = ∅ :=
by
  sorry


/-
Possible extension: prove that we cannot replace `closed balls` by
`open balls` in Cantors intersection theorem by giving an example of a
space X and a decreasing sequence of non-empty open balls
 in X whose radii tend to zero yet have empty intersection.

-/
