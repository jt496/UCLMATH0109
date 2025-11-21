import Mathlib
open Nat hiding add_le_add dist_comm dist_self dist
open Set Metric Filter

/-

# This project is about Cantor's Intersection theorem.
# Read the project pdf for details. See below for useful results from Mathlib.


-/

/-- Closed ball -/
local notation "ℬ" => Metric.closedBall
section part1
variable {X : Type}  [MetricSpace X]

/-

We will use the standard Mathlib definitions of metric spaces:

(X , dist) is a metric space iff X is a Type and dist: X → X → ℝ satisfies
dist_self : ∀ x, dist x x = 0
dist_comm : ∀ x y, dist x y = dist y x
dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
eq_of_dist_eq_zero : ∀ x y, dist x y = 0 → x = y

In particular closed balls are defined as:

def closedBall (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

We use the notation `ℬ a ρ` to denote the closed ball centred at a with radius ρ

-/

/-- The sequence `x : ℕ → X` tends to `a : X` as n → ∞ iff -/
def TendsTo (x : ℕ → X) (a : X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n, N ≤ n → dist (x n) a < ε

/-- A sequence is  `x : ℕ → X` is Cauchy in the metric space X iff -/
def IsCauchy (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, dist (x m) (x N) < ε

/-- A sequence is eventually constant iff -/
def EventuallyConst (x : ℕ → X) : Prop :=
  ∃ N, ∀ n, N ≤ n → x n = x N

/-
Both `TendsTo` and `IsCauchy` defined above are slightly different to their respective Mathlib
definitions `Tendsto` and `CauchySeq`, but they are equivalent in the context of metric spaces.

The lemmas `tendsTo_def` and `isCauchy_def` below allow us to translate back and forth.
-/

lemma tendsTo_def (x : ℕ → X) (l : X) : Tendsto x atTop (nhds l) ↔ TendsTo x l  :=by
  rw [Metric.tendsto_atTop]; rfl

lemma isCauchy_def (x : ℕ → X) : CauchySeq x ↔ IsCauchy x := by
  rw [Metric.cauchySeq_iff']; rfl


/- Part 1:

  #  Cantor's Intersection theorem

If (X,d) is a complete metric space and {ℬₙ} is a decreasing sequence of closed balls
(ie ∀ n, ℬₙ₊₁ ⊆ ℬₙ) and the radii of the ℬₙ are nonnegative and tend to zero then ⋂ₙ ℬₙ is non-empty

A useful lemma to state and prove:

If the sequence xₙ tends to l and ∃ N, ∀ n, N ≤ n → (x n) ∈ ℬ a ρ then l ∈ ℬ a ρ
-/

/-- Cantor's Intersection theorem  -/
theorem Cantor_Intersection [CompleteSpace X] {c : ℕ → X}
    (hdec : ∀ n, ℬ (c (n + 1)) (r (n + 1)) ⊆ ℬ (c n) (r n)) (rnonneg : ∀ n, 0 ≤ r n)
    (hz : TendsTo r 0) : (⋂ n, ℬ (c n) (r n)).Nonempty :=by
  sorry

end part1



section parts2and3

/-
Part 2 : prove that the function `Ndist` (see below) defines a complete metric on ℕ.
-/

/-- Ndist will be the metric on ℕ -/
noncomputable
def Ndist : ℕ → ℕ → ℝ := fun m n => if m = n then 0 else 1 + 1 / (m + n)

/-
You should first state and prove all the basic results needed to show that `Ndist`
is a metric on ℕ.
-/


/-- We can endow ℕ with a `Dist` function which (using the results you should
have proved above) you will prove to be a metric-/
noncomputable
instance natDist : Dist ℕ := ⟨Ndist⟩

/-
A pseudo-metric space is a set with a `Dist` function that satisfies all the axioms of
a metric space except that it does not require Dist x y = 0 → x = y
-/
/-- Show that `(ℕ, Dist)` is a pseudo metric space-/
noncomputable
instance natPseudoMetricSpace : PseudoMetricSpace ℕ
    where
  dist_self := by sorry
  dist_comm := by sorry
  dist_triangle := by sorry
  edist := fun m n => ENNReal.ofReal (dist m n)
  edist_dist :=by intro m n; rfl


/-- Add the final axiom to make this a metric space-/
noncomputable
instance natMetricSpace : MetricSpace ℕ
    where
  eq_of_dist_eq_zero :=by sorry

/--
In order to prove that our natMetricSpace is complete we need to infer a UniformSpace structure on it
-/
noncomputable
instance : UniformSpace ℕ := PseudoMetricSpace.toUniformSpace


/-- Any Cauchy sequence in (ℕ, dist) is eventually constant-/
lemma Cauchy_imp_event_const (x : ℕ → ℕ) (hc: CauchySeq x ): EventuallyConst x :=by
  sorry

/-- Hence (ℕ, Ndist) is a CompleteSpace -/
theorem Nat_Complete : CompleteSpace ℕ := by

  sorry

/-
Part 3: An example to show that the condition `radii tend to zero` is necessary in Cantor's theorem.

For `n : ℕ`, we define the set `Nball n = {n, n + 1, ....} ⊆ ℕ`, which we will prove below is a
closed ball in `(ℕ , Ndist)`
-/

/-- Define Nball n to be {n, n+1, n+2,...} -/
def Nball (n : ℕ) : Set ℕ := Set.Ici n

/-
The sequence of sets `{Nball n}` form an example to show that the condition `radii tend to zero`
is necessary in Cantor's Intersection theorem.

To demonstrate this you should now state and prove lemmas showing that the following three properties hold:

1. ∀ n, Nball n is a nonempty closed ball of radius at least 1,
    i.e. `Nball n = ℬ cₙ rₙ` with `rₙ ≥ 1`
2. This sequence of balls is strictly decreasing i.e. `∀ n, Nball (n + 1) ⊂ Nball n`
3. The intersection of all the Nballs is empty i.e. `⋂ n, Nball n = ∅`

(Remember you can/should always add small helper lemmas to help with the main proofs.)
-/

end parts2and3



/-
Possible extension: prove that we cannot replace `closed balls` by
`open balls` in Cantors Intersection theorem by giving an example of a
space X and a decreasing sequence of non-empty open balls
 in X whose radii tend to zero and have empty intersection.
-/
