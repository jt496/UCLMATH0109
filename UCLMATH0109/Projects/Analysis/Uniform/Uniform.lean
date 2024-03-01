import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

/-
We define pointwise and uniform convergence of a sequence of functions fₙ: X → Y
on a set s (where X, Y are Metric Spaces)

Our mains results are:

`bdd_of_unifConv_bdd`: if {fₙ} are bounded on s for every n, and
  fₙ → g uniformly on s, then g is bounded on s

`cts_of_unifConv_cts`: if fₙ is cts on s for every n,  and
fₙ → g uniformly on s, then g is cts on s

We then consider an example Fₙ : ℝ → ℝ, Fₙ(a) = n/(n*a + 1)

We will show that each Fₙ is bounded on (0,2) and Fₙ(a) → 1/a pointwise on (0,2)

We then show that 1/a is not bounded on (0,2) and hence deduce that the convergence of Fₙ → 1/a is not uniform

-/

section metric
variable {X Y : Type} [MetricSpace X] [MetricSpace Y]


open Set

/-- A sequence of functions fₙ converges pointwise to g on a set s iff  -/
def PtWiseConv (f : ℕ → X → Y) (g : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ N, ∀ n, N ≤ n → dist (f n x) (g x) < ε

/-- A sequence of functions fₙ converges uniformly to g on a set s iff  -/
def UnifConv (f : ℕ → X → Y) (g : X → Y) (s : Set X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ x ∈ s, ∀ n, N ≤ n → dist (f n x) (g x) < ε

/-- A function f : X → Y is bdd_on the set s, iff ∃B, such that if a,b ∈ s then
dist (f a) (f b) ≤ B -/
def BddOn (f : X → Y) (s : Set X) : Prop :=
  ∃ B, ∀ a b, a ∈ s → b ∈ s → dist (f a) (f b) ≤ B

/-- A function f : X → Y is cts_on the set s, iff ... -/
def CtsOn (f : X → Y) (s : Set X) : Prop :=
  ∀ a ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ b ∈ s, dist b a < δ → dist (f b) (f a) < ε


#check dist_comm
#check dist_triangle

/-- If fₙ → g uniformly on s then it converges pointwise to g on s -/
lemma pt_conv_of_unifConv {f : ℕ → X → Y}   (hu : UnifConv f g s) : PtWiseConv f g s :=
by
  sorry

#check dist_triangle4 -- the triangle inequality for 4 points

/-- if fₙ converges to g uniformly on s and every fₙ is bounded on s then g is bounded on s -/
theorem bdd_of_unifConv_bdd {f : ℕ → X → Y} (hu : UnifConv f g s) (hb : ∀ n, BddOn (f n) s) : BddOn g s :=
by
  sorry

/-- If fₙ is cts on s for each n, and fₙ → g uniformly on s, then g is cts on s-/
theorem cts_of_unifConv_cts {f : ℕ → X → Y} (hu : UnifConv f g s) (hc : ∀ n, CtsOn (f n) s) : CtsOn g s :=
by
  sorry


end metric
open Nat Set
/-
We now consider an example Fₙ : ℝ → ℝ, Fₙ(a) = n/(n*a + 1)

We will show that each Fₙ is bounded on (0,2) and Fₙ(a) → 1/a pointwise on (0,2)

We then show that 1/a is not bounded on (0,2) and hence deduce that the convergence of Fₙ → 1/a is not uniform
-/
noncomputable def F : ℕ → ℝ → ℝ := fun n a => n / (n * a + 1)

#check Real.dist_eq

/-- Rewriting lemma for F -/
lemma F' : F n a = n / (n * a + 1) :=
  sorry

/-- F is nonnegative on (0,2)-/
lemma F_nonneg : ∀ n : ℕ, ∀ a, a ∈ Ioo (0 : ℝ) 2 → 0 ≤ F n a :=
by
  sorry

/-- Fₙ a ≤ n for a ∈ (0,2)-/
lemma F_le : ∀ n : ℕ, ∀ a, a ∈ Ioo (0 : ℝ) 2 → F n a ≤ n :=
by
  sorry

/-- Fₙ → 1/a pointwise on (0,2)-/
lemma F_tends_to_inv : PtWiseConv F (fun a => 1 / a) (Ioo 0 2) :=
by
  sorry

/-- Fₙ is bounded on (0,2) for each n -/
lemma F_bdd : BddOn (F n) (Ioo 0 2) :=
by
  sorry

/-- 1/a is not bounded on (0,2) -/
lemma inv_not_bdd : ¬BddOn (fun a : ℝ => 1 / a) (Ioo 0 2) :=
by
  sorry

/-- Hence Fₙ does not converge uniformly to 1/a on (0,2)  -/
theorem F_not_unifConv : ¬UnifConv F (fun a => 1 / a) (Ioo 0 2) :=
by
  sorry

/-
Possible extension: give an example of a sequence  fₙ of continuous functions on [0,2]
that converge pointwise to a continuous function f on [0,2] but for which the convergence is not uniform.

One example is to take the piecewise linear function that is equal to

(n+1)²x for x ≤ 1/(n+1)
(n+1)(2 - (n+1)x) for 1/(n+1)< x ≤ 2/(n+1)
and zero elsewhere

The proof is not hard but it could be messy unless you prove some useful intermediate lemmas.
-/

theorem exists_cts_limit_cts_not_uniform : ∃ (f : ℕ → ℝ → ℝ), ∃ (g : ℝ → ℝ),
 (∀ n, CtsOn (f n) (Icc 0 2)) ∧ CtsOn g (Icc 0 2) ∧ PtWiseConv f g (Icc 0 2) ∧ ¬ UnifConv f g (Icc 0 2)  :=
by
  sorry
