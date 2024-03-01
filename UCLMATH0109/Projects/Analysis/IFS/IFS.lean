import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
If X is a complete metric space then the Hausdorff distance defines a complete metric
on the space of NonemptyCompact subsets of X.

Given a finite set A of Lipschitz mappings on X (with common factor K) the map ℱ on
Nonempty Compact subsets of X taking
`s ↦ ⋃ fᵢ ∈ A, fᵢ '' s` is Lipschitz with factor K on NonemptyCompacts X.

So if K < 1 this is a contraction mapping and so (by the contraction mapping theorem)
has a unique fixed point t. In particular if s is any nonempty compact subset of X then
the iterated sequence of sets `sₙ := ℱⁿ s` converges to this fixed point.

Hence any fractal in ℝⁿ defined by a contractive iterated function system can be approximated to within
an exponentially small (in Hausdorff distance) error by iteratively applying ℱ to any closed bounded
subset of ℝⁿ.

See pdf for more details.
-/

open Classical  Metric EMetric TopologicalSpace ENNReal Finset
open scoped ENNReal NNReal BigOperators Topology

section withX
#check ENNReal
variable {X : Type} [MetricSpace X]



#check infEdist
#check hausdorffEdist
#check hausdorffEdist_comm
#check hausdorffEdist_le_of_infEdist
#check infEdist_le_hausdorffEdist_of_mem
#check inf_le_left

/-- The dₕ(a ∪ b) (c ∪ d) ≤ max (dₙ a c) (dₕ b d) -/
lemma hausdorffEdist_union_union_le (a b c d : Set X)  :
hausdorffEdist (a ∪ b) (c ∪ d) ≤ max (hausdorffEdist a c) (hausdorffEdist b d):=
by
  wlog h : hausdorffEdist a c ≤ hausdorffEdist b d
  · sorry
  sorry

#check infEdist_iUnion

/-- If a b: ι  → Set X then dₕ((⋃ i ∈ I, aᵢ), (⋃ i ∈ I, bᵢ)) ≤ max'_{i ∈ I} dₕ(aᵢ,bᵢ) -/
lemma hausdorffEdist_iunion_iunion_le_max' {I : Finset ι} (hI : I.Nonempty) {a b : ι  → Set X} :
hausdorffEdist (⋃ i ∈ I, a i) (⋃ i ∈ I, b i) ≤ max' (I.image (fun i => hausdorffEdist (a i) (b i))) (Nonempty.image hI _):=
by
  sorry

#check nonempty_of_hausdorffEdist_ne_top

/-- If f : X → X is 0-Lipschitz then it maps any two sets not at distance ∞ to points at distance 0  -/
lemma lipschitzWith_zero {f : X → X} (hc: LipschitzWith 0 f) {s t : Set X} (hnt: hausdorffEdist s t ≠ ∞):
hausdorffEdist (f '' s) (f '' t) = 0:=
by
  sorry

#check ENNReal.le_of_forall_pos_le_add
#check exists_edist_lt_of_hausdorffEdist_lt

/-- If f : X → X is K-Lipschitz then it is K-Lipschitz for hausdorffEDist on Set X  -/
@[simp]
lemma lipschitzWith_hausdorff {f : X → X} (hc: LipschitzWith K f) (s t : Set X) (hnt: hausdorffEdist s t ≠ ∞) :
hausdorffEdist (f '' s) (f '' t) ≤ K * hausdorffEdist s t:=
by
  sorry


#check IsCompact.image

/-- The continuous image of a nonempty compact set as a nonempty compact  -/
def Continuous.map {f : X → X} (h : Continuous f) (s : NonemptyCompacts X) : NonemptyCompacts X where
  carrier := (f '' s)
  isCompact' :=by
    sorry
  nonempty' :=by
    sorry

#check hausdorffEdist_ne_top_of_nonempty_of_bounded

/-- If s and t are nonempty compact then dₙ s t ≠ ∞-/
@[simp]
lemma hausdorffEdist_ne_top_of_nonemptycompacts (s t: NonemptyCompacts X) : hausdorffEdist (s : Set X) t ≠ ∞ :=
by
  sorry

/-- If s and t are nonempty compact and F is cts then dₙ (f '' s) (f '' t) ≠ ∞-/
@[simp]
lemma hausdorffEdist_ne_top_of_nonemptycompacts_cts {f : X → X} (s t : NonemptyCompacts X) (hf : Continuous f):
hausdorffEdist ((f '' s) : Set X) (f '' t) ≠ ∞ :=
by
  sorry

#check lipschitzWith_iff_dist_le_mul

/-- If f : X → X is K-Lipschitz then so is the induced map on noncompact subsets -/
@[simp]
lemma nonemptyCompacts_Lipschitz (f : X → X) (hk : LipschitzWith K f) : LipschitzWith K (hk.continuous.map) :=
by
  sorry

/-- The type of contractive IFS on X with contraction factor 0 ≤ K < 1 -/
structure IFS (X : Type) (K : ℝ≥0)  [MetricSpace X] : Type where
A : Finset (X → X) -- finite set of maps
nonempty : A.Nonempty -- there is at least one map
lip : ∀ ⦃f⦄, f ∈ A → LipschitzWith K f -- the maps are Lipschitz with factor K
con : K < 1

namespace IFS

#check isCompact_biUnion
#check Set.nonempty_biUnion
#check  Finset.isCompact_biUnion

/-- The induced map of ℱ on NonemptyCompacts X -/
@[simp]
def map (ℱ : IFS X K) (s : NonemptyCompacts X) : NonemptyCompacts X where
  carrier :=⋃ f ∈ ℱ.A, f '' s
  isCompact' :=by
    sorry
  nonempty' :=by
    sorry

/-- Given an IFS the image of nonempty compacts sets are always at finite distance-/
@[simp]
lemma hausdorffEdist_ne_top_of_nonemptycompacts_cts_biUnion (ℱ : IFS X K)
(s t : NonemptyCompacts X) : hausdorffEdist (ℱ.map s : Set X)  (ℱ.map t) ≠ ∞:=
by
  sorry

/-- A K-Lipschitz IFS induces a K-Lipschitz map on nonempty compacts -/
lemma nonemptyCompacts_Lipschitz_IFS (ℱ : IFS X K) : LipschitzWith K ℱ.map :=
by
  sorry

/- We need the existence of a NonemptyCompact X, which Lean will easily infer from `[Inhabited X]` -/
variable [Inhabited X]

open ContractingWith

/-
In order to use the contraction mapping theorem we require completeness.
If `X` is a complete metric space then Lean can work out that `NonemptyCompacts X`
endowed with the Hausdorff metric is also complete.
-/
variable [CompleteSpace X]

/-
We now define the limit of an IFS as the fixed point of the induced map.
-/
#check fixedPoint

/-- The limit of an IFS (e.g. the Cantor set) -/
noncomputable
def limit (ℱ : IFS X K) : NonemptyCompacts X :=
by
  sorry

#check fixedPoint_isFixedPt

/-- This limit is a fixed point of ℱ.map -/
lemma limit_isFixedPt (ℱ : IFS X K) : ℱ.map ℱ.limit = ℱ.limit:=
by
  sorry

#check fixedPoint_unique

/-- If `s` is any fixed point of the IFS then `s` is its limit-/
lemma IFS_unique_fixedPoint  (ℱ : IFS X K) (hfp: ℱ.map s = s) : s = ℱ.limit  :=
by
  sorry


#check apriori_dist_iterate_fixedPoint_le

/--
The distance between the nth iteration of ℱ applied to a nonempty compact set `s` and its `ℱ.limit`
is an exponentially small multiple of the the distance between `s` and `ℱ.map s` -/
theorem speed_of_convergence (ℱ : IFS X K) (s : NonemptyCompacts X) (n : ℕ):
dist ((ℱ.map)^[n] s) ℱ.limit ≤ dist s (ℱ.map  s) * (K : ℝ) ^ n / (1 - K):=
by
  sorry


end IFS
end withX

/-
Examples: The IFS given by `f₀ : ℝ → ℝ, x ↦ 3⁻¹*x` and `f₁ : ℝ → ℝ, x ↦ 3⁻¹*(x + 2)` is one way of defining
the Cantor set (as its unique fixed point in `NonemptyCompacts ℝ`)
-/

open NNReal Classical Finset

lemma LipschitzWith.mul_const (K : ℝ≥0)   : LipschitzWith K (fun x : ℝ => K * x):=
by
  sorry

-- Any constant function is LipschitzWith 0
#check LipschitzWith.const

-- If f and g are Lipschitz with factors K_f and K_g then `f + g` is Lipschitz with factor `K_f + K_g`
#check LipschitzWith.add

/-- The Cantor IFS -/
noncomputable
def Cantor : IFS ℝ 3⁻¹ where
A := {fun x => 3⁻¹ * x, fun x => 3⁻¹ * (x + 2)}
nonempty :=by
  sorry
lip := by
  sorry
con := by
  sorry

lemma LipschitzWith.mul_const' (K : ℝ≥0) : LipschitzWith K (fun (x : ℝ × ℝ) => (K : ℝ) • x):=
by
  sorry

/-- The Sierpinski IFS given as 3 functions all scaling by 2⁻¹ and then translated by (0,0) (2⁻¹,0) and
(4⁻¹,4⁻¹*√3)-/
noncomputable
def Sierpinski : IFS (ℝ × ℝ) 2⁻¹ where
A := {fun x => 2⁻¹ * x,fun x => 2⁻¹ * x + ⟨2⁻¹,0⟩,
            fun x => 2⁻¹ * x + 4⁻¹*⟨1, Real.sqrt 3⟩}
nonempty :=by sorry
lip := by
  sorry
con := by
  sorry


/-
Possible extension: prove that if we start with the set {0} then after n-iterations of
the Cantor IFS we are within Hausdorff distance 1/3ⁿ  of the Cantor set.

-/

/-- Any singleton set is nonempty and compact -/
def singleton (x : ℝ) : NonemptyCompacts ℝ where
  carrier := {x}
  isCompact' :=by sorry
  nonempty' :=by sorry

/-- So we can write {x} for x ∈ ℝ and Lean will know this is a nonempty compact subset of ℝ-/
instance : Singleton ℝ (NonemptyCompacts ℝ) where
  singleton := singleton

/-- After n iterations the image of {0} under the Cantor IFS is within Hausdorff distance
 3^{-n} of the Cantor set.-/
theorem zero_conv_to_Cantor (n  : ℕ) :
dist ((Cantor.map)^[n] {0}) Cantor.limit ≤ (3⁻¹ : ℝ) ^ n:=
by
  sorry
