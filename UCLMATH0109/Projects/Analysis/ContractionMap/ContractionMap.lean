import Mathlib

open Nat
open Finset


/-
# In this project we will explore the 2-adic metric on ℕ.
# Read the project pdf for details. See below for useful results from Mathlib.

-/


section log₂
/-
log₂ n := 0 if n = 0 and otherwise := k such that 2ᵏ is the largest power of two dividing n.

We define this recursively and will need to prove that it does have the claimed property.
-/
/--log₂ n := 0 if n = 0 and otherwise := k such that 2ᵏ is the largest power of two dividing n.
-/
@[reducible]
def log₂ : ℕ → ℕ
  | 0 => 0
  | succ n => if 2 ∣ succ n then log₂ (succ n / 2) + 1 else 0

-- We start by adding some definitional lemmas about log₂

@[simp]
lemma log₂_zero : log₂ 0 = 0 :=by sorry

@[simp]
lemma log₂_succ : log₂ (succ n) = ite (2 ∣ succ n) (log₂ (succ n / 2) + 1) 0 :=by sorry


-- Think about other simple lemmas that you can state and prove before tackling the first theorem.

/-- If n ≠ 0 then log₂ n  = m  such that 2ᵐ ∣  n and ¬ 2ᵐ⁺¹ ∣ n -/
theorem log₂_prop (hne : n ≠ 0) : 2 ^ log₂ n ∣ n ∧ ¬2 ^ (log₂ n + 1) ∣ n :=by
  sorry




end log₂

/-
We would like to define a metric d₂ on ℕ by:

  d₂ m n := 0 for m = n, and d₂ m n := 1/2^(log₂ |m - n|) for m ≠ n,

but we need to be careful about truncated subtraction in ℕ.

We use `Nat.dist` which is defined as `Nat.dist m n = (m - n) + (n - m)`

Notice that truncation of subtraction means this is exactly what we would
usually write as `|m - n|`
-/
/--
ndist m n = |m - n|  -/
def ndist : ℕ → ℕ → ℕ := fun m n => Nat.dist m n

/-- We can now define a metric d₂ on ℕ -/
noncomputable def d₂ : ℕ → ℕ → ℝ :=
  fun m n => if  (m = n)  then 0 else (1 / 2 ^ log₂ (ndist m n))




/-- (ℕ , d₂) is a metric space -/
noncomputable
instance twoMetric : MetricSpace ℕ
    where
  dist := d₂
  dist_self :=by sorry
  dist_comm := by sorry
  dist_triangle := by sorry
  eq_of_dist_eq_zero := by sorry
  edist := fun m n => ENNReal.ofReal (d₂ m n)
  edist_dist :=
  by
    intro m n; rfl



-- Facts about Fixed points and contraction maps
#check ContractingWith
#check lipschitzWith_iff_dist_le_mul
#check ContractingWith.fixedPoint_isFixedPt


/-- If a and b are non-zero then `n ↦ a * n + b` has no fixed points -/
lemma not_IsFixedPt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :  ¬ (fun n => a*n + b).IsFixedPt k :=by
  sorry

/-- d₂ is translation invariant-/
lemma shift_invariant (x y b : ℕ) : d₂ (x + b) (y + b) = d₂ x y :=by
  sorry

/-- Any map x ↦ 2x + b is a contraction but has no fixed points for b ≠ 0 -/
lemma ContractingWith_mul_two (b : ℕ) : ContractingWith 2⁻¹ (fun n => 2*n + b):=by
  sorry

/-
We are now ready to prove that (ℕ, d₂) is not complete.

Before we do this we need to give ℕ a UniformSpace structure in the correct way.

-/
noncomputable
instance twoUnif: UniformSpace ℕ  := PseudoMetricSpace.toUniformSpace


theorem Nat_not_complete : ¬ CompleteSpace ℕ :=by
  sorry

/-

Possible extension: continuity in (ℕ, d₂).

Prove that every polynomial with coefficients in ℕ is continuous everywhere.

To make sure we have the correct topology on ℕ we need the following instance.

-/

noncomputable
instance twoTop : TopologicalSpace ℕ  := UniformSpace.toTopologicalSpace
