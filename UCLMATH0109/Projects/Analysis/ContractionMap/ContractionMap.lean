import Mathlib.Tactic.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Prime
import Mathlib.Topology.MetricSpace.Contracting

open Nat hiding pow_zero pow_succ pow_succ' ne_of_gt add_le_add Prime

/-
Note `a divides b` is written as `a ∣ b` (where ∣ is \| )
-/

section log₂

/-- If n ≠ 0 then n / 2 < n -/
lemma div_two_lt (hne : n ≠ 0) : n / 2 < n :=
by
  rw [div_lt_iff_lt_mul zero_lt_two]
  apply lt_mul_right (Nat.pos_of_ne_zero hne) one_lt_two


/--
log₂ n := 0 if n = 0 and otherwise := k such that 2ᵏ is the largest power of two dividing n.
-/
def log₂ : ℕ → ℕ
  | 0 => 0
  | succ n =>
    have dec : succ n / 2 < succ n := div_two_lt (succ_ne_zero _)
    if 2 ∣ succ n then log₂ (succ n / 2) + 1 else 0

/-- log₂ 0 = 0 -/
@[simp]
lemma log₂_zero : log₂ 0 = 0 :=
by
  sorry

/-- log₂ 1 = 0-/
@[simp]
lemma log₂_one : log₂ 1 = 0 :=
by
  sorry

/-- log₂ (succ n ) = ite ...  -/
@[simp]
lemma log₂_succ : log₂ (succ n) = ite (2 ∣ succ n) (log₂ (succ n / 2) + 1) 0 :=
by
  sorry

/-- If n ≠ 0 and 2 ∣ n then log₂ n = log₂ (n / 2) + 1-/
lemma log₂_even (hne : n ≠ 0) (h2 : 2 ∣ n) : log₂ n = log₂ (n / 2) + 1 :=
by
  sorry

/-- If ¬ 2 ∣ n then log₂ n = 0 -/
@[simp]
lemma log₂_odd (h2 : ¬2 ∣ n) : log₂ n = 0 :=
by
  sorry


#check Nat.mul_div_cancel_left
#check mul_ne_zero

/-- If n ≠ 0 then log₂ (2*n) = log₂ n + 1 -/
@[simp]
lemma log₂_two_mul (hne : n ≠ 0) : log₂ (2 * n) = log₂ n + 1 :=
by
  sorry

#check pow_succ
#check pow_pos

/-- If n ≠ 0 and ¬ 2 ∣ n then log₂ (2ᵏ * n) = k -/
@[simp]
lemma log₂_mul_odd (hne : n ≠ 0) (hnd : ¬2 ∣ n) : log₂ (2 ^ k * n) = k :=
by
  sorry

#check two_dvd_ne_zero

/-- So in particular log₂ 2ᵏ = k  -/
lemma log₂_pow_two : log₂ (2 ^ k) = k :=
by
  sorry


#check lt_of_pow_dvd_right

/-- If n ≠ 0 and  2ᵗ∣ n then t < n -/
lemma dvd_pow_two_lt (hne : n ≠ 0) (htd : 2 ^ t ∣ n) : t < n :=
by
  sorry

section withFinset
open Finset

#check mem_range_succ_iff
#check mem_filter
#check le_max'
#check max'

/-- If n ≠ 0 then there exists a largest power of two dividing n -/
lemma exists_max_pow_two_dvd (hne : n ≠ 0) : ∃ m, 2 ^ m ∣ n ∧ ¬2 ^ (m + 1) ∣ n :=
by
  sorry

end withFinset

-- Our first main result is that log₂ has the desired property

#check right_ne_zero_of_mul

/-- If n ≠ 0 then log₂ n  = m  such that 2ᵐ ∣  n and ¬ 2ᵐ⁺¹ ∣ n -/
theorem log₂_prop (hne : n ≠ 0) : 2 ^ log₂ n ∣ n ∧ ¬2 ^ (log₂ n + 1) ∣ n :=
by
  sorry

lemma log₂_dvd_self (hne : n ≠ 0) : 2 ^ log₂ n ∣ n :=
by
  sorry

#check pow_dvd_of_le_of_pow_dvd

/-- if ¬ 2ᵏ ∣ n then log₂ n < k -/
lemma log₂_lt (hd : ¬2 ^ k ∣ n) : log₂ n < k :=
by
  sorry

/-- for n ≠ 0, if log₂ n < k then  ¬ 2ᵏ ∣ n  -/
lemma succ_log₂_lt (hne : n ≠ 0) (hd : log₂ n < k) : ¬2 ^ k ∣ n :=
by
  sorry

/-- for n ≠ 0, if 2ᵏ ∣ n then log₂ n ≤ k    -/
lemma succ_le_log₂ (hne : n ≠ 0) (hd : 2 ^ k ∣ n) : k ≤ log₂ n :=
by
  sorry

/-- if k ≤ log₂ n then 2ᵏ ∣ n -/
lemma le_log₂ (hd : k ≤ log₂ n) : 2 ^ k ∣ n :=
by
  sorry

#check Nat.eq_zero_of_zero_dvd

/-- if n ≠ 0 then m | n → log₂ m ≤ log₂ n -/
lemma log₂_dvd (hne : n ≠ 0) (hd : m ∣ n) : log₂ m ≤ log₂ n :=
by
  sorry

/-- 2^n ≠ 0 -/
lemma two_pow_ne_zero : 2 ^ n ≠ 0 :=
by
  sorry

end log₂

/- Up to this point we have only been dealing with ℕ-valued functions but a metric is ℝ-valued
so we need to establish some simple inequalities in ℝ  -/

/-- 0 < 2^n, in ℝ-/
lemma two_pow_pos : (0 : ℝ) < 2 ^ n :=
by
  sorry

#check div_pos

/-- 0 < 1/2^n -/
lemma two_inv_pow_pos : (0 : ℝ) < 1 / 2 ^ n :=
by
  sorry

#check div_le_div

/-- if m ≤ n then 1/2^n ≤ 1/2^m -/
lemma two_inv_pow_le (h : m ≤ n) : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ m :=
by
  sorry

/-- if m ≤ n then 1/2^n ≤ 1/2^m -/
lemma two_inv_pow_lt (h : m < n) : (1 : ℝ) / 2 ^ n < 1 / 2 ^ m :=
by
  sorry


#check le_add_of_nonneg_left

/-- 1/2^(min m n) ≤ 1/2^m + 1/2^n -/
lemma two_inv_pow_min (m n : ℕ) : (1 / 2 ^ min m n : ℝ) ≤ 1 / 2 ^ m + 1 / 2 ^ n :=
by
  sorry

/-- if min m n ≤  k then 1/2^k ≤ 1/2^m + 1/2^n -/
lemma two_inv_pow_le_of_min (h : min m n ≤ k) : (1 : ℝ) / 2 ^ k ≤ 1 / 2 ^ m + 1 / 2 ^ n :=
by
  sorry

/- We would like to define a metric d₂ on ℕ by:
  d₂ m n := 0 for m = n, and d₂ m n := 1/2^(log₂ |m - n|) for m ≠ n,
but there is no absolute value on ℕ (if there were it would just be the identity!)
However there is an absolute value function from `ℤ → ℕ` called `Int.natAbs`
-/

/--
ndist m n = |m - n| (where m and n are first cast to ℤ so subtraction is well-behaved) -/
def ndist : ℕ → ℕ → ℕ := fun m n => Int.natAbs ((m : ℤ) - n )

@[simp]
lemma ndist' : ndist m n = Int.natAbs ((m : ℤ) - n ):=
by
  sorry

#check min_self
#check tsub_self

/-- | n - n | = 0-/
@[simp]
lemma ndist_self (n : ℕ) : ndist n n = 0 :=
by
  sorry

#check max_eq_right


/-- if a < b then |a - b|  = b - a -/
@[simp]
lemma ndist_of_lt (hab : a < b) : ndist a b = b - a :=
by
  sorry

/-- if a ≤ b then |a - b|  = b - a -/
@[simp]
lemma ndist_of_le (hab : a ≤ b) : ndist a b = b - a :=
by
  sorry


/-- |a - b| = |b - a| -/
@[simp]
lemma ndist_comm (a b : ℕ) : ndist a b = ndist b a :=
by
  sorry

/-- if a ≠ b then |a - b| ≠ 0 -/
lemma ndist_ne (hab : a ≠ b) : ndist a b ≠ 0 :=
by
  sorry

#check add_tsub_add_eq_tsub_right

/-- |a + c - (b + c)| = |a - b| -/
@[simp]
lemma ndist_shift (c : ℕ) : ndist (a + c) (b + c) = ndist a b :=
by
  sorry

/-- We can now define a metric d₂ on ℕ -/
noncomputable def d₂ : ℕ → ℕ → ℝ :=
fun m n => if  (m = n)  then 0 else (1 / 2 ^ log₂ (ndist m n))

lemma d₂' : d₂ m n = if (m = n) then 0 else ((1:ℝ) / 2 ^ log₂ (ndist m n)) :=
by
  sorry

lemma d₂_ne (hne : m ≠ n) : d₂ m n = 1 / 2 ^ log₂ (ndist m n) :=
by
  sorry

lemma d₂_self (m : ℕ) : d₂ m m = 0 :=
by
  sorry

lemma d₂_comm (m n : ℕ) : d₂ m n = d₂ n m :=
by
  sorry

lemma d₂_pos_of_ne (h : m ≠ n) : 0 < d₂ m n :=
by
  sorry

lemma d₂_nonneg : 0 ≤ d₂ m n :=
by
  sorry

lemma d₂_eq_zero (h : d₂ m n = 0) : m = n :=
by
  sorry


lemma ndist_dvd {d : ℕ} (hab : d ∣ ndist a b) (hbc : d ∣ ndist b c) : d ∣ ndist a c :=
by
  sorry

lemma ndist_dvd_pow {i j: ℕ} (hab : 2^i ∣ ndist a b) (hbc : 2^j ∣ ndist b c) :
 2^(min i j) ∣ ndist a c :=
by
  sorry

lemma d₂_triangle (k m n : ℕ) : d₂ k n ≤ d₂ k m + d₂ m n :=
by
  sorry

/-- (ℕ , d₂) is a metric space -/
noncomputable
instance twoMetric : MetricSpace ℕ
    where
  dist := d₂
  dist_self := sorry
  dist_comm := sorry
  dist_triangle := sorry
  eq_of_dist_eq_zero :=  sorry
  edist := fun m n => ENNReal.ofReal (d₂ m n)
  edist_dist :=
  by
    intro m n; rfl

/-- We can now use `dist m n` but sometimes we will need to get back to the definition d₂-/
@[simp]
lemma dist_eq : dist m n = d₂ m n :=
by
  sorry

-- We now consider linear maps T: ℕ → ℕ, x ↦ ax + b

#check le_mul_of_pos_left
#check Function.IsFixedPt

/-- If a and b are non-zero then there are no fixed points -/
lemma not_IsFixedPt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :  ¬ (fun n => a*n + b).IsFixedPt k :=
by
  sorry

/-- d₂ is translation invariant-/
lemma shift_invariant (x y b : ℕ) : d₂ (x + b) (y + b) = d₂ x y :=
by
  sorry

/-- |n*(a - b)| = n*|a - b| -/
lemma ndist_mul : ndist (n * a) (n * b) = n * ndist a b :=
by
  sorry


#check ContractingWith
#check lipschitzWith_iff_dist_le_mul

/-- Any map x ↦ 2x + b is a contraction but has no fixed points for b ≠ 0 -/
lemma ContractingWith_mul_two (b : ℕ) : ContractingWith 2⁻¹ (fun n => 2*n + b):=
by
  sorry

/-
We are now ready to prove that (ℕ, d₂) is not complete.

Before we do this we need to give ℕ a UniformSpace structure in the correct way.

(Without this instance Lean will infer a different UniformSpace structure that
will break the proof of our final theorem.)
-/
noncomputable
instance twoUnif: UniformSpace ℕ  := PseudoMetricSpace.toUniformSpace

#check ContractingWith.fixedPoint_isFixedPt

theorem Nat_not_complete : ¬ CompleteSpace ℕ :=
by
  sorry

/-
Possible extension: continuity in (ℕ, d₂). We define continuity of f : ℕ → ℕ
at a point n : ℕ in the obvious way.

Prove that every polynomial with coefficients in ℕ is continuous everywhere.

You will probably want to prove some intermediate lemmas.
-/

open Metric
def CtsAt (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, dist x n < δ → dist (f x) (f n) < ε

open BigOperators Finset

/-- any polynomial over ℕ is cts everywhere in (ℕ, d₂)-/
theorem poly_cts (c : ℕ → ℕ) (m n : ℕ) : CtsAt (fun x => ∑ j in range m, c j * x ^ j) n :=
by
  sorry
