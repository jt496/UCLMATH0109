import Mathlib.Tactic.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.CauchySequences
import Mathlib.Data.Nat.Factorial.Basic
namespace UCL

/-

We introduce the definition of a convergent infinite sum and prove basic results such as:

`abs_sums_imp` absolute convergence implies convergence
`comparison_test` if 0 ≤ xₙ ≤ yₙ and ∑ yₙ converges then ∑ xₙ converges
`comparison_test'` if 0 ≤ xₙ ≤ yₙ and ∑ xₙ diverges then ∑ yₙ converges

`harmonic_diverges` ∑ 1/n diverges
`sums_recip_sq` ∑ 1/n^2 converges
`sum_geo_sLim_lt_one` if |a|<1 then 1+ a+a^2+... converges to 1/(1-a)

`ratio_test` the ratio test for convergence
`ratio_test'`the ratio test for divergence

`sums_asc_fac_mul_geo` if |a|<1 then ∑ (n)(n+1)... (n+k) a^n converges for any k ∈ ℕ
(this will help us to differentiate power series later) -/

open Nat Finset

open BigOperators

/-- A sequence xₙ `sums` iff x₀ + x₁ + x₂ + ... + xₙ converges to a limit -/
def Sums (x : ℕ → ℝ) : Prop :=
  ∃ a, limₙ (fun n => ∑ i in range n, x i) a

/-- If ∑ xₙ converges and yₙ = xₙ for all n then ∑ yₙ converges -/
lemma sums_congr (hs : Sums x) (he : ∀ n, y n = x n) : Sums y :=
by
  sorry

/-- If ∑ xₙ converges so does  ∑ xₘ₊ₙ, for any m -/
lemma tail_sums (m : ℕ) (hx : Sums x) : Sums fun n => x (n + m) :=
by
  sorry

/-- The `Cauchy criterion` for convergence of a sum:
∑ xₙ converges iff ∀ε>0, ∃N,∀ n≥ N,∀ p, |xₙ + xₙ₊₁ + ... + xₙ₊ₚ₋₁| < ε    -/
lemma cauchy_criterion :
    Sums x ↔ ∀ ε : ℝ, ε > 0 → ∃ N, ∀ n p, N ≤ n → |∑ i in Ico n (n + p), x i| < ε :=
by
  sorry

/-- If ∑ |xₙ| converges then ∑ xₙ converges -/
lemma abs_sums_imp (hs : Sums fun n => |x n|) : Sums x :=
by
  sorry

/--
If a sum converges absolutely then any sum over a Finset ℕ is bounded above by the infinite sum -/
lemma sum_abs_sums_bd {x : ℕ → ℝ}(hs : limₙ (fun n => ∑ i in range n, |x i|) a) (s : Finset ℕ) :
    ∑ i in s, |x i| ≤ a :=
by
  sorry

/-- if ∑ xₙ converges then for any f : ℕ → ℕ (not necessarily monotone)  ∑ n ≤ i < n + f(n) xᵢ → 0 -/
lemma sums_Ico_to_zero (hx : Sums x) (f : ℕ → ℕ) :
    limₙ (fun n => ∑ i in Ico n (n + f n), x i) 0 :=
by
  sorry

/-- If ∑ xₘ₊ₙ converges for any m then so does ∑ xₙ -/
lemma sums_of_tail_sums (m : ℕ) (hx : Sums fun n => x (n + m)) : Sums x :=
by
  sorry

/-- If a nonnegative sum converges then it converges absolutely -/
lemma abs_sums_of_sums_nonneg (hs : Sums x) (hp : ∀ n, 0 ≤ x n) : Sums fun n => |x n| :=
by
  sorry

/-- The zero sum converges (to zero ..)-/
lemma sums_zero : Sums fun _ => 0 :=
by
  sorry

/-- If the terms are eventually zero (ie finite sum) then the sum converges -/
lemma sums_eventually_zero (m : ℕ) (he : ∀ n, m ≤ n → x n = 0) : Sums x :=
by
  sorry

/-- the terms of a convergent sum tend to zero -/
lemma sums_terms_to_zero (hx : Sums x) : limₙ (fun n => x n) 0 :=
by
  sorry

/-- A sum of nonnegative reals converges iff it sequence of partial sums is bounded above-/
lemma sums_nonneg_iff_bdAbove (hp : ∀ n, 0 ≤ x n) :
    Sums x ↔ BdAbove fun n => ∑ i in range n, x i :=
by
  sorry


/-- If 0 ≤ xₙ ≤ yₙ for all n, and ∑ yₙ converges then so does ∑ xₙ  -/
lemma comparison_test (hp : ∀ n, 0 ≤ x n) (hxy : ∀ n, x n ≤ y n) (hs : Sums y) : Sums x :=
by
  sorry

/-- If 0 ≤ xₙ ≤ yₙ for all m ≤ n, and ∑ yₙ converges then so does ∑ xₙ  -/
lemma comparison_from_test (hs : Sums y) (m : ℕ) (hp : ∀ n, m ≤ n → 0 ≤ x n)
    (hxy : ∀ n, m ≤ n → x n ≤ y n) : Sums x :=
by
  sorry

/-- If ∑ xₙ and ∑ yₙ converge then so does ∑ xₙ + yₙ -/
lemma sums_add (hx : Sums x) (hy: Sums y): Sums fun n => x n +y n :=
by
  sorry

/-- if ∑ xₙ converges then so does ∑ (xₙ*c) for any constant c -/
lemma sums_mul_const (c : ℝ) (hs : Sums x) : Sums fun n => x n * c :=
by
  sorry

/-- if ∑ xₙ converges then so does ∑ (-xₙ)   -/
lemma sums_neg (hs : Sums x) : Sums fun n => -x n  :=
by
  sorry

/-- If ∑ xₙ and ∑ yₙ converge then so does ∑ xₙ - yₙ -/
lemma sums_sub (hx : Sums x) (hy: Sums y): Sums fun n => x n - y n :=
by
  sorry

/-- if ∑ (xₙ*c) converges for any c ≠ 0 then so does ∑ xₙ -/
lemma sums_of_sums_mul_const (c : ℝ) (hc : c ≠ 0) (hs : Sums fun n => x n * c) : Sums x :=
by
  sorry

/-- If ∑ yₙ converges, 0 ≤ xₙ ≤ yₙ and 0 < yₙ for all n,  and xₙ/yₙ → l  then ∑ xₙ converges -/
lemma sLim_comp_test (l : ℝ) (hs : Sums y) (hp : ∀ n, 0 ≤ x n) (hpy : ∀ n, 0 < y n)
    (hl : limₙ (fun n => x n / y n) l) : Sums x :=
by
  sorry

/-- If 0 ≤ xₙ ≤ yₙ for all n, and ∑ xₙ diverges then so does ∑ yₙ  -/
theorem comparison_test' (hp : ∀ n, 0 ≤ x n) (hxy : ∀ n, x n ≤ y n) (hs : ¬Sums x) : ¬Sums y :=
by
  sorry

/-- The harmonic series 1/(n+1) diverges -/
lemma harmonic_diverges : ¬Sums fun n => (n + 1)⁻¹ :=
by
  sorry

/-- ∑ 1/(n+1)n converges -/
lemma telescope : Sums fun n => ((n : ℝ) + 1)⁻¹ * (n:ℝ)⁻¹ :=
by
  sorry

/-- The ∑ 1/(n+1)^2 converges by comparison with ∑ 1/n(n+1)-/
lemma sums_recip_sq : Sums fun n => ((n:ℝ) + 1)⁻¹ ^ 2 :=
by
  sorry

/-- 1 + a + a^2 + ... + a^n = (a^n - 1)/(a - 1) for a ≠ 1 -/
lemma sum_geo {a : ℝ} (ha : a ≠ 1) (n : ℕ) : ∑ k in range n, a ^ k = (a ^ n - 1) / (a - 1) :=
by
  sorry

/-- aⁿ → 0 for any a ∈ ℝ satisfying |a| < 1-/
lemma geo_lt_one_sLim_zero (ha : |a| < 1) : limₙ (fun n => a ^ n) 0 :=
by
  sorry

/-- the infinite geometric series 1 + a + a^2 + ... converges to (1-a)⁻¹ for |a| < 1 -/
lemma sum_geo_sLim_lt_one (ha : |a| < 1) : limₙ (fun n => ∑ i in range n, a ^ i) (1 - a)⁻¹ :=
by
  sorry

/-- Geometric series converges for |a| < 1-/
theorem sums_geo (ha : |a| < 1) : Sums fun n => a ^ n :=
by
  sorry

/-- Convert a bound from the ratio test to a bound on terms of the form  c^n * d -/
lemma ratio_sLim_help {x : ℕ → ℝ} (hnz : ∀ n, x n ≠ 0) (hr : 0 < r)
    (hN : ∀ n, N ≤ n → |x (n + 1) / x n| ≤ r) : ∀ n, N ≤ n → |x n| ≤ r ^ n * (r⁻¹ ^ N * |x N|) :=
by
  sorry

/-- Getting from the sLim to a form we can use to compare to geometric series-/
lemma ratio_sLim_imp {x : ℕ → ℝ} (hnz : ∀ n, x n ≠ 0) (hx : limₙ (fun n => |x (n + 1) / x n|) (|l|))
    (hl : |l| < 1) : ∃ N, ∃ c d, |c| < 1 ∧ ∀ n ≥ N, |x n| ≤ c ^ n * d :=
by
  sorry

/-- **The Ratio test** for convergence -/
theorem ratio_test (hnz : ∀ n, x n ≠ 0) (hx : limₙ (fun n => |x (n + 1) / x n|) (|l|))
    (hl : |l| < 1) : Sums (|x|) :=
by
  sorry

/-- **The Ratio test** for divergence -/
theorem ratio_test' (hnz : ∀ n, x n ≠ 0) (hx : limₙ (fun n => |x (n + 1) / x n|) l)
    (hl : 1 < |l|) : ¬Sums x :=
by
  sorry

/- n.asc_factorial k is the ascending factorial sometimes denoted (n)ₖ and is 1 for k = 0 and otherwise
(n+1)(n+2)...(n+k) they occur when you differentiate polynomials/power-series -/

/-- For any |a|< 1 and k ∈ ℕ, the sum ∑ (n)ₖ aᵏ converges absolutely-/
lemma sums_asc_fac_mul_geo (ha : |a| < 1) (k : ℕ) : Sums fun n => |n.ascFactorial k * a ^ n| :=
by
  sorry


/-- Alternating series test with bounds on even/odd partial sums.
 If `xₙ` is decreasing (antitone) and converges to zero then `∑ (-1)ⁿ xₙ` converges and for any n,
 the even and odd partial sums satisfy: s₂ₙ ≤ L ≤ s₂ₙ₊₁ and |L - sₙ| ≤ xₙ₊₁ -/
lemma alternating_series_test_with_bounds  (hanti : Antitone x) (hlim: limₙ x 0) :
∃ L, limₙ (fun n => ∑ i in range n, (-1)^i * (x i)) L ∧ ∀ n, (∑ i in range (2*n), (-1)^i * (x i) ≤ L) ∧ (L ≤ ∑ i in range (2*n+1), (-1)^i * (x i) ) ∧ |L - ∑ i in range n,  (-1)^i * (x i)| ≤ x n:=
by
  sorry

/- Alternating series test: if `xₙ` is decreasing (antitone) and converges to zero then
`∑ (-1)ⁿ xₙ` converges -/
theorem alternating_series_test (hanti : Antitone x) (hlim: limₙ x 0) : Sums (fun n =>  (-1)^n * (x n)) :=
by
  sorry

/-- Lower bound on error in alternating series test
 If `xₙ` is decreasing (antitone) and converges to zero then the sum of consecutive error terms is `xₙ` so the maximum of
 consecutive errors is at least `xₙ/2`  -/
lemma alternating_series_test_lower_error  (hanti : Antitone x) (hlim: limₙ x 0) :
∃ L, limₙ (fun n => ∑ i in range n, (-1)^i * (x i)) L ∧ ∀ n, (x n) / 2 ≤ max |L - ∑ i in range n,  (-1)^i * (x i)|  |L - ∑ i in range (n+1),  (-1)^i * (x i)| :=
by
  sorry
