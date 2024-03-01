import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Series.CauchyProduct
import UCLMATH0109.Projects.Analysis.Analysis1.Series.Uniform
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Cts
import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.MinMax
import Mathlib.Data.Nat.Factorial.Basic
namespace UCL


/-
We now consider power series (but only around zero) i.e. of the form ∑ aₙ xⁿ

`PowSums a x` is our definition of `∑ aₙxⁿ converges at x for a sequence a : ℕ → ℝ

Inside the radius of convergence (which we manage to avoid formally defining) we have
`PowVal a x` is the value of the convergent series `∑ aₙxⁿ` we denote this by `∑ᵖ a x`

Our main results are :
`powVal_cts` power-series are cts inside the radius of convergence;

`powValDeriv` power-series are differentiable and the derivative is given by
differentiating term-by-term, inside the radius of convergence.
-/
open Finset Nat
open scoped Classical BigOperators
noncomputable section

/-- The power series of aₙ converges at a point x -/
def PowSums (a : ℕ → ℝ) (x : ℝ) : Prop :=
  Sums fun n => a n * x ^ n

lemma powSums_def (a : ℕ → ℝ) (x : ℝ) : PowSums a x ↔ Sums fun n => a n * x ^ n :=
by
  sorry

/-- Two identical power-series converge at x if one of them converges at x -/
lemma powSums_congr (hc : PowSums a x) (heq : ∀ n, b n = a n) : PowSums b x :=
by
  sorry

/-- Every power series converges absolutely at x = 0 -/
lemma pow_sums_zero (a : ℕ → ℝ) : Sums fun n => |a n * 0 ^ n| :=
by
  sorry

/--
If ∑ aₙxⁿ converges and |y| < |x| then ∑  ((n+k)!/n!) aₙ₊ₖ yⁿ converges  absolutely for any k ∈ ℕ -/
lemma abs_sums_fac_mul_of_abs_lt {a: ℕ → ℝ} (k : ℕ) (hx : Sums fun n => a n * x ^ n) (hxy : |y| < |x|) :
    Sums fun n => |n.ascFactorial k * a (n + k) * y ^ n| :=
by
  sorry

/-- If a power series converges at P ∈ ℝ and |x| < |P| then it converges absolutely at x -/
lemma abs_powSums_of_abs_lt (hc : PowSums a P) (hx : |x| < |P|) : Sums fun n => |a n * x ^ n| :=
by
  sorry

/-- If a power series converges at P ∈ ℝ and |x| < |P| then the power series converges at x -/
lemma powSums_of_abs_lt (hc : PowSums a P) (hlt : |x| < |P|) : PowSums a x :=
by
  sorry

/-
Our next definition is of the value of a power-series `∑ aₙxⁿ` at x.

We want this to be well-defined for all choices of `x ∈ ℝ` so we
define it to be  ∑ aₙxⁿ when x is inside the radius of convergence and `a₀` elsewhere.
[The choice of a₀ elsewhere means that if radius of convergence is zero then it still agrees with
 the limit at 0]
-/

/-- The value of the power-series at x, if x is inside the radius of convergence and a₀ otherwise -/
def PowVal (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ P, PowSums a P ∧ |x| < |P| then (powSums_of_abs_lt h.choose_spec.1 h.choose_spec.2).choose
  else a 0

notation "∑ᵖ " => PowVal

/--
Given a proof that x is inside the radius of convergence we have the limit of the partial sums equals
our definition of ∑ᵖ a x -/
lemma powVal_eq (h : ∃ P, PowSums a P ∧ |x| < |P|) :
    limₙ (fun n => ∑ i in range n, a i * x ^ i) (PowVal a x) :=
by
  sorry

/-- If x is not inside the radius of convergence then the default value is a₀ -/
lemma powVal_default (h : ¬∃ P, PowSums a P ∧ |x| < |P|) : ∑ᵖ a x = a 0 :=
by
  sorry

/-- Two power-series with the same coefficients have the same value at any point -/
lemma powVal_congr (heq : ∀ n, b n = a n) : ∑ᵖ a x = ∑ᵖ b x :=
by
  sorry

/-- Any powerseries evaluated at x = 0 equals a₀-/
lemma powVal_zero : ∑ᵖ a 0 = a 0 :=
by
  sorry

/-- If |y| ≤ |x| and  ∑ aₙxⁿ converges then so does ∑ aₙyⁿ and its value is `pow_val a y` -/
lemma powVal_eq_of_le (h : ∃ P, PowSums a P ∧ |x| < |P|) (hxy : |y| ≤ |x|) :
    limₙ (fun n => ∑ i in range n, a i * y ^ i) (∑ᵖ a y) :=
by
  sorry

/--
if ∑ aₙxⁿ converges inside the radius of convergence then there exists y in (|x|,P) such that the
power series converges at y -/
lemma powVal_exists_larger (h : PowSums a P ∧ |x| < |P|) :
    ∃ y, PowSums a y ∧ |y| < |P| ∧ |x| < |y| :=
by
  sorry

open Set

/-- A power series converges uniformly inside its radius of convergence -/
lemma powVal_unifConv (h : ∃ P, PowSums a P ∧ |x| < |P|) :
    UnifConv (fun n y => ∑ i in range n, a i * y ^ i) (∑ᵖ a) (Icc (-|x|) (|x|)) :=
by
  sorry

open Nat

/--
The term-by-term derivative of a power series converges uniformly inside the original series radius of convergence -/
lemma powVal_unifConv_deriv (h : ∃ P, PowSums a P ∧ |x| < |P|) :
    UnifConv (fun n y => ∑ i in range n, (i + 1) * a (i + 1) * y ^ i)
      (PowVal fun n => (n + 1) * a (n + 1)) (Icc (-|x|) (|x|)) :=
by
  sorry

/-- Power series are cts inside the radius of convergence -/
lemma powVal_cts (h : ∃ P, PowSums a P ∧ |x| < |P|) : CtsOn (PowVal a) (Icc (-|x|) (|x|)) :=
by
  sorry

/-- Power series can be differentiated term-by-term within the radius of convergence-/
lemma powValDeriv (h : ∃ P, PowSums a P ∧ |x| < |P|) :
    ∂ (∑ᵖ a) x (∑ᵖ (fun n => (n + 1) * a (n + 1)) x) :=
by
  sorry


/-- A power series is entire if it converges everywhere-/
def Entire (a : ℕ → ℝ) : Prop := ∀ x, PowSums a x

/-- If a power series converges everywhere then every x is inside its radius of convergence -/
lemma inside_of_entire {a : ℕ → ℝ} (x : ℝ) (he : Entire a) : ∃ P, PowSums a P ∧ |x| < |P| :=
by
  sorry

/-- Any entire power-series equals the limit of its partial sums everywhere -/
lemma powVal_eq_of_entire {a : ℕ → ℝ} (x : ℝ) (he : Entire a) :
    limₙ (fun n => ∑ i in range n, a i * x ^ i) (∑ᵖ a x) :=
by
  sorry
