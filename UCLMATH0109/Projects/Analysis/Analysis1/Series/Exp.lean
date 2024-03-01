import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Series.CauchyProduct
import UCLMATH0109.Projects.Analysis.Analysis1.Series.Uniform
import UCLMATH0109.Projects.Analysis.Analysis1.Series.PowerSeries
import Mathlib.Data.Nat.Choose.Sum
namespace UCL

/- We define the exponential function and prove some basic properties:

`exp_add` :  eˣ⁺ʸ = eˣeʸ
`exp_deriv`: ∂ exp x (exp x)

 -/
open scoped Nat BigOperators

open Nat Finset

/-- the exponential series converges absolutely for all real x -/
lemma sums_abs_exp (x : ℝ) : Sums fun n => |x ^ n / n !| :=
by
  sorry

/-- The exponential series converges everywhere -/
lemma entire_exp (x : ℝ) : Sums fun n => x ^ n / n ! :=
by
  sorry

/-- the exponential function -/
noncomputable def exp (x : ℝ) : ℝ :=
  (entire_exp x).choose

/--
`exp x` is the limit of `∑ i < n, x^i/i!` -/
lemma exp' (x : ℝ) : limₙ (fun n => ∑ i in range n, x ^ i / i !) (exp x) :=
by
  sorry

/-- eˣ⁺ʸ = eˣeʸ -/
lemma exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
by
  sorry


/-- The power-series defining exp (x) converges everywhere -/
lemma entire_pow_val_exp : Entire fun n => 1 / n ! :=
by
  sorry

/-- exp x = the value of the power-series evaluated at x -/
lemma exp_eq_powVal (x : ℝ) : exp x = ∑ᵖ (fun n => 1 / n !) x :=
by
  sorry

/-- The derivative of exp x is exp x -/
lemma expDeriv (x : ℝ) : ∂ exp x (exp x) :=
by
  sorry
