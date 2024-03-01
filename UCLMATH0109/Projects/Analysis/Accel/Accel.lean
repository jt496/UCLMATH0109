import UCLMATH0109.Projects.Analysis.Analysis1.Series.Sums
import Mathlib.Data.Real.Pi.Leibniz
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic

open Nat hiding pow_zero pow_succ' pow_succ mul_le_mul_left
open UCL BigOperators Finset Real
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)
-- Porting note: See issue lean4#2220 fixed in current Mathlib

/-

The Leibniz formula for π is given by the following infinite series:

    `π/4 = ∑ (-1)^n /(2*n+1)`

which converges very slowly.

In this project we will consider other series expansions that converge faster.

In particular we will consider Euler's forward difference operator, which will allow us to
convert this slowly converging series (which after `n` terms has error approximately `1/2n`)
into a sum of two series both of `n` terms that has error at most `4⁻ⁿ`

We will use our own library for convergence of series
 (See Projects/Analysis/Analysis1/Series/Sums).

In particular, `limₙ x a` means that the limit of `x : ℕ → ℝ` as `n → ∞` is `a`
which is notation for `sLim x a`
-/
#print sLim
/-
We say that `Sums x` if the sequence of partial sums of `∑ x` tends to a limit -/
#print Sums

/-- We define the inverse odd sequence as -/
noncomputable
def iodd : ℕ → ℝ := fun n => (2*n + 1 : ℝ)⁻¹

@[simp]
lemma iodd' : iodd n = (2*n + 1 : ℝ)⁻¹:=
by
  sorry

/-- We define the alternating inverse odd sequence as -/
noncomputable
def ioddalt : ℕ → ℝ := fun n => (-(1:ℝ))^n * (2*n + 1 : ℝ)⁻¹

@[simp]
lemma ioddalt' : ioddalt n = (-(1 : ℝ))^n * (2*n + 1 : ℝ)⁻¹:=
by
  sorry

#check antitone_nat_of_succ_le
#check inv_le_inv_of_le

/-- Inverse odd sequence is decreasing -/
lemma leibniz_anti : Antitone iodd :=
by
  sorry

#check sLim_sandwich
#check sLim_const
#check one_over_nat

/-- Inverse odd sequence tends to 0 -/
lemma leibniz_zero : limₙ iodd 0 :=
by
  sorry

#check alternating_series_test

/-- The alternating inverse odd series converges -/
lemma leibniz_conv : Sums ioddalt :=
by
  sorry

#check sLim_iff_tendsto

/-- We use Mathlib to prove that `∑ (-1)ⁿ/(2n+1) = π / 4` -/
lemma leibniz_pi : limₙ (fun n =>  ∑ i in range n, ioddalt i) (π/4) :=
by
  sorry

#check alternating_series_test_with_bounds
#check sLim_unique

/--
The even and odd partial sums are lower/upper bounds for π/4, and the nth partial sum is
within distance 1/(2n+1) of π/4 -/
lemma leibniz_bounds (n : ℕ) :
∑ i in range (2*n), ioddalt i ≤  π/4 ∧ π/4 ≤ ∑ i in range (2*n+1), ioddalt i ∧
|π/4 - ∑ i in range n, ioddalt i| ≤ iodd n:=
by
  sorry

#check alternating_series_test_lower_error
/--
We can also prove a lower bound of the same order on consecutive error terms -/
lemma leibniz_bounds' (n : ℕ) : (iodd n)/2 ≤ max |π/4 - ∑ i in range n, ioddalt i|
|π/4 - ∑ i in range (n+1), ioddalt i| :=
by
  sorry

/-
So far we have established that `∑ (-1)^n/(2n+1)` converges to `π/4` and that the error
after summing `n` terms is at most `1/(2n+1)` and typically at least `1/(2(2n+1))`.

So convergence is slow (think about how long it would take to get accuracy of just 10
decimal places).

We want to find a new series that also converges to `π/4` for which the error term is
provably much better.

We will do this using Euler's forward difference operator `Δ` that maps a sequence
`x₀,x₁,x₂,...` to `x₁ - x₀, x₂ - x₁,...` -/

namespace Forward
open Function

def Δ : (ℕ → ℝ) → (ℕ → ℝ) := fun x => (fun n => (x (n + 1) - x n))

@[simp]
lemma Δ' : Δ x n = x (n+1) - x n :=
by
  sorry

/-
We will need some results about algebra of limits etc. -/
#check sLim_sub
#check sLim_add
#check sLim_of_tail_sLim
#check sLim_neg_iff
#check tail_sLim_of_sLim
#check sLim_congr
#check sums_terms_to_zero

/-- If `∑ (-1)ⁿ yₙ` converges to `L` then  `∑ (-1)ⁿ (Δ y)ₙ` converges to `y₀ - 2L` -/
lemma sums_Δ (y : ℕ → ℝ) (hs: limₙ (fun n => ∑ i in range n, (-(1:ℝ))^i * (y i)) L) :
limₙ (fun n => ∑ i in range n, (-(1:ℝ))^i * (Δ y i)) ((y 0) - 2*L) :=
by
  sorry

/-
The notation `Δ^[k] x` means iterate `Δ` `k` times. It's full name is `Nat.iterate`
-/
#check iterate
#check iterate_zero
#check iterate_succ_apply

/-- If `∑ (-1)ⁿ yₙ` converges to `L` then  `∑ (-1)ⁿ (Δᵏ y)ₙ` converges to
`(-2)ᵏ*L + ∑ j < k, (-2)^(k - (j+1)) (Δʲ y)₀` -/
lemma sums_Δ_iterate (L : ℝ) (y : ℕ → ℝ) (hs: limₙ (fun n => ∑ i in range n, (-(1:ℝ))^i * (y i)) L) (k : ℕ) :
limₙ (fun n => ∑ i in range n, (-(1:ℝ))^i * (Δ^[k] y i)) ((-(2:ℝ))^k*L + ∑  j in range k, (-(2:ℝ))^(k-(j+1))*(Δ^[j] y 0)) :=
by
  sorry

/-- So we have the following series expansion in terms of `Δᵏ` -/
lemma accel_pi (k : ℕ): limₙ (fun n => ∑ i in range n, (-(1:ℝ))^i * (Δ^[k] iodd i))
    ((-(2:ℝ))^k*(π/4) + ∑  j in range k, (-(2:ℝ))^(k-(j+1))*(Δ^[j] iodd 0)):=
by
  sorry

#check sLim_const_mul
#check sum_congr

/-- So for π/4 we have the following series expansion in terms of `Δᵏ` -/
lemma accel_pi' (k : ℕ): limₙ (fun n =>  ∑ i in range n, (2:ℝ)⁻¹^k * (-(1:ℝ))^(k+i) * (Δ^[k] iodd i))
    (π/4 + ∑  j in range k, (-(2:ℝ))⁻¹^(j+1)*(Δ^[j] iodd 0)):=
by
  sorry

/-
In order to use the previous result we need to find an explicit expression for the terms
of the accelerated sum.

We first compute `Δ^k y` in general, which involves binomial coefficients `n.choose k` -/

#check choose_succ_succ
#check choose_zero_right
#check choose_succ_self

/--
If we iterate the forward difference operator on a sequence `yₙ` then we obtain
`(Δᵏ y)ₙ = ∑ i ≤ k, (-1)ᵏ⁻ⁱ*(k.choose i)*yₙ₊ᵢ` -/
theorem iterate_Δ (y : ℕ → ℝ) (k n : ℕ) : Δ^[k] y n = ∑ i in range (k + 1), (-(1 : ℝ))^(k-i)*(k.choose i)*(y (n+i)):=
by
-- We will want to apply the inductive hypothesis to `Δ y` so we need to revert y before applying induction
  revert y
  sorry


/-
Beware the notation for the factorial of `k : ℕ` is `k !` not `k!` (note the space between `k` and `!`)
This is defined (as usual) by `0 ! = 1` and `(k+1) ! = (k + 1) * k !` -/

#check factorial_zero
#check choose_self

/-- We will express the terms of the accelerated series in a form that we can estimate (in order to compute rate of convergence)
∑ j ≤ k, (-1)ʲ k.choose j * (2i + 2j + 1)⁻¹ = 2ᵏk! ∏ j ≤ k,(2i+2j+1)⁻¹ -/
lemma alt_sum_eq_prod (k i : ℕ) : ∑ j in range (k+1),(-(1 : ℝ))^j*(2*(i + j) + 1 : ℝ)⁻¹*k.choose j  = (2:ℝ)^k* k ! * ∏ j in range (k+1), (2*(i + j) + 1 : ℝ)⁻¹:=
by
  sorry

#check pow_sub₀


/-- Write the finite part of the limit in a more standard form (i.e. without Δ)-/
lemma simplify_limit (k : ℕ) :  ∑  j in range k, (-(2:ℝ))⁻¹^(j+1)*(Δ^[j] iodd 0) =
-∑ j in range k, j ! * 2⁻¹* ∏ i in range (j+1),(2 * i  + 1 :ℝ)⁻¹:=
by
  sorry


/-
Convergence of the accelerated series in a useful form :
`∑ (-1)ⁱ k! /(2i+1)(2i+3)⋯(2i+2k+1)` converges to `π/4 - ∑ j ≤ k, j!/(2⬝1·3·5⋯(2j+1))`
-/
theorem accel_pi'' (k : ℕ): limₙ (fun n =>  ∑ i in range n, (-(1:ℝ))^i * k ! * ∏ j in range (k+1), (2*(i + j)+1 :ℝ)⁻¹)
    (π/4 - ∑ j in range k, j ! * 2⁻¹* ∏ i in range (j+1),(2 * i + 1 : ℝ)⁻¹):=
by
  sorry


/-
In order to bound the error of convergence of the accelerated series we will need
to show that the accelerated terms are both decreasing and tend to zero.

Note that that the `aᵢ` term (i.e. k!/(2i+1)(2i+3)⋯(2i+2k+1)) is
decreasing since `aᵢ₊₁/aᵢ = (2i+1)/(2i+2k+3) < 1` and tends to zero (since `aᵢ < (2i+1)ᵏ⁺¹` )

-/

/-- The accelerated `aᵢ` is decreasing -/
lemma anti_accel (k : ℕ) : Antitone (fun (i : ℕ) => k ! * ∏ j in range (k+1), (2*(i + j)+1 :ℝ)⁻¹):=
by
  sorry


/-- The accelerated `aᵢ` tends to zero -/
lemma sLim_zero_accel (k : ℕ) : limₙ (fun (i:ℕ) => k ! * ∏ j in range (k+1), (2*(i + j)+1 :ℝ)⁻¹) 0:=
by
  sorry

/-
The accelerated series has an error when summing `n` terms of at most
   `aₙ = k!/(2n+1)(2n+3)⋯(2n+2k+1) ≤ k!/(2n+1)^(k+1).`
In particular if we take `k = n` then the error after `n + 1` terms of the infinite series is at most  `4⁻ⁿ`
-/

/--
Bound on terms of `nth` acceleration of the series -/
lemma error_accel_help (n : ℕ) : n ! * ∏ j in range (n+1), (2*(n + 1 + j)+1 : ℝ)⁻¹ ≤ (4:ℝ)⁻¹^n:=
by
  sorry



/-- If we use the `n-th` acceleration then the error from taking the first `n + 1` terms of
the accelerated infinite series (together with the `n` terms of the finite sum) is at most `1/4ⁿ` -/
theorem accel_bounds (n : ℕ) : |π/4 - ∑ i in range n, i ! * 2⁻¹* ∏ j in range (i+1),(2 * j + 1 : ℝ)⁻¹
 -  ∑ i in range (n+1), (-(1:ℝ))^i * n ! * ∏ j in range (n+1), (2*(i + j)+1 :ℝ)⁻¹| ≤  (4:ℝ)⁻¹^n:=
by
  sorry


/-!
Possible extension: find and formalise an example of a convergent alternating series
for which applying Euler's forward difference operator does not change the
speed of convergence.
-/
