import UCLMATH0109.Projects.Analysis.Analysis1.Series.Sums

namespace UCL
open BigOperators

open Finset Nat Real

/-
In order to define the exponential function we need to be able to multiply infinite series

We do this using the `cauchy product`.

Our main lemma in this file is `mertens` which gives a sufficient condition for the
sum of the cauchy product to converge to the product of the two sums -/

/-- The Cauchy product of two real sequences -/
@[reducible]
def cauchyProd (x y : ℕ → ℝ) : ℕ → ℝ := fun n => ∑ i in range (n + 1), x i * y (n - i)

@[simp]
lemma cauchyProd' (x y : ℕ → ℝ) : cauchyProd x y n  = ∑ i in range (n + 1), x i * y (n - i):=
by
  sorry

/-- The cauchy product can be indexed in reverse order -/
@[simp]
lemma cauchyProd_reflect : cauchyProd x y n = ∑ i in range (n + 1), x (n - i) * y i :=
by
  sorry

/-- The sequence of partial sums of a sequence x : ℕ → ℝ
Note that our partial sums consist of the sum of the first n terms of x
so  always start with the empty sum `∑ i in range 0, x i` -/
@[reducible]
def psum (x : ℕ → ℝ) : ℕ → ℝ := fun n => ∑ i in range n, x i

/-- the psum sum to n + 1 is the (psum sum to n) + xₙ -/
lemma psum_succ {x : ℕ → ℝ} {n : ℕ} : psum x (n + 1) = psum x n + x n :=
by
  sorry

/-- ∑ i ≤ n, ∑  j ≤ i, x_j y_{i-j} = ∑  i ≤ n, x_{n-i}(y_0+..+y_{i}) -/
lemma psum_cauchyProd :
    ∑ i in range (n + 1), (cauchyProd x y) i =
      ∑ i in range (n + 1), x (n - i) * ∑ j in range (i + 1), y j :=
by
  sorry

/-- If ∑ |xᵢ| converges then its limit is nonnegative -/
lemma sums_nonneg {x : ℕ → ℝ} (hsA: limₙ (fun n => ∑ i in range n, |x i|) A): 0 ≤ A:=
by
  sorry

/-
The next result is most of the proof of Mertens lemma

If `∑ xₙ = a` and `∑ yₙ = b` and the first sum converges absolutely then
`∑ i ≤ n, xₙ₋ᵢ ∑ j ≤ i, yⱼ  -  ∑ i ≤ n, xᵢ b )` tends to 0 as n → ∞

Note this easily implies that the Cauchy product of x and y converges to a * b.

We first massage the partial sum into:
`∑ i in range (n + 1), x (n - i) * (∑ j in range (i + 1), y j - b)`
and convert the `limₙ` to `limₙ' ` (which uses `... ≤ ε` rather than `... < ε`)

Let `∑ |xₙ| = A`, `∑ xₙ = a` and `∑ yₙ = b`. Given `ε > 0` we obtain `N : ℕ` from the definition
of `∑ yₙ = b` with `ε` equal to `ε / 2(A + 1)`

We obtain a positive bound `0 < B` such that for all n `|∑ i ≤ n,yᵢ - b| < B`

Since `∑ |xₙ|` converges its terms tend to zero so we can obtain
`M : ℕ` such that for `n ≥ M` we have `|xₙ| < ε / (2(N + 1)B)`

We can now use `N + M`. The rest of the proof is a long calculation which you should do
in detail on paper before starting to write any code.

-/
lemma mertens_lem (hx : limₙ (fun n => ∑ i in range n, x i) a)
    (hy : limₙ (fun n => ∑ i in range n, y i) b) (ha : Sums fun n => |x n|) :
    limₙ (fun n => ∑ i in range (n + 1), x (n - i) * psum y (i + 1) - psum x (n + 1) * b)
      0 :=
by
  sorry

/--
If ∑ aₙ → a and ∑ bₙ → b and ∑ |aₙ| converges then ∑ cₙ → a*b where cₙ = ∑ aᵢbₙ₋ᵢ is the cauchy product -/
theorem mertens (hx : limₙ (fun n => ∑ i in range n, x i) a)
    (hy : limₙ (fun n => ∑ i in range n, y i) b) (ha : Sums fun n => |x n|) :
    limₙ (fun n => ∑ i in range n, cauchyProd x y i) (a * b) :=
by
  sorry
