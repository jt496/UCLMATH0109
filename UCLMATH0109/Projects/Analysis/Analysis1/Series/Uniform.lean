import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Series.Sums
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Cts
import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.MinMax
namespace UCL

/-
We define the notion of uniform convergence of fₙ on a set S

Our mains results are:
`ctsOn_of_unifConv_ctsOn`: if fₙ is ctsOn s for each n,  and fₙ → g uniformly on s, then g is ctsOn on s

`Ideriv_unifConv`: if fₙ → g and f'ₙ → h uniformly on [a,b] then g is differentiable at every x ∈ (a,b) and g'(x) = h(x)

`weierstrass_M` : the Weierstrass M-test for uniform convergence of a series -/

open scoped BigOperators

open Finset

/-- A sequence of functions fₙ converges uniformly to g on a set s iff  -/
def UnifConv (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ x ∈ s, ∀ n, N ≤ n → |f n x - g x| < ε

/-- If fₙ → g uniformly on s then the fₙ(x) is "uniformly cauchy" on s -/
lemma unif_cauchy (hu : UnifConv f g s) :
    ∀ ε : ℝ, ε > 0 → ∃ N, ∀ x ∈ s, ∀ m n, N ≤ m → N ≤ n → |f n x - f m x| < ε :=
by
  sorry

/-- If fₙ is ctsOn s for each n, and fₙ → g uniformly on s, then g is ctsOn  s-/
theorem ctsOn_of_unifConv_ctsOn (hu : UnifConv f g s) (hc : ∀ n, CtsOn (f n) s) : CtsOn g s :=
by
  sorry

/-- If fₙ → g uniformly on s then it converges pointwise to g on s -/
lemma point_conv_of_unifConv (hu : UnifConv f g s) : ∀ x ∈ s, limₙ (fun n => f n x) (g x) :=
by
  sorry

/-- If fₙ → g uniformly then so does fₙ₊ₖ for every k -/
lemma tail_uconv_of_uconv (k : ℕ) (hu : UnifConv f g s) : UnifConv (fun n => f (n + k)) g s :=
by
  sorry

/-- If fₙ₊ₖ → g uniformly for any k, then so does fₙ-/
lemma uconv_of_tail_uconv (k : ℕ) (hu : UnifConv (fun n => f (n + k)) g s) : UnifConv f g s :=
by
  sorry

open Set

/--
The next lemma is part of the proof of `Ideriv_unifConv` using the MVT to prove a useful inequality  -/
lemma Ideriv_unifConv_help (hfu : UnifConv f g (Icc a b)) (hfud : UnifConv f' h (Icc a b))
    (hfd : ∀ n, Ideriv (f n) (f' n) a b) :
    ∀ c ∈ Ioo a b,
      ∀ ε > 0,
        ∃ M,
          ∀ n ≥ M,
            ∀ x ∈ Ioo a b, x ≠ c → |(g x - g c) * (x - c)⁻¹ - (f n x - f n c) * (x - c)⁻¹| ≤ ε :=
by
  sorry

/-

Our next result will allow us to differentiate power-series term-by term.

[Comment: The partial sums of ∑∞ a x are `0, a₀, a₀+a₁x, a₀+a₁x+a₂x²,...` so the derivatives of these are
`0, 0 , a₁, a₁+2a₂x ...`. Unfortunately the latter is awkward to express as the sequence of partial sums of
a power series in our definition of ∑∞ a x, to avoid this awkwardness elsewhere we state this result with
the derivative of fₙ₊₁ = fₙ'. This makes our application to power-series very easy.]

-/

/--
If fₙ → g and f'ₙ → h uniformly on [a,b] then g is differentiable at every x ∈ (a,b) and g'(x) = h(x)-/
theorem Ideriv_unifConv (hfu : UnifConv f g (Icc a b)) (hfud : UnifConv f' h (Icc a b))
    (hfd : ∀ n, Ideriv (f (n + 1)) (f' n) a b) : Ideriv g h a b :=
by
  sorry

/-
We incorporate the hypothesis of pointwise convergence to g
in our next result rather than make this an existence result
(existence of the pointwise limit follows  very easily from the other hypotheses
using the comparison test but we typically know the pointwise limit exists).
-/

/-- The **Weierstrass M-test** for uniform convergence of a series -/
theorem weierstrass_M {f : ℕ → ℝ → ℝ} (s : Set ℝ) (M : ℕ → ℝ) (hb : ∀ n, ∀ x ∈ s, |f n x| ≤ M n) (hM : Sums M)
    (hp : ∀ x ∈ s, limₙ (fun n => ∑ i in range n, f i x) (g x)) :
    UnifConv (fun n x => ∑ i in range n, f i x) g s :=
by
  sorry
