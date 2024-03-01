import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.MinMax
import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.Kdiff
import Mathlib.Data.Nat.Factorial.Basic

namespace UCL
open scoped  Nat BigOperators

/-
 We prove Taylor's theorem for a general remainder function and then give
 the Cauchy and Lagrange forms
`taylor_general`
`taylor_cauchy`
`taylor_lagrange`
-/
open Nat Set


/--
If f is (k+1)dfble and g is dfble then for any i < k+1 we can take the derivative of (Δ i f)*g and
it is given by the product law -/
lemma Ideriv_prod_ikdfble_Idfble (k : ℕ) (hf : Ikdfble (k + 1) f a b) (hg : Idfble g a b) :
    ∀ i < k + 1,
      Ideriv (fun x => Δ i f x * g x) (fun x => Δ (i + 1) f x * g x + Δ i f x * Δ 1 g x)
        a b :=
by
  sorry

open Finset
/-- The Ideriv of a sum of dfble functions is the sum of Δ 1 of these functions -/
lemma Ideriv_sum_range {F : ℕ → ℝ → ℝ} (hdf : ∀ i < n, Idfble (F i) a b) :
    Ideriv (fun x => ∑ i in range n, F i x) (∑ i in range n, Δ 1 (F i)) a b :=
by
  sorry

/-- The sum of dfble functions is dfble -/
lemma Idfble_sum_range {F : ℕ → ℝ → ℝ} (hdf : ∀ i < n, Idfble (F i) a b) :
    Idfble (fun x => ∑ i in range n, F i x) a b :=
by
  sorry

/-- The derivative of (x - z)^k as a function of z -/
lemma Ideriv_pow_neg (k : ℕ) (x : ℝ) :
    Ideriv (fun z => (x - z) ^ k) (fun z => -k * (x - z) ^ (k - 1)) a b :=
by
  sorry



/-
The kth Taylor polynomial of f at a: `T(k,f,a,x) = ∑ i ≤ k, ∂ⁱ f(a)⬝(x - a)ⁱ/i!`

We usually think of this as a function of `x` with `a` constant, but we will need to
differentiate it with respect to `a` so we write it in the following form so that the `T k f x : ℝ → ℝ`
-/
/--
The kth Taylor polynomial of f at a
-/
@[simp]
noncomputable def T (k : ℕ) (f : ℝ → ℝ) (x a : ℝ) : ℝ :=
   ∑ i in range (k + 1), Δ i f a * (x - a) ^ i / i !


/-
The proof of Taylors lemma follows by applying Cauchy's Mean Value lemma to `T k f x`
-/

/-- Evaluating T (k,f,x,a) at a = x gives f(x)-/
@[simp]
lemma T_self (k : ℕ) (f: ℝ → ℝ) (x : ℝ) : T k f x x = f x:=
by
  sorry

/-- If g is dfble on (a,x) then its derivative at `c ∈ (a,x)` is `Δ 1 g c` -/
lemma IdfbleDerivDash (hgd : Idfble g a x) : ∀ c ∈ Ioo a x, ∂ g c (Δ 1 g c) :=
by
  sorry

/-- Having non-zero derivative on (a,x) is the same and having `Δ 1` non-zero on (a,x)-/
lemma dash_one_ne_zero_iff (hgd : Idfble g a x) :
    (∀ y ∈ Ioo a x, Δ 1 g y ≠ 0) ↔ ∀ y ∈ Ioo a x, ¬∂ g y 0 :=
by
  sorry

/-- The remainder term in the Taylor expansion written in terms of `T` -/
lemma taylor_help0 :  f x - T k f x a  = T k f x x - T k f x a :=
by
  sorry


/-- If the derivatives of f are cts on [a,x] then the kth Taylor polynomial is cts on [a,x]-/
lemma taylor_ctsOn (hfc : ∀ j < k + 1, CtsOn (Δ j f) (Icc a x)) :
    CtsOn (T k f x) (Icc a x) :=
by
  sorry

/-- The derivative of the k-th Taylor polynomial -/
lemma taylor_ideriv (hfd : Ikdfble (k + 1) f a x) :
    Ideriv (T k f x) (fun z => Δ (k + 1) f z * (x - z) ^ k / k !) a x :=
by
  sorry

/--
Taylor's theorem for a general remainder function g that is continuous on [a,x],
differentiable on (a,x) with g'(z) ≠ 0 on (a,x)
 -/
theorem taylor_general (f g : ℝ → ℝ) (hax : a < x) (hfd : Ikdfble (k + 1) f a x)
    (hfc : ∀ j < k + 1, CtsOn (Δ j f) (Icc a x)) (hgc : CtsOn g (Icc a x)) (hgd : Idfble g a x)
    (hgnz : ∀ c ∈ Ioo a x, Δ 1 g c ≠ 0) :
    ∃ z ∈ Ioo a x,
      f x - T k f x a = Δ (k + 1) f z * (x - z) ^ k * (Δ 1 g z)⁻¹ * (g x - g a) / k ! :=
by
  sorry

/--
**Cauchy remainder form of Taylor's theorem**
If a < x, f is (k+1)-differentiable on (a, x) and the its derivatives are continuous on [a,x] then
∃ z ∈ (a,x) such that:
-/
theorem taylor_cauchy (hax : a < x) (hfd : Ikdfble (k + 1) f a x)
    (hfc : ∀ j < k + 1, CtsOn (Δ j f) (Icc a x)) :
    ∃ z ∈ Ioo a x, f x - T k f x a = Δ (k + 1) f z * (x - z) ^ k * (x - a) / k ! :=
by
  sorry

/--
**Lagrange remainder form of Taylor's theorem**
If a < x, f is (k+1)-differentiable on (a, x) and its derivatives are continuous on [a,x] then
∃ z ∈ (a,x) such that:
-/
theorem taylor_lagrange (hax : a < x) (hfd : Ikdfble (k + 1) f a x)
    (hfc : ∀ j < k + 1, CtsOn (Δ j f) (Icc a x)) :
    ∃ z ∈ Ioo a x, f x - T k f x a = Δ (k + 1) f z * (x - a) ^ (k + 1) / (k + 1)! :=
by
  sorry
