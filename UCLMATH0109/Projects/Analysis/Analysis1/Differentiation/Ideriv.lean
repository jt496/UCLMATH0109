import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.Diff

namespace UCL
open Set Real

#check ∂

/-
We now start considering derivatives defined on open intervals rather than
 at points.
-/
open scoped BigOperators

section Interval
/-- The derivative of f is d on (a,b)-/
@[reducible]
def Ideriv (f d : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Ioo a b, ∂ f x (d x)

/-- f is differentiable on (a,b)-/
def Idfble (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ d : ℝ → ℝ, Ideriv f d a b

/-- If f has derivative h on (a,b) and g = f on (a,b) and h = j on (a,b) then g
has derivative j on (a,b) -/
lemma Ideriv_congr' (hfd : Ideriv f h a b) (heq1 : ∀ x ∈ Ioo a b, g x = f x)
    (heq2 : ∀ x ∈ Ioo a b, j x = h x) : Ideriv g j a b :=
by
  sorry

/-- If f has derivative h on (a,b) and g = f on (a,b)  then g
has derivative h on (a,b) -/
lemma Ideriv_congr (hfd : Ideriv f h a b) (heq1 : ∀ x ∈ Ioo a b, g x = f x) : Ideriv g h a b :=
by
  sorry

/-
We now prove simple lemmas that move our pointwise derivative results to the interval (a,b)
All the proofs should be something like
  `intros x hx, exact __result_for_point_wise___`
-/

/-- If f' = d and f' = e on (a,b) then d = e on (a,b) -/
lemma Ideriv_unique (hf : Ideriv f d a b) (hg : Ideriv f e a b) : ∀ x ∈ Ioo a b, d x = e x :=
by
  sorry

/-- The derivative of the constant function is zero on (a,b) -/
lemma Ideriv_const (a b : ℝ) (c : ℝ) : Ideriv (fun _ => c) 0 a b :=
by
  sorry

/-- The derivative of the x ↦ x is 1 on (a,b) -/
lemma Ideriv_id (a b : ℝ) : Ideriv (fun z => z) 1 a b :=
by
  sorry

/-- Sum rule for derivatives on (a,b) -/
lemma Ideriv_add (hf : Ideriv f d a b) (hg : Ideriv g e a b) :
    ∀ x ∈ Ioo a b, ∂ (f + g) x (d x + e x) :=
by
  sorry

/-- Sub rule for derivatives on (a,b) -/
lemma Ideriv_sub (hf : Ideriv f d a b) (hg : Ideriv g e a b) :
    ∀ x ∈ Ioo a b, ∂ (f - g) x (d x - e x) :=
by
  sorry

/-- if f' = d on (a,b) then (cf)'(x)=c*(d(x)) on (a,b) -/
lemma Ideriv_const_mul (c : ℝ) (hf : Ideriv f d a b) :
    ∀ x ∈ Ioo a b, ∂ (fun z => c * f z) x (c * d x) :=
by
  sorry

/-- if f' = d on (a,b) then (-f)'=-d on (a,b) -/
lemma Ideriv_neg (hf : Ideriv f d a b) : ∀ x ∈ Ioo a b, ∂ (fun z => -f z) x (-d x) :=
by
  sorry

/-- if f' = d on (a,b) then limₓ [f(x + h) - (f(x) + d(x)*h)] * h⁻¹ = 0  on (a,b) -/
lemma Ideriv_linear (hf : Ideriv f d a b) :
    ∀ x ∈ Ioo a b, limₓ (fun h => (f (x + h) - (f x + d x * h)) * h⁻¹) 0 0 :=
by
  sorry

/-- Product rule for derivatives on (a,b) -/
lemma Ideriv_mul (hf : Ideriv f d a b) (hg : Ideriv g e a b) :
    ∀ x ∈ Ioo a b, ∂ (fun z => f z * g z) x (d x * g x + f x * e x) :=
by
  sorry

/-- Derivative of xⁿ on (a,b)-/
lemma Ideriv_pow (n : ℕ) : ∀ x ∈ Ioo a b, ∂ (fun z => z ^ n) x (n * x ^ (n - 1)) :=
by
  sorry

section Withfinset

open Finset


/-- Derivative of a polynomial on (a,b)-/
lemma Ideriv_poly (c : ℕ → ℝ) (n : ℕ) :
    ∀ x ∈ Set.Ioo a b,
      ∂ (fun z => ∑ i in range n, c i * z ^ i) x (∑ i in range n, i * c i * x ^ (i - 1)) :=
by
  sorry

/-- Derivative of polynomial on (a,b) (without tsub) -/
lemma Ideriv_poly_succ (c : ℕ → ℝ) (n : ℕ) :
    ∀ x ∈ Set.Ioo a b,
      ∂ (fun z => ∑ i in range (n + 1), c i * z ^ i) x
        (∑ i in range n, (i + 1) * c (i + 1) * x ^ i) :=
by
  sorry

end Withfinset

/-- If f' = d on (a,b) and f(x) ≠ on (a,b) then (1/f)'(x) = (-d(x)/f²(x)) on (a,b)-/
lemma IderivInv (hf : Ideriv f d a b) (hnz : ∀ x ∈ Ioo a b, f x ≠ 0) :
    ∀ x ∈ Set.Ioo a b, ∂ (fun z => 1 / f z) x (-d x / f x ^ 2) :=
by
  sorry

/-- Quotient rule for derivatives on (a,b) -/
lemma IderivDiv (hf : Ideriv f d a b) (hg : Ideriv g e a b) (hnz : ∀ x ∈ Ioo a b, g x ≠ 0) :
    ∀ x ∈ Set.Ioo a b, ∂ (fun z => f z / g z) x ((d x * g x - f x * e x) / g x ^ 2) :=
by
  sorry

/-- Chain rule for derivatives on (a,b) -/
lemma IderivComp {d : ℝ → ℝ} (hf : ∀ x ∈ Ioo a b, ∂ f (g x) (d x)) (hg : Ideriv g e a b) :
    ∀ x ∈ Set.Ioo a b, ∂ (f ∘ g) x (d x * e x) :=
by
  sorry

/-- Derivative restricted to sub open interval -/
lemma Ideriv_inside (hfd : Ideriv f d a b) (hau : a ≤ u) (hvb : v ≤ b) : Ideriv f d u v :=
by
  sorry

/-
Equivalent Idfble results which follow quickly from the above.
-/
/-- If is Idfble on (a,b) iff -f is -/
lemma Idfble_neg_iff : Idfble f a b ↔ Idfble (fun z => -f z) a b :=
by
  sorry


/-- The constant function is Idfble on (a,b) -/
lemma Idfble_const (a b : ℝ) (c : ℝ) : Idfble (fun _ => c) a b :=
by
  sorry

/-- If f is Idfble on (a,b) then so is c * f -/
lemma Idfble_const_mul (c : ℝ) (hf : Idfble f a b) : Idfble (fun x => c * f x) a b :=
by
  sorry

/-- The identity function is Idfble on (a,b) -/
lemma Idfble_id : Idfble (fun x => x) a b :=
by
  sorry

/-- If f and g are Idfble on (a,b) then so is f + g -/
lemma Idfble_add (hf : Idfble f a b) (hg : Idfble g a b) : Idfble (f + g) a b :=
by
  sorry

/-- If f and g are Idfble on (a,b) then so is f - g -/
lemma Idfble_sub (hf : Idfble f a b) (hg : Idfble g a b) : Idfble (f - g) a b :=
by
  sorry

/-- If f is Idfble on (a,b)  and f = g on (a,b) then g is Idfble -/
lemma Idfble_congr (hfd : Idfble f a b) (heq1 : ∀ x ∈ Ioo a b, g x = f x) : Idfble g a b :=
by
  sorry

lemma Idfble_mul (hf : Idfble f a b) (hg : Idfble g a b) : Idfble (fun x => f x * g x) a b :=
by
  sorry

/-- xⁿ is Idfble -/
lemma Idfble_pow (n : ℕ) : Idfble (fun z => z ^ n) a b :=
by
  sorry

/-- If f is Idfble on (a,b) and (u,v) ⊆ (a,b) then f is Idfble on (u,v)
-/
lemma Idfble_inside {f : ℝ → ℝ} (hfd : Idfble f a b) (hau : a ≤ u) (hev : v ≤ b) : Idfble f u v :=
by
  sorry

end Interval
