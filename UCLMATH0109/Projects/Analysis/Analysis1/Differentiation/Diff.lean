import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.IvtExtreme
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Limits

namespace UCL
open Real Set

/-

We develop the basic theory of differentiation of f : ℝ → ℝ at a point, before going
on to define this on open intervals these are `pderiv` and `Ideriv`


`dfble_imp_ctsAt` if f is differentiable at a then it is cts at a
`deriv_comp ` the chain rule at a point
`Ideriv_comp` the chain rule on an interval (a,b)
-/
open scoped Classical

/-- f'(a) = lim (f(a+h) - f(a))*h⁻¹ as h → 0 (if the limit exists) -/
def pderiv (f : ℝ → ℝ) (a d : ℝ) : Prop :=
  limₓ (fun h => (f (a + h) - f a) * h⁻¹) 0 d


notation "∂ " => pderiv

/-- A function f is differentiable at a iff the limit exists -/
def dfble (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ d, ∂ f a d

/-- Alternative expression for derivative: f'(a) = lim_{x → a} (f x - f a)/(x - a) -/
lemma pderiv_alt : ∂ f a d ↔ limₓ (fun x => (f x - f a) * (x - a)⁻¹) a d :=
by
  sorry

/-- If f and g are the same function and f'(a) = b and b = c then g'(a) = c-/
lemma pderiv_congr (hf : ∂ f a b) (heq1 : ∀ x, g x = f x) (heq2 : c = b) : ∂ g a c :=
by
  sorry

/-- If f'(a) exists and f = g then g'(a) exists -/
lemma dfble_congr (hf : dfble f a) (heq1 : ∀ x, g x = f x) : dfble g a :=
by
  sorry

/-- If f is differentiable at a then it is cts there -/
lemma dfble_imp_ctsAt (hd : dfble f a) : CtsAt f a :=
by
  sorry

/-- We often want to consider functions that are differentiable on an open
interval (a,b) in which case they are CtsOn on [c,d] for any a < c < b -/
lemma dfble_Ioo_ctsOn (hdf : ∀ x ∈ Ioo a b, dfble f x) (hc : a < c) (hd : d < b) :
    CtsOn f (Icc c d) :=
by
  sorry

/-- If f'(a) exists then f(a + h) → f(a) as h → 0 -/
lemma dfble_imp_fLim (hd : dfble f a) : limₓ (fun x => f (a + x)) 0 (f a) :=
by
  sorry

/-- the derivative if it exists is unique -/
lemma pderiv_unique : ∂ f a b → ∂ f a c → b = c :=
by
  sorry

/-- if f'(a) = b and g'(a) = c and f(x) = g(x) then b = c -/
lemma pderiv_unique_congr (hf : ∂ f a b) (hg : ∂ g a c) (heq1 : ∀ x, f x = g x) : b = c :=
by
  sorry

/-- if f(x) = c is constant the f' = 0-/
lemma  pderiv_const (a c : ℝ) : ∂ (fun _ => c) a 0 :=
by
  sorry

/-- if f(x) = c is constant on an open interval then it vanishes there -/
lemma pderiv_constIoo (hc : ∀ x ∈ Ioo a b, f x = c) : ∀ x ∈ Ioo a b, ∂ f x 0 :=
by
  sorry


/-- if f(x) = x then f'(x) = 1 -/
lemma pderiv_id (a : ℝ) : ∂ (fun x => x) a 1 :=
by
  sorry

/-- (f + g)'(a) = f'(a) + g'(a) -/
lemma pderiv_add (hf : ∂ f a b) (hg : ∂ g a c) : ∂ (f + g) a (b + c) :=
by
  sorry

/-- (f - g)'(a) = f'(a) - g'(a) -/
lemma pderiv_sub (hf : ∂ f a b) (hg : ∂ g a c) : ∂ (f - g) a (b - c) :=
by
  sorry

/-- if f'(a) = b then (cf)'(a)=cb -/
lemma  pderiv_const_mul (c : ℝ) (hf : ∂ f a b) : ∂ (fun x => c * f x) a (c * b) :=
by
  sorry

/-- if f'(a)= b then (-f)'(a) = -b  -/
lemma pderiv_neg (hf : ∂ f a b) : ∂ (fun x => -f x) a (-b) :=
by
  sorry

/-- If f'(a) = b then f(a + h) = f(a) + bh + ε(h) where ε(h)*h⁻¹ → 0 as h → 0 -/
lemma pderiv_linear (hf : ∂ f a b) : limₓ (fun h => (f (a + h) - (f a + b * h)) * h⁻¹) 0 0 :=
by
  sorry

/-- The product rule: (fg)'(a) = f'(a)g(a) + f(a)g'(a) (if f'(a) and g'(a) exist )-/
lemma pderiv_mul (hf : ∂ f a b) (hg : ∂ g a c) :
    ∂ (fun x => f x * g x) a (b * g a + f a * c) :=
by
  sorry


/-- the derivative of xⁿ at a is n * aⁿ⁻¹ -/
lemma pderiv_pow (a : ℝ) (n : ℕ) : ∂ (fun x => x ^ n) a (n * a ^ (n - 1)) :=
by
  sorry



open scoped BigOperators

open Finset Nat

/-- The derivative of a polynomial (∑ aᵢxⁱ)' = ∑ iaᵢx^(i-1) -/
lemma pderiv_poly (a : ℕ → ℝ) (n : ℕ) :
    ∂ (fun x => ∑ i in range n, a i * x ^ i) b (∑ i in range n, i * a i * b ^ (i - 1)) :=
by
  sorry

/-- the derivative of a polynomial without tsub -/
lemma pderiv_poly_succ (a : ℕ → ℝ) (n : ℕ) :
    ∂ (fun x => ∑ i in range (n + 1), a i * x ^ i) b
      (∑ i in range n, (i + 1) * a (i + 1) * b ^ i) :=
by
  sorry


/-- If f'(a) = b and f(a) ≠ 0 then (1/f)'(a) = -b/(f(a)²) -/
lemma pderiv_inv (hf : ∂ f a b) (hnz : f a ≠ 0) : ∂ (fun x => 1 / f x) a (-b / f a ^ 2) :=
by
  sorry

/--
The quotient rule: (f/g)'(a) = (f'(a)g(a) - f(a)g'(a))/(g(a)^2) (if f'(a) and g'(a) exist and g(a)≠0)-/
lemma pderiv_div (hf : ∂ f a b) (hg : ∂ g a c) (hnz : g a ≠ 0) :
    ∂ (fun x => f x / g x) a ((b * g a - f a * c) / g a ^ 2) :=
by
  sorry


/-- The chain rule if g'(a) = c and f'(g(a))= b then (f ∘ g)'(a) = b * c-/
lemma pderiv_comp (hf : ∂ f (g a) b) (hg : ∂ g a c) : ∂ (fun x => f (g x)) a (b * c) :=
by
  sorry

/-
Having established facts about derivatives related to f'(a) we prove some
 equivalent differentiability results -/

/-- f is dfble at a iff -f is -/
lemma dfble_neg_iff : dfble f a ↔ dfble (fun x => -f x) a :=
by
  sorry

/-- f(x) = b is dfble-/
lemma dfble_const (a b : ℝ) : dfble (fun _ => b) a :=
by
  sorry

/-- if f' exists then b*f' exists for b ∈ ℝ-/
lemma dfble_const_mul (b : ℝ) (hf : dfble f a) : dfble (fun x => b * f x) a :=
by
  sorry

-- f(x) = x is dfble
lemma dfble_id (a : ℝ) : dfble (fun x => x) a :=
by
  sorry

/-- if f and g are dfble at a then so is f + g -/
lemma dfble_add (hf : dfble f a) (hg : dfble g a) : dfble (f + g) a :=
by
  sorry

/-- if f and g are dfble at a then so is f + g -/
lemma dfble_sub (hf : dfble f a) (hg : dfble g a) : dfble (f - g) a :=
by
  sorry
