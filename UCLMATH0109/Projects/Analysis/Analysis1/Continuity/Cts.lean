import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Limits


namespace UCL
open Set Nat


/- We develop the basic definitions and results about continuous functions at a point a
 `CtsAt f a` and on a set s `CtsOn f s`

Rather than simply defining `f is ctsAt a` iff `limₓ f a (f a)` we define it directly
The reason for this is that if we used `limₓ f a (f a)` then we would be carrying around
a redundant `x ≠ a` condition that we would need to discharge
-/
/-- The standard definition of continuity of f at a -/
def CtsAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

/-- right-cts at a -/
def RctsAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → a ≤ x → |f x - f a| < ε

/-- left-cts at b -/
def LctsAt (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - b| < δ → x ≤ b → |f x - f b| < ε

/-- f is ctsAt a iff its limit at a is its value there -/
lemma ctsAt_iff_fLim_eq : CtsAt f a ↔ fLim f a (f a) :=
by
  sorry

/--
If two functions are equal everywhere and one is ctsAt a and a = b then the second is ctsAt b -/
lemma ctsAt_congr (hf : CtsAt f a) (he1 : ∀ x, g x = f x) (he2 : b = a) : CtsAt g b :=
by
  sorry

/-- f is ctsAt a iff it is sequentially ctsAt a -/
lemma ctsAt_iff_sLim : CtsAt f a ↔ ∀ x : ℕ → ℝ, limₙ x a → limₙ (f ∘ x) (f a) :=
by
  sorry

/-- if f is constant then it is ctsAt -/
lemma ctsAt_const : CtsAt (fun _ => b) a :=
by
  sorry

/-- f(x) = x is ctsAt a-/
lemma ctsAt_id (a : ℝ) : CtsAt (fun x => x) a :=
by
  sorry

/-- if f and g are ctsAt a so is f + g  -/
lemma ctsAt_add (hf : CtsAt f a) (hg : CtsAt g a) : CtsAt (fun x => f x + g x) a :=
by
  sorry

/-- if f and g are ctsAt a so is (f - g) -/
lemma ctsAt_sub (hf : CtsAt f a) (hg : CtsAt g a) : CtsAt (fun x => f x - g x) a :=
by
  sorry

/-- if f is CtsAt a and b ∈ ℝ then so is  f * b -/
lemma ctsAt_mul_const (b : ℝ) (hf : CtsAt f a) : CtsAt (fun x => f x * b) a :=
by
  sorry

/-- if f and g are ctsAt a so is f * g -/
lemma ctsAt_mul (hf : CtsAt f a) (hg : CtsAt g a) : CtsAt (fun x => f x * g x) a :=
by
  sorry

/-- If f is ctsAt a and k ∈ ℕ then fᵏ is ctsAt a -/
lemma ctsAt_pow (hf : CtsAt f a) (k : ℕ) : CtsAt (fun x => f x ^ k) a :=
by
  sorry

/-- if f and g are ctsAt a and g(a) ≠ 0 then so is f / g -/
lemma ctsAt_div (hf : CtsAt f a) (hg : CtsAt g a) (hd : g a ≠ 0) : CtsAt (fun x => f x / g x) a :=
by
  sorry

/-- f is ctsAt a iff -f is ctsAt a -/
lemma ctsAt_neg_iff : CtsAt f a ↔ CtsAt (fun x => -f x) a :=
by
  sorry

/-- If f is ctsAt a then so is |f| -/
lemma ctsAt_abs (hf : CtsAt f a) : CtsAt (|f|) a :=
by
  sorry

/-- Composition of ctsAt functions is ctsAt -/
lemma ctsAt_comp (hf : CtsAt f (g a)) (hg : CtsAt g a) : CtsAt (f ∘ g) a :=
by
  sorry

open scoped BigOperators

open Finset

/-- Any finite sum of ctsAt functions is ctsAt -/
lemma ctsAt_sum {h : ℕ → ℝ → ℝ} (hc : ∀ i < n, CtsAt (h i) b) : CtsAt (fun x => ∑ i in range n, h i x) b :=
by
  sorry

/-- Polynomials are ctsAt -/
lemma ctsAt_poly {c : ℕ → ℝ} (b : ℝ) (n : ℕ) : CtsAt (fun x => ∑ i in range n, c i * x ^ i) b :=
by
  sorry

/-
  Continuity on a set: `CtsOn`
-/
/--
for each a ∈ s given ε > 0 there exists δ >0  st for x ∈ s, and δ-close to a, f x is ε-close to f a -/
def CtsOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ a ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, |x - a| < δ → |f x - f a| < ε

/-- Allowing |x - a| = δ will sometimes be useful help-/
def CtsOn' (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ a ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, |x - a| ≤ δ → |f x - f a| < ε

/-- CtsOn and CtsOn' are equivalent -/
lemma ctsOn_iff_ctsOn' (f : ℝ → ℝ) (s : Set ℝ) : CtsOn f s ↔ CtsOn' f s :=
by
  sorry

/-- If f is CtsOn on s and f = g then g is CtsOn on s -/
lemma ctsOn_congr (hf : CtsOn f s) (he1 : ∀ x, g x = f x) : CtsOn g s :=
by
  sorry

/-- f is CtsOn on s iff it is sequentially CtsAt a for all a ∈ s -/
lemma ctsOn_iff_sLim :
    CtsOn f s ↔ ∀ a ∈ s, ∀ x : ℕ → ℝ, (∀ n, x n ∈ s) → limₙ x a → limₙ (f ∘ x) (f a) :=
by
  sorry

/-- f is CtsOn on s iff -f is CtsOn on s -/
lemma ctsOn_neg_iff : CtsOn f s ↔ CtsOn (fun x => -f x) s :=
by
  sorry

/-- if f is constant then it is CtsOn any set s -/
lemma ctsOn_const : CtsOn (fun _ => b) s :=
by
  sorry

/-- f(x) = x is CtsOn on any set s -/
lemma ctsOn_id (s : Set ℝ) : CtsOn (fun x => x) s :=
by
  sorry

/-- if f and g are CtsOn on s then so is f + g -/
lemma ctsOn_add (hf : CtsOn f s) (hg : CtsOn g s) : CtsOn (fun x => f x + g x) s :=
by
  sorry

/-- Given a finite set of CtsOn functions their sum is CtsOn -/
lemma ctsOn_sum_range {h : ℕ → ℝ → ℝ} (hh : ∀ i < n, CtsOn (h i) s) :
    CtsOn (fun x => ∑ i in range n, h i x) s :=
by
  sorry

/-- if f and g are CtsOn s then so is f - g -/
lemma ctsOn_sub (hf : CtsOn f s) (hg : CtsOn g s) : CtsOn (fun x => f x - g x) s :=
by
  sorry

/-- if f is CtsOn s so is  f * b for any constant b -/
lemma ctsOn_mul_const (b : ℝ) (hf : CtsOn f s) : CtsOn (fun x => f x * b) s :=
by
  sorry

/-- if f and g are CtsOn s so is  f * g -/
lemma ctsOn_mul (hf : CtsOn f s) (hg : CtsOn g s) : CtsOn (fun x => f x * g x) s :=
by
  sorry

/-- If f is CtsOn s and k ∈ ℕ then fᵏ is CtsOn s -/
lemma ctsOn_pow (hf : CtsOn f s) (k : ℕ) : CtsOn (fun x => f x ^ k) s :=
by
  sorry

/-- if f and g are CtsOn s and g(x) ≠ 0 on s then f / g is CtsOn s -/
lemma ctsOn_div (hf : CtsOn f s) (hg : CtsOn g s) (hd : ∀ x ∈ s, g x ≠ 0) :
    CtsOn (fun x => f x / g x) s :=
by
  sorry

/-- Polynomials are CtsOn -/
lemma ctsOn_poly {s : Set ℝ} {n : ℕ} {c : ℕ → ℝ} : CtsOn (fun x => ∑ i in range n, c i * x ^ i) s :=
by
  sorry

lemma ctsOn_ss (hc : CtsOn f s) (hss : t ⊆ s) : CtsOn f t :=
by
  sorry
