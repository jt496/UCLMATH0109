import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.CauchySequences

namespace UCL
open Nat

/-

 We introduce the standard definition of the limit `f(x) → l as x → a`

 We will call this `fLim` (limit of a function) with the notation `limₓ` to distinguish it from
 sLim limₙ (limit of a sequence).

 We then prove the basic facts about limits (most follow immediately from the analogous facts
 about limits of sequences)

 Some slightly more interesting results proved include:

 `fLim_iff_sLim` : f → l as x → a  iff  for every real sequence xₙ that is never equal to a,
 xₙ → a  implies  f(xₙ) →  l (as sequences)

 `fLim_congr_nbhd` if f and g agree on a δ-nbhd of a and f → b as x → a then g → b as x → a

 `fLim_ne_nbhd` if f → b as x → a and b ≠ c then ∃ δ-nbhd of a such that f(x) ≠ c for x ≠ a in the nbhd

 `fLim_shift` f(a+x) → l as x → b iff  f(x) → b as x → a + b

 `fLim_comp` if g → b as x → a and f → c as x → b then f ∘ g → c as x → a.
-/
def fLim (f : ℝ → ℝ) (a l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a → |x - a| < δ → |f x - l| < ε

notation "limₓ " => fLim

/-- Sometimes useful to have ≤ δ -/
def fLim' (f : ℝ → ℝ) (a l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a → |x - a| ≤ δ → |f x - l| < ε

lemma fLim_iff_fLim' : limₓ f a l ↔ fLim' f a l :=
by
  sorry

/-- f(x) → l as x → a iff for every sequence xₙ → a , with xₙ ≠ a we have f(xₙ) → l  -/
lemma fLim_iff_sLim :
    limₓ f a l ↔ ∀ x : ℕ → ℝ, (∀ n, x n ≠ a) → limₙ x a → limₙ (f ∘ x) l :=
by
  sorry

/-- limits are unique -/
lemma fLim_unique (hb : limₓ f a b) (hc : limₓ f a c) : b = c :=
by
  sorry

/-- If f → b as x → a and g x = f x for all x ≠ a then g → b as x → a  -/
lemma fLim_congr (hb : limₓ f a b) (heq1 : ∀ x, x ≠ a → g x = f x) (heq2 : c = b) :
    limₓ g a c :=
by
  sorry

/-- If f → b as x → a and c < b then ∃ δ-nbhd of a such that  c < f(x)  for x ≠ a in the nbhd  -/
lemma lt_fLim_nbhd (hf : limₓ f a b) (hlt : c < b) :
    ∃ δ > 0, ∀ x, x ≠ a → |x - a| ≤ δ → c < f x :=
by
  sorry

/-- If f → b as x → a and b < c then ∃ δ-nbhd of a such that f(x) < c  for x ≠ a in the nbhd  -/
lemma fLim_lt_nbhd (hf : limₓ f a b) (hlt : b < c) :
    ∃ δ > 0, ∀ x, x ≠ a → |x - a| ≤ δ → f x < c :=
by
  sorry

/-- If f → b as x → a and b ≠ c then ∃ δ-nbhd of a such that f(x) ≠ c for x ≠ a in the nbhd  -/
lemma fLim_ne_nbhd (hf : limₓ f a b) (hne : b ≠ c) :
    ∃ δ > 0, ∀ x, x ≠ a → |x - a| ≤ δ → f x ≠ c :=
by
  sorry

/-
Occaisionally we need a more refined equivalence of limits that only involves
checking equality of the functions in some δ-nbhd of a point
(see for example the  quotient rule for derivatives where this is very helpful)
-/

/-- If f and g agree in a punctured δ-nbhd of a and f → b as x → a and c = b then g → c as x → a -/
lemma fLim_congr_nbhd (hb : limₓ f a b) (hδ : 0 < δ)
    (heq1 : ∀ x, x ≠ a → |x - a| < δ → g x = f x) (heq2 : c = b) : limₓ g a c :=
by
  sorry

/-- f(a + x) → l as x → b iff  f(x) → b as x → a + b -/
lemma fLim_shift (a b : ℝ) (f : ℝ → ℝ) (l : ℝ) :
    limₓ (fun x => f (a + x)) b l ↔ limₓ f (a + b) l :=
by
  sorry

/-- f x = b → b as x → a -/
lemma fLim_const (a b : ℝ) : limₓ (fun _ => b) a b :=
by
  sorry

/-- x → a as x → a -/
lemma fLim_id (a : ℝ) : limₓ (fun x => x) a a :=
by
  sorry

/-- if f → b and g → c as x → a then f + g → b + c as x → a -/
lemma fLim_add (hf : limₓ f a b) (hg : limₓ g a c) :
    limₓ (fun x => f x + g x) a (b + c) :=
by
  sorry

/-- if f → b and g → c as x → a then f - g → b - c as x → a -/
lemma fLim_sub (hf : limₓ f a b) (hg : limₓ g a c) :
    limₓ (fun x => f x - g x) a (b - c) :=
by
  sorry

/-- if f → b and g → c as x → a then f * g → b * c as x → a-/
lemma fLim_mul (hf : limₓ f a b) (hg : limₓ g a c) :
    limₓ (fun x => f x * g x) a (b * c) :=
by
  sorry

/-- If f(x) → b as x → a then (f(x))ᵏ → bᵏ as x → a -/
lemma fLim_pow (hf : limₓ f a b) : limₓ (fun x => f x ^ k) a (b ^ k) :=
by
  sorry

/-- if f → b and g → c as x → a and c ≠ 0 then  f / g → b / c as x → a  -/
lemma fLim_div (hf : limₓ f a b) (hg : limₓ g a c) (hc : c ≠ 0) :
    limₓ (fun x => f x / g x) a (b / c) :=
by
  sorry

/-- If f → b as x → a and b ≠ 0 then (f x)⁻¹ → b⁻¹ as x → a  -/
lemma fLim_inv (hf : limₓ f a b) (hne : b ≠ 0) : limₓ (fun x => (f x)⁻¹) a b⁻¹ :=
by
  sorry

/-- f → b as x → a iff -f → -b as x → a -/
lemma fLim_neg_iff : limₓ f a b ↔ limₓ (fun x => -f x) a (-b) :=
by
  sorry

/-- If f → b as x → a then |f| → |b| as x → a -/
lemma fLim_abs (hf : limₓ f a b) : limₓ (|f|) a (|b|) :=
by
  sorry

/-- Composition of limits  -/
lemma fLim_comp (hf : limₓ f b (f b)) (hg : limₓ g a b) : limₓ (f ∘ g) a (f b) :=
by
  sorry
