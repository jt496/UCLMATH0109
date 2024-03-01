import Mathlib.Tactic.Basic
import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.Ideriv

namespace UCL
open scoped Classical
noncomputable section
open Set

/- We introduce the notion of local min/max and prove:
`Idfble_local_min` if f has a local min at c ∈ (a,b) and f is dfble on (a,b) then f'(c) = 0
`rolle` Rolles lemma
`cauchy_mean_value` the Cauchy Mean Value Theorem
`mean_value` the Mean Value Theorem
`Ideriv_pos_strict_mono` if f is cts on [a,b] and dfble on (a,b) and f'(x)>0 on (a,b)
 then f is strictly increasing on [a,b] -/
/- We introduce the notion of local min/max and prove:
`Idfble_local_min` if f has a local min at c ∈ (a,b) and f is dfble on (a,b) then f'(c) = 0
`rolle` Rolles lemma
`cauchy_mean_value` the Cauchy Mean Value Theorem
`mean_value` the Mean Value Theorem
`Ideriv_pos_strict_mono` if f is cts on [a,b] and dfble on (a,b) and f'(x)>0 on (a,b)
 then f is strictly increasing on [a,b] -/

/-- a is a local min of f iff -/
def LocalMin (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, |x - a| ≤ δ → f a ≤ f x

/-- a is a local max of f iff -/
def LocalMax (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ δ > 0, ∀ x, |x - a| ≤ δ → f x ≤ f a

/-- -f has a local min at a iff f has a local max at a -/
lemma localMin_iff : LocalMin (-f) a ↔ LocalMax f a :=
by
  sorry

/-- If f has a local min at c ∈ (a,b) and f is dfble on (a,b) then f'(c) = 0 -/
lemma IdfbleLocalMin (hf : Idfble f a b) (hc1 : c ∈ Ioo a b) (hc2 : LocalMin f c) : ∂ f c 0 :=
by
  sorry

/-- If f has a local max at c ∈ (a,b) and f is dfble on (a,b) then f'(c) = 0 -/
lemma IdfbleLocalMax (hf : Idfble f a b) (hc1 : c ∈ Ioo a b) (hc2 : LocalMax f c) : ∂ f c 0 :=
by
  sorry

/-- **Rolle's Theorem** if f is dfble on (a,b) and cts on [a,b] and f(a)=f(b)
then ∃ c ∈ (a,b) such f'(c) = 0 -/
theorem rolle (hab : a < b) (hfc : CtsOn f (Icc a b)) (hfd : Idfble f a b) (hfeq : f a = f b) :
    ∃ c, c ∈ Ioo a b ∧ ∂ f c 0 :=
by
  sorry

/-- **Cauchy's Mean Value Theorem**  -/
theorem cauchy_mean_value (hab : a < b) (hfc : CtsOn f (Icc a b)) (hfd : Idfble f a b)
    (hgc : CtsOn g (Icc a b)) (hgd : Idfble g a b) (hdnz : ∀ x ∈ Ioo a b, ¬∂ g x 0) :
    ∃ c, c ∈ Ioo a b ∧ ∃ d, ∂ f c d ∧ ∃ e, ∂ g c e ∧ d * e⁻¹ = (f b - f a) * (g b - g a)⁻¹ :=
by
  sorry


/-- the **Mean Value Theorem** follows easily from the Cauchy MVT-/
theorem mean_value (hab : a < b) (hfc : CtsOn f (Icc a b)) (hfd : Idfble f a b) :
    ∃ c, c ∈ Ioo a b ∧ ∂ f c ((f b - f a) * (b - a)⁻¹) :=
by
  sorry

/--
If f is cts on [a,b] and dfble on (a,b) and f'(x)>0 on (a,b) then f is strictly increasing on [a,b]-/
theorem ideriv_pos_strict_mono (hfc : CtsOn f (Icc a b)) (hd : Ideriv f e a b)
    (hdp : ∀ x ∈ Ioo a b, 0 < e x) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y → f x < f y :=
by
  sorry
