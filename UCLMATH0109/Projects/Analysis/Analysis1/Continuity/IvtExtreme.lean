import UCLMATH0109.Projects.Analysis.Analysis1.Continuity.Cts
import UCLMATH0109.Projects.Analysis.Analysis1.Sets.Bounds

namespace UCL
/- We prove the basic lemmas about cts functions on closed bounded intervals:


`ctsOn_imp_bdd` : if f is cts on [a,b] then its image is bounded on [a,b]

`extreme_value_max/min`: if f is cts  on [a,b] attains then it attains  its max/min

`intermediate_value`: the intermediate value theorem, if f is cts on [a,b] and f(a) < c < f(b) then
there exists d ∈ (a,b) such that f(d) = c

`ctsOn_imp_unifCts` : if f is cts on [a,b] then it is uniformly cts on [a,b] -/

open Nat Set




#check not_bddAbove_iff

-- The Archimedean property of ℝ
#check exists_nat_gt -- Given any `x ∈ ℝ` there exists `n : ℕ` such that `x < n`

#check sLim_Icc -- if `xₙ → l` and `∀ n, xₙ ∈ [a,b]` then `l ∈ [a,b]`

#check bd_imp_conv_sub -- Any bounded sequence has a convergent subsequence
#check bd_of_mem_Icc -- If a sequence is contained in an interval then it is bounded

/-
`ctsOn_imp_bddAbove` : If f is cts on [a,b] then it is bounded above on [a,b]

Proof Sketch:
By contradiction, so assume f is cts but not bounded above on [a,b]
i.e., ∀ z ∈ ℝ, ∃ x ∈ [a,b] such that z < f x.

So we can choose a sequence `xₙ ∈ [a,b]` such that `n < f xₙ`

Since `xₙ ∈ [a,b]` it is bounded so contains a subsequence `x∘g` that converges
to some value `c ∈ [a,b] `.

Now apply the definition of continuity of f at c with `ε = 1` to obtain:
`∀ (x : ℝ), x ∈ [a,b] → |x - c| < δ → |f x - f c| < 1`

By convergence of `(x∘g)ₙ` there exists `N : ℕ` such that
`∀ (n : ℕ), N ≤ n → |(x ∘ g) n - c| < δ`

Using the Archimedean property of `ℝ` there exists `M : ℕ` such that `1 + f c < M`

Taking `k = max N M ` we have `k < f (x∘g)ₖ`, `1 + f c < M` and `|f (x∘g)ₖ - f c| < 1` which
is impossible.
-/



/-- Any function that is CtsOn a closed bdd interval is bounded above -/
lemma ctsOn_imp_bddAbove (hf : CtsOn f (Icc a b)) : BddAbove (f '' Icc a b) :=
by
  sorry

/-- Any function that is CtsOn a closed bdd interval is bounded below -/
lemma ctsOn_imp_bddBelow (hf : CtsOn f (Icc a b)) : BddBelow (f '' Icc a b) :=
by
  sorry

/-- Any function that is CtsOn a closed bdd interval is bounded  -/
lemma ctsOn_imp_bdd (hf : CtsOn f (Icc a b)) : BddBelow (f '' Icc a b) ∧ BddAbove (f '' Icc a b) :=
by
  sorry

/-- Any function CtsOn [a,b] attains its maximum -/
theorem extreme_value_max (hab : a ≤ b) (hf : CtsOn f (Icc a b)) :
    ∃ c, c ∈ Icc a b ∧ ∀ x ∈ Icc a b, f x ≤ f c :=
by
  sorry

/-- Any function CtsOn [a,b] attains its min -/
lemma extreme_value_min (hab : a ≤ b) (hf : CtsOn f (Icc a b)) :
    ∃ d, d ∈ Icc a b ∧ ∀ x ∈ Icc a b, f d ≤ f x :=
by
  sorry

/-- The **intermediate value** theorem -/
theorem intermediate_value (hf : CtsOn f (Icc a b)) (hab : a < b) (hfab : f a < c ∧ c < f b) :
    ∃ x, x ∈ Ioo a b ∧ f x = c :=
by
  sorry


/--
A function f is uniformly cts on a set S iff ∀ε>0 ∃δ>0 ∀ x y ∈ S , |x - y| < δ → |f x - f y| < ε -/
def UnifCts (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, x ∈ S → y ∈ S → |x - y| < δ → |f x - f y| < ε

/-- If f is CtsOn a closed bounded interval then it is uniformly cts there -/
lemma ctsOn_imp_unifCts (hf : CtsOn f (Icc a b)) : UnifCts f (Icc a b) :=
by
  sorry
