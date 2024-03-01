import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.Sequences
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.BoundedSeq

namespace UCL
/-
We develop the basic theory of subsequences and prove:

`mono_or_anti_subseq` every sequence contains an increasing or decreasing subsequence

`sLim_of_mono_bdAbove` : a monotone increasing sequence that is bounded above converges

`bd_imp_conv_sub` : any bounded sequence contains a convergent subsequence (Bolzano-Weierstrass)
-/

open scoped BigOperators

open Nat
/- --------------------------- **Subsequences** ----------------------------------------------
 If x: ℕ → ℝ is a real sequence and f : ℕ → ℕ then we can form a new real sequence: `x ∘ f`.

 This is *not* in general a subsequence of xₙ.

For a  `proper subsequence` we require f (n) < f(n + 1). In Lean this is called  `StrictMono f`

[However some properties of subsequences also hold for all `f: ℕ → ℕ`, in which case it is often
easier to prove the more general statement]
--------------------------------------------------------------------------------------------/

/-- Any subsequence of a bounded sequence is bounded -/
lemma subseq_bd_of_bd {f : ℕ → ℕ} (hb : Bd x) : Bd (x ∘ f) :=
by
  sorry

/-- Any StrictMono f: ℕ → ℕ grows at least as fast as `n ↦ n` -/
lemma strictMono_ge_id {f : ℕ → ℕ} (hsm : StrictMono f) : ∀ n, n ≤ f n :=
by
  sorry

/-- Any proper subsequence of a convergent sequence converges to the same limit -/
lemma subseq_sLim_of_sLim {f : ℕ → ℕ} (hx : limₙ x a) (hsm : StrictMono f) : limₙ (x ∘ f) a :=
by
  sorry

/--
If even and odd subsequences both converge to the same value then so does the original sequence -/
lemma even_odd_sLim_imp (he : limₙ (x ∘ fun n => 2 * n) a)
    (ho : limₙ (x ∘ fun n => 2 * n + 1) a) : limₙ x a :=
by
  sorry

/-- ¬ unBdAbove iff BdAbove -/
lemma exists_iff_not_unbdAbove : ¬UnbdAbove x ↔ ∃ b, ∀ n, x n ≤ b :=
by
  sorry

/-- If a sequence x is unbounded above then its tail, `xₙ₊ₘ` is unbounded above for any m -/
lemma tail_unb_abv_of_unb_abv (hbd : UnbdAbove x) :
∀ m, UnbdAbove fun n => x (n + m) :=
by
  sorry

/-- If `x ∶ ℕ → ℝ` is unbounded above then for any `b : ℝ` and `m : ℕ` there exists
`n : ℕ` such that `m ≤ n` and `b ≤ xₙ`
-/
lemma tail_unb_abv_of_unb_abv' (hbd : UnbdAbove x) :
∀ b, ∀ m, ∃ n, m ≤ n ∧ b < x n:=
by
  sorry

/-
If `x : ℕ → ℝ` is unbounded above then it contains a strictly increasing proper subsequence `x ∘ f`,
i.e. we have  `f : ℕ → ℕ` such that  `StrictMono f` and `StrictMono (x ∘ f)`.

This is pretty obvious mathematically, but its slightly less obvious how to express this in Lean.

The main challenge is how to describe a subsequence `f : ℕ → ℕ`.

We can do this using induction (otherwise known as recursion)

In order to define the subsequence `f : ℕ → ℕ` we need to give
a value for `f(0)` which we set to be `0` and then given a value for `f(n)` we
define `f(n+1)` using the fact that since `x` is unbounded so its tail is unbounded and
hence `∀ m : ℕ, ∀ b : ℝ, ∃ t : ℕ, b < x (t + m)` so we set `m = f(n)` and `b = x(f(n))`
and `choose` `t` such that `x(f(n)) < x (t + f(n))`. Note that this implies `t ≠ 0`
and hence we can define `f(n+1) = t + f(n)`.
-/


/--
If x: ℕ → ℝ is a real sequence that is unbounded above, then it contains a
proper monotone increasing subsequence -/
lemma exists_strictMono_of_unbounded_above (hb : UnbdAbove x) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (x ∘ f) :=
by
  sorry

#check Antitone

/-- A sequence xₙ is strictly increasing iff -xₙ is strictly decreasing -/
lemma strictMono_iff_neg {f : ℕ → ℕ} {x : ℕ → ℝ}: StrictMono ((fun n => -x n) ∘ f) ↔ StrictAnti (x ∘ f) :=
by
  sorry

/--
Any unbounded real sequence contains either a strictly increasing / strictly decreasing subsequence-/
lemma strictMono_or_anti_subseq_of_unbd (hx : Unbd x) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (StrictMono (x ∘ f) ∨ StrictAnti (x ∘ f)) :=
by
  sorry

/-- We say `m is a peak of xₙ` if  `xₘ ≥ xₙ` for all `m ≤ n`  -/
def Peak (x : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n, m ≤ n → x n ≤ x m

/-- If m is the last peak of the sequence x then -/
def LastPeak (x : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ n, m < n → ∃ k, n ≤ k ∧ x n < x k

@[simp]
lemma LastPeak'  (x : ℕ → ℝ) (m : ℕ) : LastPeak x m ↔ ∀ n, m < n → ∃ k, n ≤ k ∧ x n < x k :=
by
  sorry

/-- If `xₙ` has a last peak at `m` then `xₙ₊ₘ₊₁` has no peaks-/
lemma tail_of_lastPeak (hlp : LastPeak x m) : ∀ t, ∃ n, x (t + m + 1) < x (n + m + 1) ∧ t < n :=
by
  sorry

/-- Given a strictMono subsequence in xₙ₊ₘ₊₁ we have a strictMono subsequence in xₙ -/
lemma smono_of_tail_smono (x : ℕ → ℝ) (m : ℕ)
    (hsm : ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (x ∘ fun n => f n + m + 1)) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ StrictMono (x ∘ g) :=
by
  sorry

/-- Every sequence either contains a strictly increasing or monotonic decreasing subsequence -/
lemma mono_or_anti_subseq (x : ℕ → ℝ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (StrictMono (x ∘ f) ∨ Antitone (x ∘ f)) :=
by
  sorry

/- For the next result we need to use the fact that any nonempty set of reals that is bounded above has
a supremum. This requires us to use Lean's version of boundedness for sets (rather than our version
for sequences).

In Lean functions are total, so if we want to define "Sup S" to be the supremum of a set of real
numbers S, then it needs to be defined for *all* sets of reals (including those that are empty or
unbounded above.) However Lean has some useful results telling us that "Sup S" is what you think it
is in the case that S is nonempty and bounded above.

Two key results here are :

lemma `Real.isLUB_sSup` (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) : IsLUB S (Sup S)`

Where `IsLUB` tells us that Sup S is, in this case, a least upper bound of S, and

lemma `lt_isLUB_iff` (h : isLUB s a) : b < a ↔ ∃ c ∈ s, b < c  -/

#check IsLUB
#check Real.isLUB_sSup
#check lt_isLUB_iff

/-- **The monotone convergence lemma** (for increasing sequences):
if xₙ is increasing and bounded above then it converges -/
theorem sLim_of_mono_bdAbove (hm : Monotone x) (hb : BdAbove x) : ∃ a, limₙ x a :=
by
  sorry

/-- If xₙ is bounded below and decreasing then it converges -/
lemma sLim_of_anti_bdBelow (hm : Antitone x) (hb : BdBelow x) : ∃ a, limₙ x a :=
by
  sorry

/-- **Bolzano-Weierstraass** Any bounded sequence contains a convergent subsequence-/
theorem bd_imp_conv_sub (hb : Bd x) : ∃ f : ℕ → ℕ, ∃ a, StrictMono f ∧ limₙ (x ∘ f) a :=
by
  sorry
