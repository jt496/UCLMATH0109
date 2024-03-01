import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
import UCLMATH0109.Projects.Analysis.Analysis1.Sequences.Sequences


namespace UCL
open scoped BigOperators

open Nat

/-
Mathlib has predicates for boundedness but they are defined for sets rather than
sequences
-/
#check BddAbove
/-
eg. `BddAbove` is a predicate for whether a set has an upper bound

Here we will mainly use our own definitions (the exception to this is that we will need
to consider bounded sets for the monotone convergence lemma)

Beware: we use `Bd` as shorthand for bounded sequences while Mathlib uses `Bdd`
-/

/-- A real sequence is bounded above iff -/
def BdAbove (x : ℕ → ℝ) : Prop :=
  ∃ b, ∀ n, x n ≤ b

/-- A real sequence is bounded below iff -/
def BdBelow (x : ℕ → ℝ) : Prop :=
  ∃ b, ∀ n, b ≤ x n

/-- A real sequence is bounded iff -/
def Bd (x : ℕ → ℝ) : Prop :=
  BdAbove fun n => |x n|

/-- A real sequence is unbounded above iff -/
def UnbdAbove (x : ℕ → ℝ) : Prop :=
  ∀ b, ∃ n, b < x n

/-- A real sequence is unbounded below iff -/
def UnbdBelow (x : ℕ → ℝ) : Prop :=
  ∀ b, ∃ n, x n < b

/-- A real sequence is unbounded iff -/
def Unbd (x : ℕ → ℝ) : Prop :=
  UnbdAbove fun n => |x n|


/-- A sequence xₙ is unbounded above iff -xₙ is unbounded below -/
lemma unbdAbove_iff_neg_unbdBelow : UnbdAbove x ↔ UnbdBelow fun n => -x n :=
by
  sorry

/-- A sequence xₙ is unbounded below iff -xₙ is unbounded above -/
lemma unbdBelow_iff_neg_unbdAbove : UnbdBelow x ↔ UnbdAbove fun n => -x n :=
by
  sorry

/-- If a sequence is not UnbdAbove then it is BdAbove -/
lemma bdAbove_of_not_unbdAbove (hx : ¬UnbdAbove x) : BdAbove x :=
by
  sorry

/-- If a sequence is not UnbdBelow then it is BdBelow -/
lemma bdBelow_of_not_unbdBelow (hx : ¬UnbdBelow x) : BdBelow x :=
by
  sorry

/-- If a sequence is not unbd then it is bd -/
lemma bd_of_not_unbd (hx : ¬Unbd x) : Bd x :=
by
  sorry

/-- If a sequence is bounded it is bounded above -/
lemma bdAbove_of_bd (hb : Bd x) : BdAbove x :=
by
  sorry

/-- If a sequence is bounded it is bounded below -/
lemma bdBelow_of_bd (hb : Bd x) : BdBelow x :=
by
  sorry

/-- If a sequence is Unbd then it is UnbdAbove or UnbdBelow -/
lemma unbd_cases (hu : Unbd x) : UnbdAbove x ∨ UnbdBelow x :=
by
  sorry

/-- If a sequence is bounded above and below then it is bounded -/
lemma bd_of_bdBelow_and_above (ha : BdBelow x) (hb : BdAbove x) : Bd x :=
by
  sorry

open Set

/-- if a sequence always lies in [a,b] then it is bounded-/
lemma bd_of_mem_Icc (hx : ∀ n, x n ∈ Icc a b) : Bd x :=
by
  sorry
