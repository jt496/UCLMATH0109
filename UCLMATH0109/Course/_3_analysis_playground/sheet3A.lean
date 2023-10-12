import Mathlib.Tactic


/-

Examples of using refine / congr! / convert etc

-/

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε


notation "limₙ " => sLim 

-- 01 
example (x y: ℕ → ℝ) (hxa: limₙ x a) (ha: b = a) (hxy: ∀ n, y n = x n) : limₙ y b :=
by
  -- you can do this with `rw`, but `convert` is more direct
  convert hxa
  sorry


