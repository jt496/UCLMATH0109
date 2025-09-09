import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/-- The sequence `1/(n+1) → 0` -/
theorem one_over_nat : limₙ (fun n => (n + 1)⁻¹) 0 :=
by
  intro ε hε
  dsimp
  have h : ∃ N : ℕ, N > ε⁻¹
  · exact exists_nat_gt ε⁻¹
  obtain ⟨N,hN⟩ := h
  use N
  intro n hn
  rw [sub_zero]
  have h : |(n+1:ℝ)⁻¹| = (n+1:ℝ)⁻¹
  · rw [abs_eq_self]
    apply le_of_lt
    exact Nat.inv_pos_of_nat
  rw [h]
  have : n+1 > ε⁻¹
  · trans (N:ℝ)
    · norm_cast
      exact Nat.lt_succ.mpr hn
    · assumption
  exact inv_lt_of_inv_lt hε this
