import Mathlib.Tactic.Basic
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
  --  We need to use the Archimedean property of ℝ, ie for any r ∈ ℝ there 
  --  exists N ∈ ℕ such that r < N
  have h : ∃ N : ℕ, N > ε⁻¹
  · --exact?
    exact exists_nat_gt ε⁻¹
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  rw [sub_zero]
  -- Very useful to know that the absolute value makes no difference here.
  have hsp : |(n + 1 : ℝ)⁻¹| = (n + 1: ℝ)⁻¹
  · -- apply?
    refine abs_eq_self.mpr ?hsp.a
    apply le_of_lt
    -- exact?
    exact Nat.inv_pos_of_nat
  rw [hsp]; clear hsp
  -- work out the next line using `apply?`
  refine inv_lt_of_inv_lt hε ?h.h
  trans ↑N
  exact hN
  norm_cast
  -- work out the next line using `exact?`
  exact Nat.lt_succ.mpr hn
