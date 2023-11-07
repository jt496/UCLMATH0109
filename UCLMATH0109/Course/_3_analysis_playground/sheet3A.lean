import Mathlib.Tactic


/-
TODO: Add more examples of using refine / congr! / convert etc

-/

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

-- 01
lemma sLim_congr  (hxa: limₙ x a)  (hxy: ∀ n, y n = x n) (ha: b = a) : limₙ y b :=
by
  -- you can do this with `rw`, but `convert` is more direct
  convert hxa
  sorry


-- 02
example (hl : limₙ x a) : limₙ (2*x) (2*a) :=
by
  intro ε hε ; dsimp
  obtain ⟨N,hN⟩ :=hl (ε/2) (by positivity)
  use N
  intro n hn
  norm_cast
  rw [← mul_sub, abs_mul]
  norm_num
  specialize hN n hn
  linarith


-- 03 You can do this with `apply?` but you need to choose the correct suggestion carefully
example (a b c d : ℝ) (ha : d ≤ a) : d ≤ min (max a b) (max a c) :=
by
  sorry


-- 05 If `xₙ → a` then `xₙ₊ₘ → a` for all m
lemma tail_sLim_of_sLim (m : ℕ) (hx : limₙ x a) : limₙ (fun n => x (n + m)) a :=
by
  intro ε hε; dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), N ≤ n → |x (n + m) - a| < ε
  -- You now need to use `hx : limₙ x a` to obtain a suitable `N`
  -- To finish the proof `apply?` may be useful.
  sorry
