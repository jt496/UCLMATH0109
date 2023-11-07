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


-- 04 Try to solve this using only `congr!`, `symm` and `exact`
example (a b c d : ℕ) (h1 : a = b) (h2 : c = d): (a + b + a)*(c + d) = (a + b + b)*(c + c):=
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

/- If `a b : ℕ` then `a ∣ b` is `∃ c, b = a * c`
Note `∣` is not `|` it is `\|`
-/

-- 06 Use `trans` to solve this
example (a b c d : ℕ) (ha: a ∣ b) (hb : b ∣ c) : a ∣ d*c :=
by
  sorry


-- 07
example (a b c d: ℕ) (ha : c ∣ a) (hb : c ∣ b) (hd : b ∣ d):  c ∣ a + d :=
by
  sorry

/-
If `a b : ℤ` then `a % b` is the remainder of `a modulo b`
-/

-- 08 Try `apply?`
example (a b n : ℤ) (h : a % n = b % n) : n ∣ (b - a) :=
by
  sorry

-- 09
example (a b n : ℤ) :(a + b) % n = ((a % n) + (b % n))%n  :=
by
  sorry


-- 10 `apply?` won't work here but you do know a tactic that will do this in one line.
example (a b n : ℤ) :(a + b + 10*n^2) % n = ((a % n) + (b % n))%n  :=
by
  sorry

/-
If α and β are types then `α ≃ β` is an equivalence between `α` and `β`.

This is a function from `α` to `β` that has a two-sided inverse (i.e. a bijection)

If `e : α ≃ β` then `e.symm` is its inverse so `e.symm : β ≃ α`

Try to solve the following examples using only `trans` `symm` and `exact`
-/

-- 11
example (α β  : Type) (e : α ≃ β) (f : β ≃ ℕ) : α ≃ ℕ :=
by
  sorry

-- 12
example (α β γ δ: Type) (e : α ≃ β) (f : β ≃ γ) (g : δ ≃ γ): α ≃ δ :=
by
  sorry
