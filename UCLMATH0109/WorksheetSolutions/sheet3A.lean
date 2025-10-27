import Mathlib.Tactic


namespace Sheet3Asol
/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

-- 01
lemma sLim_congr  (hxa: limₙ x a)  (hxy: ∀ n, y n = x n) (ha: b = a) : limₙ y b :=
by
  -- you can do this with `rw`, but `convert` is more direct
  convert hxa
  ext
  apply hxy


-- 02 You can do this with `apply?` but you need to choose the correct suggestion carefully
example (a b c d : ℝ) (ha : d ≤ a) : d ≤ min (max a b) (max a c) :=
by
  refine Iff.mpr le_min_iff ?_
  constructor
  · exact le_max_of_le_left ha
  · exact le_max_of_le_left ha


-- 03 Try to solve this using only `congr!`, `symm` and `exact`
example (a b c d : ℕ) (h1 : a = b) (h2 : c = d): (a + b + a)*(c + d) = (a + b + b)*(c + c):=
by
  congr!
  symm
  exact h2

-- 04 If `xₙ → a` then `xₙ₊ₘ → a` for all m
lemma tail_sLim_of_sLim (m : ℕ) (hx : limₙ x a) : limₙ (fun n => x (n + m)) a :=
by
  intro ε hε; dsimp
  specialize hx ε hε
  obtain ⟨N, hN⟩ := hx
  use N
  intro n hn
  apply hN
  exact le_add_right hn

/- If `a b : ℕ` then `a ∣ b` is `∃ c, b = a * c`
Note `∣` is not `|` it is `\|`
-/

-- 05 Use `trans` to solve this
example (a b c d : ℕ) (ha: a ∣ b) (hb : b ∣ c) : a ∣ d*c :=
by
  trans c
  · trans b
    · exact ha
    · exact hb
  · use d
    rw [mul_comm]


-- 06
example (a b c d: ℕ) (ha : c ∣ a) (hb : c ∣ b) (hd : b ∣ d):  c ∣ a + d :=
by
  obtain ⟨x,rfl⟩ := ha
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨z,rfl⟩ := hd
  use x + y * z
  rw [mul_add, mul_assoc]

/-
If `a b : ℤ` then `a % b` is the remainder of `a modulo b`
-/

-- 07 Try `apply?`
example (a b n : ℤ) (h : a % n = b % n) : n ∣ (b - a) :=
by
  exact Int.ModEq.dvd h

-- 08
example (a b n : ℤ) :(a + b) % n = ((a % n) + (b % n))%n  :=
by
  exact Int.add_emod a b n


/-
If α and β are types then `α ≃ β` is an equivalence between `α` and `β`.

This is a function from `α` to `β` that has a two-sided inverse (i.e. a bijection)

If `e : α ≃ β` then `e.symm` is its inverse so `e.symm : β ≃ α`

Try to solve the following examples using only `trans` `symm` and `exact`
-/

-- 09
example (α β  : Type) (e : α ≃ β) (f : β ≃ ℕ) : α ≃ ℕ :=
by
  trans β
  · exact e
  · exact f

-- 10
example (α β γ δ: Type) (e : α ≃ β) (f : β ≃ γ) (g : δ ≃ γ): α ≃ δ :=
by
  trans β
  · exact e
  · trans γ
    · exact f
    · symm
      exact g

end Sheet3Asol
