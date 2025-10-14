import Mathlib.Tactic
import Mathlib.Data.Real.Basic
/-

  # Assessed Sheet 3

Covering material from sheets 2G-H, 3A-D using the following tactics:

 `ext` `norm_num` `linarith` `ring` `apply?` `exact?` `decide`
  `refine` `convert` `congr!` `have` `calc`

In the exercises below you can always introduce new `have` statements
to give new goals that help.

-/

-- 01
example (a b : ℕ) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry

-- 02
example (A B : Set ℕ) (hA : ∀ a ∈ A, a ≤ 3) (hB : ∀ b ∈ B, b ≤ 2) : ∀ c ∈ A ∪ B, c ^ 2 ≤ 9 := by
  sorry

/-
 # Set builder notation
Set builder notation is built up from left to right in the obvious way,
so `x ∈ {a, b, c, d}` is definitionally `x = a ∨ x ∈ {b, c, d}`
-/

example (a b c d e : ℤ) : a ∈ ({d, c, b, a, e} : Set ℤ) := by
  right; right; right; left; rfl


/- # Set.range
If `f : α → β` then `Set.range f := {x : β | ∃ y : α, f y = x}`
So if `h : x ∈ Set.range f` then `h` is definitionally `∃ y : α, f y = x`
-/

-- 03
example (f : ℤ → ℤ) (h₀ : f 0 = -1) (h₁ : f 1 = 1) (h : ∀ x, f x = -1 ∨ f x = 1) : Set.range f = {-1, 1} := by
  sorry

/-
In the same way that `succ n` is Lean for `n + 1` so `pred n` is Lean for `n - 1`

Subtraction on ℕ is defined in terms of `pred`

def Nat.pred : ℕ → ℕ
  | 0      => 0         --          0 - 1 = 0
  | succ a => a         --    (a + 1) - 1 = a


def Nat.sub : ℕ → ℕ → ℕ
  | a, 0      => a              --            a - 0 = a
  | a, succ b => pred (a - b)   --      a - (b + 1) = (a - b) - 1

Warning: subtraction in ℕ is nasty, eg `4 - 6 = 0` etc..

In particular `ℕ` is not a ring so the `ring` tactic will struggle with
subtraction in ℕ (but is great at proving identities in ℤ, ℝ, ℚ etc).

One strategy that can work in `ℕ` is to first rewrite the identity you are trying to prove
so that subtraction does not appear. Once you've done this `ring` should finish it off.

-/

-- 04
example (a b : ℕ) : a = a + b - b := by
  sorry

-- 05
example : ∃ (a b : ℕ), a - b  + b ≠ a := by
  sorry

-- 06
example (m : ℕ) (h : 0 < m) : (2 * m) ^ 2 + (m ^ 2 - 1) ^ 2 = (m ^ 2 + 1) ^ 2:= by
  sorry

-- 07 this is very easy (notice we are in `ℤ` not `ℕ`)
example (m n : ℤ) : (n ^ 2 - m ^ 2) ^ 2 + (2 * m * n) ^ 2 = (n ^ 2 + m ^ 2) ^ 2 := by
  sorry

/-- A function `f : ℝ → ℝ` is continuous at `a : ℝ` iff ... -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a| < δ → |f x - f a| < ε


#check half_pos -- if `0 < a` then `0 < a / 2`
#check lt_min -- if `a < b` and `a < c` then `a < min b c`
/-
08 If `f` and `g` are continuous at `a` then so is `f + g`
-/
lemma cts_add (hf : Cts f a) (hg : Cts g a):  Cts (f + g) a := by
  sorry

#check lt_div_iff' -- if `0 < c` then  `a < b / c ↔ c * a < b`
#check div_pos -- if `0 < a` and `0 < b` then `0 < a / b`
/-
09 If `f` is continuous at `a` then so is `f * c` for any constant `c : ℝ`
Hint: consider the cases `c = 0` and `c ≠ 0` separately. Sketch the proof on paper first.
-/
lemma cts_const_mul (hf : Cts f a) (c : ℝ) : Cts (fun x ↦ c * f x) a := by
  sorry
