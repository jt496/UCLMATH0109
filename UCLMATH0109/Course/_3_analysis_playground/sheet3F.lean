import Mathlib.Tactic


/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/-
These examples should be solved mainly using `norm_cast`, `push_cast` and (occaisionally) `cancel_denoms`.

Other useful tactics include: `ring`, `linarith`, `norm_num` and `apply?`.

You will also need to find rewrite lemmas (and introduce `have` statements where needed).
-/


-- 01
example (a : ℕ)  (b : ℚ) (h : (a : ℝ) = b): (a : ℂ) = b  :=
by
/-
a : ℕ
b : ℚ
h : ↑a = ↑b
⊢ ↑a = ↑b
Note that `exact h` fails here even though Infoview seems to suggest otherwise (hover over Infoview to see why)  -/
  sorry


-- 02
example (a b c : ℕ) (h : a*b = 3*c) : (2*c : ℝ) = (2*a*b)/3:=
by
  sorry


-- 03
example (a b c : ℕ) (h : a + b + c = 3*c) : (2*c : ℝ) = a + b:=
by
  sorry


/- Remember you can do `norm_cast at h` if `h` is in the local context -/
-- 04
example (a b c d : ℕ) (h1 : a + b = (c + (d : ℤ) : ℝ)) (h2: a ≤ (c : ℝ)) (h3 : b ≤ (d : ℤ)) : a = c :=
by
  sorry


-- 05
example (a b  : ℕ) (c : ℤ) (h1: a ∣ 2*b)  (h2 : (4*b : ℤ) ∣ -c) : (a : ℤ) ∣ c :=
by
  sorry
/-
If `d n : ℕ` and we have the hypothesis `h: d ∣ n` then norm_cast can prove
that `((n / d : ℕ) : ℝ)` equals `(n : ℝ)/(d : ℝ)`, but without this hypothesis
it simply isn't true.

In the next example you may want to prove an extra divisibility hypothesis before
using norm_cast. The following two results may also be useful. -/
#check Nat.div_mul_div_comm
#check Nat.mul_div_mul

-- 06
example (a b c : ℕ) (h : b ≠ 0) (h1 : b ∣ a) (h2 : c ∣ b):
(a / b : ℕ) * (b / c : ℕ) = (a : ℝ) / c :=
by
  sorry


-- 07 if xₙ → a then 2 * xₙ → 2 * a
example (hl : limₙ x a) : limₙ (2*x) (2*a) :=
by
  intro ε hε
  dsimp -- this definitionally simplifies the goal so `(2 * x) n` becomes `↑2 * x n`
  sorry
/-
 `Nat.choose n k` is the number of `k`-element subsets of an `n`-element set,
 aka the binomial coefficient `n.choose k`

In Lean this is defined as:

def choose : ℕ → ℕ → ℕ
  | _    , 0     => 1 (there is one empty subset of any set)
  | 0    , _ + 1 => 0 (the empty set has no subsets that are non-empty)
  | n + 1, k + 1 => n.choose k + n.choose (k + 1)  (Pascal's Rule: https://en.wikipedia.org/wiki/Pascal%27s_rule)

This definition may look odd, but has the big advantage of not involving either
subtraction or division in ℕ, both of which are awkward.

Note that `n.choose k = n! / (k! * (n - k)!)`, but this is a theorem not a definition
(and doesn't hold for n = 0 and k = 1).

Our last example can be solved using the following two results, together
with `norm_cast` and `apply?`
-/

#check div_lt_one -- if 0 < b then a / b < 1 ↔ a < b
#check Nat.choose_succ_succ -- Pascal's identity
#check Nat.choose_pos -- if k ≤ n then `0 <  n.choose k`

/- If k ≤ n then `(n choose k + 1)/(n + 1 choose k + 1) < 1 -/
-- 08
example (n : ℕ) (h : k ≤ n): (n.choose (k + 1) : ℝ) / ((n + 1).choose (k + 1)) < 1:=
by
  sorry
