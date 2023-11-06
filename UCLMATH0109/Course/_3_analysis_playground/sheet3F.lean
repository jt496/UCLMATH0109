import Mathlib.Tactic



#check Nat.div_mul_div_comm
#check Nat.mul_div_mul

/-
If `d n : ℕ` and we have the hypothesis `h: d ∣ n` then norm_cast can prove
that `((n / d : ℕ) : ℝ)` equals `(n : ℝ)/(d : ℝ)`, but without this hypothesis
it simply isn't true.

In the next example you may want to prove an extra divisibility hypothesis before
using norm_cast.
-/
example (a b c : ℕ) (h : b ≠ 0) (h1 : b ∣ a) (h2 : c ∣ b):
(a / b : ℕ) * (b / c : ℕ) = (a : ℝ) / c :=
by
  sorry

/-
 `Nat.choose n k` is the number of `k`-element subsets of an `n`-element set,
 aka the binomial coefficient `n.choose k`

In Lean this is defined as:

def choose : ℕ → ℕ → ℕ
  | _    , 0     => 1 (there is one empty set)
  | 0    , _ + 1 => 0 (the empty set has no subsets that are non-empty)
  | n + 1, k + 1 => n.choose k + n.choose (k + 1) Pascal's Identity

This definition may look odd, but has the big advantage of not involving either
subtraction or division in ℕ, both of which are awkward.

Note that `n.choose k = n! / (k! * (n - k)!)`, but this is a theorem not a definition
(and doesn't hold for n = 0 and k = 1).


Our last example can be solved using the following two results, together
with `norm_cast` and `apply?`
-/

#check div_lt_one -- if 0 < b then a / b < 1 ↔ a < b
#check Nat.choose_succ_succ -- Pascal's identity

/- If k ≤ n then `(n choose k + 1)/(n + 1 choose k + 1) < 1 -/

example (n : ℕ) (h : k ≤ n): (n.choose (k + 1) : ℝ) / ((n + 1).choose (k + 1)) < 1:=
by
  sorry
