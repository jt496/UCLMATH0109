/-
# Convergence of continued fractions.

Let `a: ℕ → ℕ+` be a sequence of positive integers.
Show that the continued fraction converges:

`a 0 + 1 / (a 1 + 1 / (a 2 + ...))`.

To do this, let `numer a n` and `denom a n` be the numerator and denominator of the `n`-th partial
quotient `partQuot n`.
Prove that `partQuot (n+1) = partQuot n + (-1)^n / (denom n * denom (n+1))`.
Prove that the sequence `denom` is a strictly increasing sequence of positve integers.
-/

import Mathlib.Tactic

/--
The (finite) continued fraction of a list of real numbers.
-/
noncomputable
def CFrac : List ℝ → ℝ
| []      => 0
| x :: xs => x + 1 / (CFrac xs)

-- # I recommend you state and prove som definitional lemmas for `CFrac`.

lemma CFrac_append_CFrac :
  CFrac (as ++ [CFrac bs]) = CFrac (as ++ bs) := sorry

lemma CFrac_append_pair :
  CFrac (as ++ [x,y]) = CFrac (as ++ [x + 1/y]) := sorry

variable (a : ℕ → ℕ+)

/-
`to_list a n` is the list of the first `n` terms in the sequence `a`.
-/
def to_list : ℕ → List ℝ
| 0   => []
| n+1 => to_list n ++ [(a n : ℝ)]

-- I recommend you state and prove some definitional lemmas for `to_list`.

/-
define the numerator and denominator of the `n`-th convergent:
-/
def numer : ℕ → ℕ+
| 0   => a 0
| 1   => (a 0) * (a 1) + 1
| n+2 => a (n+2) * numer (n+1) + numer n

def denom : ℕ → ℕ+
| 0   => 1
| 1   => (a 1)
| n+2 => a (n+2) * denom (n+1) + denom n

-- # I recommend you state and prove some more definitional lemmas here.

lemma CFrac_to_list_append (hα : α > 0) :
    CFrac (to_list a (n+2) ++ [α]) = (numer a (n+1) * α + numer a n) / (denom a (n+1) * α + denom a n) :=
by
  sorry

lemma CFrac_to_list :
    CFrac (to_list a (n+1)) = (numer a n) / (denom a n) :=
by
  sorry



lemma numer_mul_denom_sub : (numer a (n+1) * denom a n - numer a n * denom a (n + 1) : ℤ) = (-1) ^ n :=
by
  sorry


/-
define the `n`-th convergent as follows.
-/
def partQuot (n : ℕ) : ℝ := (numer a n / denom a n : ℚ)

lemma partQuot_sub_partQuot :
  partQuot a (n+1) - partQuot a n = (-1) ^ n / (denom a n * denom a (n+1)) :=
by
  sorry

open BigOperators Finset

lemma partQuot_eq :
  partQuot a n = partQuot a 0 + ∑ i in range n, (-1 : ℝ) ^ i / (denom a i * denom a (i+1)) :=
by
  sorry


/-
Now prove that the sequence of partial quotients converges using the alternating series test.
Prove some of the other results in the pdf file.
-/
