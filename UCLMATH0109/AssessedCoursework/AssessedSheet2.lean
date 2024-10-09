
import Mathlib.Tactic
import UCLMATH0109.Course._2_foundations.F_nat

-- You need to have covered all the videos/sheets 2A - 2F to do this problem sheet.

-- # Questions using `rfl` / `rw`

-- 01
example (a b : ℝ) (ha : a = 0) (hb : b = a ) : b = 0 :=
by
  sorry

-- 02
example : 2 + 3  - 7 = 2 * 4 - 8 :=
by
  sorry

-- 03
example (a : ℕ) (ha : ∀ b, ∃ c, c * b = a) : a = 0:=
by
  sorry

-- 04 This is easy but make sure you understand why your proof works
example (a : ℕ) (h : a * a = a): a*a*a*a*a = a*a*a :=
by
  sorry

-- 05
example (a b c : ℕ) (hab : a*b = c) (hbc: b * c = a) (hca : c * a = b) : c*b*a = a*b*(c*a)*(b*c):=
by
  sorry


/-
# Questions using our version of the natural numbers `N`

inductive N
| zero : N
| succ (n : N) : N

You can do the next few questions using `induction` as well as `rw` using the results proved in `F_nat.lean`

Look in that file for definitions of functions on N as well as useful theorems to apply.
In particular remember how we defined the `pow` function `a ^ b`

def pow : N → N → N
| _ , 0      =>   1              --  a ^ 0 = 1
| a , succ b => a * (pow a b)    --  a ^ (b + 1) = a * (a ^ b)

-/

namespace N
--- This bit of code allows us to refer to "3" in the usual way
instance : OfNat N 3 where
  ofNat := succ 2

-- 06
theorem one_pow (n : N) : 1 ^ n = 1:=
by
  sorry

-- 07
theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  sorry

-- 08
theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  sorry

-- 09
theorem two_eq_succ_one : (2 : N) = succ 1 :=
by
  sorry

-- 10
theorem three_eq_one_add_two : (3 : N) = 1 + 2 :=
by
  sorry

-- 11
theorem two_mul (n : N) : 2 * n = n + n :=
by
  sorry

-- 12
theorem pow_three (n : N) : n ^ 3 = n * n^2:=
by
  sorry

-- 13
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  sorry

/-
We can define the Fibonacci numbers in the standard way (note that Mathlib uses a much faster equivalent definition)
-/

def Fibonacci : N → N
  | 0     => 0
  | 1     => 1
  | n + 2 => Fibonacci n + Fibonacci (n + 1)

/-
We prove a few simple results using the `rfl` tactic.
-/
lemma Fibonacci_zero : Fibonacci 0 = 0 :=
by
  rfl

lemma Fibonacci_one : Fibonacci 1 = 1 :=
by
  rfl

lemma Fibonacci_step (n : N) : Fibonacci (n + 2) = Fibonacci n + Fibonacci (n + 1) :=
by
  rfl

-- 14
lemma Fibonacci_add_three :
    Fibonacci (n + 3) = Fibonacci n + 2 * Fibonacci (n + 1) :=
by
  sorry

-- 15 Prove that if `n` is a multiple of 3, then the `n`-th Fibonacci number is even.
lemma Fibonacci_three_mul (n : N) : ∃ x, Fibonacci (3 * n) = 2 * x :=
by
  sorry

-- 16 The `induction n generalizing m` tactic is very useful here. Make sure you understand what it does.
lemma Fibonacci_add (m n : N) : Fibonacci (m + n + 1) = Fibonacci m * Fibonacci n + Fibonacci (m + 1) * Fibonacci (n + 1) :=by
  induction n generalizing m with
  | zero =>
    sorry
  | succ n ih =>
    sorry

-- 17 A harder question on propositional logic (only use tactics from 2A - 2D)
example (P : ℕ → Prop) (h : ∀ n, P n ↔ ¬ (P (n+1) ↔ P (n + 2))) :  ∀ n, P n → P (n + 3) :=
by
  sorry
