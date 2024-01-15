
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Use
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import UCLMATH0109.Course._2_foundations.F_nat



-- # Questions using `rfl` / `rw` and `nth_rewrite`

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

-- 06
theorem one_pow (n : N) : 1 ^ n = 1:=
by
  induction n with
  | zero => sorry
  | succ n ih => sorry


-- 07
theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  sorry

-- 08
theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  sorry

-- 09
theorem two_eq_succ_one : 2 = succ 1 :=
by
  sorry

-- 10
theorem two_mul (n : N) : 2 * n = n + n :=
by
  sorry


-- 11
theorem pow_three (n : N) : n ^ (1 + 1 + 1) = n * n^2:=
by
  sorry

-- 12
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  sorry


-- # Questions using Mathlib (and `exact?`)
/-
In this exercise you can use the theorem `Nat.succ_ne_self` from Mathlib.
-/
#check Nat.succ_ne_self

--13
example : ∀ n : ℕ, ∃ m : ℕ, m ≠ n :=
by
  sorry


-- 14
example : ∃ n : ℕ, ∀ m : ℕ, n+m = n → m = n :=
by
  sorry


/-
In this next example, you can use the theorem `mul_eq_mul_left_iff` from `Mathlib`.
-/
#check mul_eq_mul_left_iff

-- 15
example : 2 * n = 2 * 2 ↔ n = 2 :=
by
  sorry
