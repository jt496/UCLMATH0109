
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
  rwa [hb]

-- 02
example : 2 + 3  - 7 = 2 * 4 - 8 :=
by
  rfl

-- 03
example (a : ℕ) (ha : ∀ b, ∃ c, c * b = a) : a = 0:=
by
  specialize ha 0
  obtain ⟨c,hc⟩ := ha
  rw [← hc]
  rfl


-- 04 This is easy but make sure you understand why your proof works
example (a : ℕ) (h : a * a = a): a*a*a*a*a = a*a*a :=
by
  rwa [h,h,h]


-- 05
example (a b c : ℕ) (hab : a*b = c) (hbc: b * c = a) (hca : c * a = b) : c*b*a = a*b*(c*a)*(b*c):=
by
  rw [hab,hca,hbc]


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
  | zero => rfl --sorry
  | succ n ih =>
    rwa [pow_succ,one_mul]


-- 07
theorem pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  induction c with
  | zero =>
    rw [zero_eq,add_zero,pow_zero,mul_one]
  | succ n ih =>
    rw [add_succ,pow_succ,ih,←mul_assoc,mul_comm a,pow_succ,mul_assoc]

-- 08
theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  induction c with
  | zero => rw [zero_eq,mul_zero,pow_zero,pow_zero]
  | succ n ih =>
    rw [mul_succ,pow_add,ih,pow_succ,mul_comm]

-- 09
theorem two_eq_succ_one : 2 = succ 1 :=
by
  rfl

-- 10
theorem two_mul (n : N) : 2 * n = n + n :=
by
  rw [two_eq_succ_one,succ_mul,one_mul]


-- 11
theorem pow_three (n : N) : n ^ (1 + 1 + 1) = n * n^2:=
by
  rfl

-- 12
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [two_eq_succ_one, pow_succ, pow_one, pow_succ, pow_one,pow_succ,pow_one, succ_mul,
      add_mul,mul_add, mul_add, one_mul,add_mul, add_assoc, add_assoc, add_assoc, mul_comm b]


-- # Questions using Mathlib (and `exact?`)
/-
In this exercise you can use the theorem `Nat.succ_ne_self` from Mathlib.
-/
#check Nat.succ_ne_self

--13
example : ∀ n : ℕ, ∃ m : ℕ, m ≠ n :=
by
  intro n
  use n+1
  exact Nat.succ_ne_self n

/-
In this exercise you can use the theore `Nat.eq_zero_of_add_eq_zero_left` from Mathlib.
-/
#check Nat.eq_zero_of_add_eq_zero_left

-- 14
example : ∃ n : ℕ, ∀ m : ℕ, n+m = n → m = n :=
by
  use 0
  intro m hm
  exact Nat.eq_zero_of_add_eq_zero_left hm


/-
In this next example, you can use the theorem `mul_eq_mul_left_iff` from `Mathlib`.
-/
#check mul_eq_mul_left_iff

-- 15
example : 2 * n = 2 * 2 ↔ n = 2 :=
by
  constructor
  · intro h
    rw [mul_eq_mul_left_iff] at h
    cases h with
    | inl h => assumption
    | inr h => contradiction
  · intro h
    rw [h]
