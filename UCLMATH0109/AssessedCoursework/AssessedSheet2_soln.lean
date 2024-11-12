
import Mathlib.Tactic
import UCLMATH0109.Course._2_foundations.F_nat



-- # Questions using `rfl` / `rw`

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
  obtain ⟨c,hc⟩ := ha 0
  rw [← hc, mul_zero]


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
--- This bit of code allows us to refer to "3" in the usual way
instance : OfNat N 3 where
  ofNat := succ 2

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
theorem two_eq_succ_one : (2 : N) = succ 1 :=
by
  rfl


-- 10
theorem three_eq_one_add_two : (3 : N) = 1 + 2 :=
by
  rfl

-- 11
theorem two_mul (n : N) : 2 * n = n + n :=
by
  rw [two_eq_succ_one,succ_mul,one_mul]


-- 12
theorem pow_three (n : N) : n ^ 3 = n * n^2:=
by
  rfl

-- 13
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [two_eq_succ_one, pow_succ, pow_one, pow_succ, pow_one,pow_succ,pow_one, succ_mul,
    add_mul,mul_add, mul_add, one_mul,add_mul, add_assoc, add_assoc, add_assoc, mul_comm b]

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
  rw [three_eq_one_add_two,←add_assoc,Fibonacci_step,add_assoc,←succ_eq_add_one 1,← two_eq_succ_one,
    Fibonacci_step,add_comm n.Fibonacci,add_comm n.Fibonacci,←add_assoc,two_eq_succ_one,succ_eq_add_one,
    add_mul,one_mul]

-- 15
/-
Prove that if `n` is a multiple of 3, then the `n`-th Fibonacci number is even.
-/
lemma Fibonacci_three_mul (n : N) : ∃ x, Fibonacci (3 * n) = 2 * x :=
by
  induction n with
  | zero =>
    use 0
    rfl
  | succ n ih =>
    obtain ⟨y, ih⟩ := ih
    use y + Fibonacci (3 * n + 1)
    rw [succ_eq_add_one,mul_add, mul_one, Fibonacci_add_three, mul_add, ih]

-- 16 The `induction n generalizing m` tactic is very useful here. Make sure you understand what it does.
lemma Fibonacci_add (m n : N) : Fibonacci (m + n + 1) = Fibonacci m * Fibonacci n + Fibonacci (m + 1) * Fibonacci (n + 1) :=by
  induction n generalizing m with
  | zero =>
    rw [zero_eq,add_zero,Fibonacci_zero,mul_zero,zero_add,zero_add,Fibonacci_one,mul_one]
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n, add_assoc] at ih
    rw [succ_eq_add_one, add_assoc,ih, add_assoc m ,add_assoc n,← succ_eq_add_one 1, ←two_eq_succ_one,
        Fibonacci_step,Fibonacci_step, add_mul,mul_add,←add_assoc,add_assoc,←add_assoc,
        add_comm ((m+1).Fibonacci*_),←add_assoc]


-- 17 A harder question on propositional logic (only use tactics from 2A-2D)
example (P : ℕ → Prop) (h : ∀ n, P n ↔ ¬ (P (n+1) ↔ P (n + 2))) :  ∀ n, P n → P (n + 3) :=
by
  intro n h0
  by_contra h3
  by_cases h1 : P (n + 1)
  · by_cases h2 : P (n + 2)
    · apply (h n).1 h0
      constructor <;>
      · intro; assumption
    · apply (h (n+1)).1 h1
      constructor <;>
      · intro; contradiction
  · by_cases h2 : P (n + 2)
    · apply h1
      apply (h (n+1)).2
      by_contra hh
      apply h3 (hh.1 h2)
    · apply (h n).1 h0
      constructor <;>
      · intro; contradiction
