
import Mathlib.Tactic
import UCLMATH0109.Course._2_foundations.F_nat


-- # Questions using `rfl` / `rw` (covering sections 2E and 2F of the course material)

-- 01
example (a b : ℝ) (ha : a = 0) (hb : b = a ) : b = 0 :=by
  rwa [hb]

-- 02
example : 2 + 3 - 7 = 2 * 4 - 8 :=by
  rfl

-- 03
example (a : ℕ) (ha : ∀ b, ∃ c, c * b = a) : a = 0 :=by
  obtain ⟨c, hc⟩ := ha 0
  rw [← hc]
  rfl

-- 04
example (a : ℕ) (h : a * a = a) : a * a * a * a * a = a * a * a :=by
  rwa [h, h, h]

-- 05
example (a b c : ℕ) (hab : a * b = c) (hbc : b * c = a) (hca : c * a = b) :
    c * b * a = a * b * (c * a) * (b * c) :=by
  rw [hab, hca, hbc]

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
theorem one_pow (n : N) : 1 ^ n = 1 :=by
  induction n with
  | zero => rfl
  | succ n ih =>
    rwa [pow_succ,one_mul]


-- 07
theorem pow_add (a b c : N) : a ^ (b + c) = a ^ b * a ^ c :=by
  induction c with
  | zero =>
    rw [zero_eq, add_zero, pow_zero, mul_one]
  | succ n ih =>
    rw [add_succ, pow_succ, ih, ←mul_assoc, mul_comm a, pow_succ, mul_assoc]

-- 08
theorem pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=by
  induction c with
  | zero => rw [zero_eq, mul_zero, pow_zero, pow_zero]
  | succ n ih => rw [mul_succ, pow_add, ih, pow_succ, mul_comm]

-- 09
theorem two_eq_succ_one : (2 : N) = succ 1 :=by
  rfl

-- 10
theorem three_eq_one_add_two : (3 : N) = 1 + 2 :=by
  rfl

-- 11
theorem two_mul (n : N) : 2 * n = n + n :=by
  rw [two_eq_succ_one, succ_mul, one_mul]

-- 12
theorem pow_three (n : N) : n ^ 3 = n * n ^ 2:=by
  rfl

-- 13
theorem add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=by
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
lemma Fibonacci_zero : Fibonacci 0 = 0 :=by
  rfl

lemma Fibonacci_one : Fibonacci 1 = 1 :=by
  rfl

lemma Fibonacci_step (n : N) : Fibonacci (n + 2) = Fibonacci n + Fibonacci (n + 1) :=by
  rfl

-- 14
lemma Fibonacci_add_three :
    Fibonacci (n + 3) = Fibonacci n + 2 * Fibonacci (n + 1) :=by
  rw [three_eq_one_add_two, ← add_assoc, Fibonacci_step, add_assoc, ← succ_eq_add_one 1,
    ← two_eq_succ_one, Fibonacci_step, add_comm n.Fibonacci, add_comm n.Fibonacci, ← add_assoc,
    two_eq_succ_one, succ_eq_add_one, add_mul, one_mul]


-- 15
/-
Prove that if `n` is a multiple of 3, then the `n`-th Fibonacci number is even.
-/
lemma Fibonacci_three_mul (n : N) : ∃ k, Fibonacci (3 * n) = 2 * k :=by
  induction n with
  | zero =>
    use 0
    rfl
  | succ n ih =>
    obtain ⟨y, ih⟩ := ih
    use y + Fibonacci (3 * n + 1)
    rw [succ_eq_add_one,mul_add, mul_one, Fibonacci_add_three, mul_add, ih]


-- 16 The `induction n generalizing m` tactic is very useful here. Make sure you understand what it does.
lemma Fibonacci_add (m n : N) :
    Fibonacci (m + n + 1) = Fibonacci m * Fibonacci n + Fibonacci (m + 1) * Fibonacci (n + 1) :=by
  induction n generalizing m with
  | zero => rw [zero_eq, add_zero, Fibonacci_zero, mul_zero, zero_add, zero_add, Fibonacci_one, mul_one]
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n, add_assoc] at ih
    rw [succ_eq_add_one, add_assoc,ih , add_assoc m ,add_assoc n, ← succ_eq_add_one 1, ← two_eq_succ_one,
        Fibonacci_step, Fibonacci_step, add_mul, mul_add, ← add_assoc, add_assoc, ← add_assoc,
        add_comm (_ * n.Fibonacci), ← add_assoc]


-- 17 A harder question on propositional logic
example (P : N → Prop) (h : ∀ n, P n ↔ ¬ (P (n + 1) ↔ P (n + 2))) :  ∀ n, P n → P (n + 3) :=by
  intro n h0
  by_contra h3
  by_cases h1 : P (n + 1)
  · by_cases h2 : P (n + 2)
    · apply (h n).1 h0
      constructor <;> -- `<;>` tells Lean to run the next line on all goals, useful for repetitive proofs
      · intro; assumption
    · apply (h (n + 1)).1 h1
      constructor <;>
      · intro; contradiction
  · by_cases h2 : P (n + 2)
    · apply h1
      apply (h (n + 1)).2
      by_contra hh
      apply h3 (hh.1 h2)
    · apply (h n).1 h0
      constructor <;>
      · intro; contradiction

/-   # Proof by structural recursion
The plain `induction` tactic only allows us to apply the induction hypothesis for `n`
while proving the case `succ n`. Sometimes we need something stronger and Lean has its
own internal version of induction called `structural recursion` built-in. This is like
strong induction in that it allows us to use the inductive hypothesis for any smaller case.

We give an example below where we use the inductive hypothesis for `n` to prove the
case of `n + 2`.

-/

theorem add_two_eq (n : N) : ∃ i j : N, n + 2 = 2 * i + 3 * j := by
  cases n with
  | zero =>
    use 1, 0;
    rw [zero_eq, zero_add, mul_one, mul_zero, add_zero]
  | succ n =>
    cases n with
    | zero =>
      use 0, 1
      rw [zero_eq, succ_eq_add_one,  zero_add, mul_one, mul_zero, zero_add,
          three_eq_one_add_two]
    | succ n =>
      -- We now use the fact that `n` is smaller than `n + 2` and
      -- since we are in the case `n + 2` we can apply the theorem we
      -- are proving in the case `n`.
      obtain ⟨c, d, hc⟩ := add_two_eq n
      use (c + 1), d
      rw [two_mul, succ_add, succ_add, hc, ← succ_eq_add_one,
       add_succ, succ_add c, ←two_mul, succ_add,succ_add]


-- 18 define a series `mySeries` by taking the first two terms to be `1` and `3`,
-- and then each further term to be the product of the previous two terms.
def mySeries : N → N
| 0 => 1
| 1 => 3
| n + 2 => mySeries n * mySeries (n + 1)

-- 19 State and prove a lemma in Lean which relates `mySeries` to `Fibonacci`.
-- (You may want to use the the `structural recursion` we saw in the proof of `add_two_eq` above.)
theorem mySeries_eq_three_pow_Fibonacci (n : N) : mySeries n = 3 ^ Fibonacci n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [succ_eq_add_one, succ_eq_add_one, add_assoc, ← succ_eq_add_one, ← two_eq_succ_one, Fibonacci_step,
         pow_add, ← mySeries_eq_three_pow_Fibonacci n, ← mySeries_eq_three_pow_Fibonacci (n + 1)]
      rfl
