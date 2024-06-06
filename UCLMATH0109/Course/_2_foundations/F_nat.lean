import Mathlib.Tactic

/-

## The Natural numbers and named theorems (new tactics: induction / injection / cases)

In this file we (re)define the natural numbers and prove some basic results.

We also introduce `named` theorems.

Most of our previous proofs were of `examples`.

An example is simply an anonymous theorem (i.e. a theorem with no name).

If we want to use a theorem then it needs to have a name that we can refer to.

As we prove theorems in this file they become available for us to use.

We will use `N` to denote the natural numbers rather than `ℕ` so that we can't
accidentally use results from Mathlib.

The names of the theorems we prove are identical to those in Mathlib for ℕ.

You may notice that they are named in a very consistent way.


For a much more complete introduction see the Natural Numbers Game in Lean 4:

  https://adam.math.hhu.de/#/game/nng

-/



/-

# The Natural Numbers N

The definition of the natural numbers `N` below says that there are two ways to construct
a natural number `k : N`

Either k is `zero` or it is `succ n` (for some other natural number n).

We should think of this as saying there is a first natural number `zero` and given any
natural number `n` we can construct its successor `succ n` (we would usually call this `n + 1`)

Built-in to this definition is the fact that `zero` is not equal to `succ n` for any n
and `succ m = succ n` implies that `m = n` (i.e. `succ` is injective).

This is part of Lean's internal definition of an `inductive` type.
-/

inductive N
| zero : N
| succ (n : N) : N


namespace N  -- this allows us to use `zero` and `succ` that we just defined


/- Feel free to ignore the next few lines.  We will discuss instances later in term -/
-----------------------------------------------------------------------------------------
--- These instances allow us to use `0, 1, 2` to mean `zero, succ zero, succ (succ zero)`
instance : OfNat N 0 where
  ofNat := zero

instance : OfNat N 1 where
  ofNat := succ 0

instance : OfNat N 2 where
  ofNat := succ 1
-----------------------------------------------------------------------------------------


/-- Addition is defined inductively on the 2nd argument -/
def add : N → N → N
| a , 0   => a                    --  a + 0 = a
| a , succ b => succ (add a b)    --  a + (b + 1) = (a + b) + 1


-- This allows us to use the notation `a + b`
instance : Add N where
  add := add


theorem zero_eq : zero = 0 :=
by
  rfl

--- and this...
theorem one_eq_succ_zero :  1 = succ 0 :=
by
  rfl


-- We can use `dot` notation for the successor function.
/--  n + 1 = n.succ -/
theorem succ_eq_add_one (n : N) :  n.succ = n + 1  :=
by
  rfl


theorem add_zero (n : N) : n + 0 = n :=
by
  rfl

/-- a + (b + 1) = (a + b) + 1 -/
theorem add_succ (a b : N) : a + b.succ = (a + b).succ:=
by
  rfl

/-
# New tactic for N: induction

If we want to prove `∀ (n : N), P n` then we can use `induction n`
which requires us to prove two things:
`P 0` and `P n →  P n.succ`

-/

theorem zero_add (n : N) : 0 + n = n :=
by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [add_succ,ih]




theorem succ_add (a b : N) : a.succ + b = (a + b).succ:=
by
  induction b with
  | zero =>
    rfl
  | succ n ih =>
    rw [add_succ, ih, add_succ]


/- Digression: how do we know that 0 ≠ 1?
This is one of the axioms of the natural numbers (Peano arithmetic)
and it is built into Lean's model of N.  -/

theorem succ_ne_zero (n : N) : n.succ ≠ 0 :=
by
  intro hf
  contradiction


-- Lean also knows that the successor function is injective (by definition)
theorem succ_inj (n m : N) : n.succ = m.succ → n = m :=
by
  intro h
  injection h


/- Our next result says that `+` is `associative`

In Lean `a + b + c` is defined as `(a + b) + c` so whenever you see an expression such as
`a + b + c + d` you need to remember how this is read by Lean : `((a + b) + c) + d`

We know that the brackets aren't required, but in Lean you need to prove this.
-/

theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c):=
by
  sorry

theorem add_comm (m n : N) : m + n = n + m :=
by
  sorry

/-
Multiplication is also defined inductively in Lean, again on the 2nd argument.
-/

def mul : N → N → N
| _ , 0      =>   0                --  a * 0 = 0
| a , succ b => (mul a b) + a      --  a * (b + 1) = (a * b) + a  -/


-- This allows us to use the notation `a * b`
instance : Mul N where
  mul := mul

theorem mul_zero (n : N) : n * 0 = 0:=
by
  sorry

/-- m * (n + 1)= m * n + m -/
theorem mul_succ (m n : N) : m * n.succ = m * n + m:=
by
  sorry

/--  (n + 1) * m = n * m + m -/
theorem succ_mul (m n : N) : n.succ * m =  n * m + m:=
by
  sorry

theorem zero_mul (n : N) : 0 * n = 0:=
by
  sorry


theorem mul_one (n : N) : n * 1 = n:=
by
  sorry

theorem one_mul (n : N) : 1 * n = n:=
by
  sorry

theorem mul_add (a b c: N) : a * (b + c) = a * b + a * c:=
by
  sorry

theorem add_mul (a b c: N) : (b + c) * a = b * a + c * a:=
by
  sorry

theorem mul_comm (a b : N) : a * b = b * a :=
by
  sorry

theorem mul_assoc (a b c : N) : a * b * c = a * (b * c):=
by
  sorry

/-
Powers are also defined inductively in Lean.
-/

def pow : N → N → N
| _ , 0      =>   1              --  a ^ 0 = 1
| a , succ b => a * (pow a b)    --  a ^ (b + 1) = a * (a ^ b)   -/


-- This allows us to use the notation `a ^ b`
instance : Pow N N where
  pow := pow


theorem pow_zero (n : N) : n ^ 0 = 1 :=
by
  sorry

/-- a ^ (b + 1) = a * a ^ b -/
theorem pow_succ (a b : N) : a ^ b.succ = a * a ^ b:=
by
  sorry

theorem pow_one (n : N) : n ^ 1 = n:=
by
  sorry

/-
# New use of tactic : cases

We don't need induction to prove our next result, but we do need to consider the cases of zero and
successor separately. The `cases n` tactic does exactly this.   -/

theorem zero_pow (n : N) (h : n ≠ 0) : 0 ^ n = 0:=
by
  cases n with
  | zero =>
    contradiction
  | succ n =>
    rw [pow_succ,zero_mul]



/-
 Now do sheet2F.
-/
