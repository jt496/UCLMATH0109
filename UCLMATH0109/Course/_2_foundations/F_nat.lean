import Mathlib.Tactic

namespace NotNat

/-
In this file we (re)define the natural numbers and prove many of the basic results.

We use `N` to denote the natural numbers rather than `ℕ` so that we can't 
accidentally use the results proved in Mathlib for ℕ.

The names of the results are identical to those in Mathlib for ℕ.

For a much more complete introduction see the Natural Numbers Game in Lean 4:

https://github.com/leanprover-community/lean4game 


The definition of the natural numbers `N` below says that there are two ways to construct `k : N`

Either k is `zero` or it is `succ n` (for some other natural number n). 

Built-in to this definition is the fact that `zero` is not equal to `succ n` for any n
and `succ m = succ n` implies that `m = n` (succ is injective).   -/

inductive N
| zero : N
| succ (n : N) : N


--------------------------------------------------------------------
open N  -- this ensures that `zero` is the zero we just defined etc

--- these instances allow us to use `0, 1, 2` to mean `zero, succ zero, succ (succ zero)` 
instance : OfNat N 0 where
  ofNat := zero
  
instance : OfNat N 1 where
  ofNat := succ 0

instance : OfNat N 2 where
  ofNat := succ 1
-----------------------------------------------------------------------
/-- Addition is defined inductively on the 2nd argument -/
def add : N → N → N
| a , 0   => a                    --  a + 0 := a
| a , succ b => succ (add a b)    --  a + (b + 1) := (a + b) + 1

-- This allows us to use the notation `a + b`
instance : Add N where
  add := add
 
--- Ask Richard about why I need this for the rewrites below
lemma zero_eq_zero : zero = 0 :=
by
  rfl

--- and this...
lemma one_eq_succ_zero :  1 = succ 0 :=
by
  rfl

-- We can use `dot` notation for the successor function.
/--  n + 1 = n.succ -/
lemma succ_eq_add_one (n : N) :  n.succ = n + 1  :=
by 
  rfl

lemma add_zero (n : N) : n + 0 = n :=
by
  rfl

/-- a + (b + 1) = (a + b) + 1 -/
lemma add_succ (a b : N) : a + b.succ = (a + b).succ:=
by
  rfl

/-
# New tactic for N: induction 

If we want to prove `∀ (n : N), P n` then we can use 
`induction n` which requires us to prove two things: 
`P 0` and `P n →  P n.succ`
-/

lemma zero_add (n : N) : 0 + n = n :=
by
  induction n with
  | zero => 
    rfl
  | succ n ih => 
    rw [add_succ, ih]
  

lemma succ_add (a b : N) : a.succ + b = (a + b).succ:=
by
  induction b with
  | zero => rfl
  | succ n ih => 
    rw [add_succ,add_succ, ih]


/- Digression: how do we know that 0 ≠ 1? 
This is one of the axioms of the natural numbers (Peano arithmetic)
and it is built into Lean's model of N.  -/

theorem succ_ne_zero (n : N) : n.succ ≠ 0 :=
by 
  intro h
  contradiction


-- Lean also knows that the successor function is injective (by definition)
theorem succ.inj (n m : N) : n.succ = m.succ → n = m :=
by
  intro h
  injection h


/- Our next result says that `+` is `associative`

In Lean `a + b + c` is defined as `(a + b) + c` so whenever you see an expression such as `a + b + c + d`
you need to remember how this is read by Lean: `((a + b) + c) + d`

We know that the brackets aren't required, but in Lean you need to prove this.
-/

lemma add_assoc (a b c : N) : (a + b) + c = a + (b + c):=
by
  induction c with
  | zero => rfl
  | succ n ih => 
    rw [add_succ, ih, add_succ, add_succ]


lemma add_comm (m n : N) : m + n = n + m :=
by
  induction n with
  | zero =>
    rw [zero_eq_zero, zero_add]
    rfl
  | succ n ih => 
    rw [add_succ, ih ,succ_add]
  

/-
Multiplication is also defined inductively in Lean, again on the 2nd argument.
-/

def mul : N → N → N
| _ , 0      =>   0                --  a * 0 := 0
| a , succ b => (mul a b) + a      --  a * (b + 1) = (a * b) + a  -/


-- This allows us to use the notation `a * b`
instance : Mul N where
  mul := mul

lemma mul_zero (n : N) : n * 0 = 0:=
by
  rfl

/-- m * (n + 1)= m * n + m -/
lemma mul_succ (m n : N) : m * n.succ = m * n + m:=
by
  rfl

/--  (n + 1) * m = n * m + m -/
lemma succ_mul (m n : N) : n.succ * m =  n * m + m:=
by
  induction m with
  | zero => rfl
  | succ m ih => 
    rw [mul_succ,mul_succ,ih,add_succ,add_succ]
    rw [add_assoc,add_comm m,add_assoc] 


lemma zero_mul (n : N) : 0 * n = 0:=
by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [mul_succ,ih]
    rfl


lemma mul_one (n : N) : n * 1 = n:=
by
  rw [one_eq_succ_zero,mul_succ,mul_zero,zero_add]


lemma one_mul (n : N) : 1 * n = n:=
by
  rw [one_eq_succ_zero,succ_mul,zero_mul,zero_add]


lemma mul_add (a b c: N) : a * (b + c) = a * b + a * c:=
by
  induction a with
  | zero =>
    rw [zero_eq_zero, zero_mul,zero_mul,zero_mul,zero_add]
  | succ n ih => 
    rw [succ_mul,succ_mul,succ_mul,ih, add_assoc,add_assoc,add_comm b,add_comm b,add_assoc]

 
lemma add_mul (a b c: N) : (b + c) * a = b * a + c * a:=
by
   induction a with
  | zero =>
    rw [zero_eq_zero, mul_zero,mul_zero,mul_zero,zero_add]
  | succ n ih => 
    rw [mul_succ,mul_succ,mul_succ,ih, add_assoc,add_assoc,add_comm b,add_comm b,add_assoc]


lemma mul_comm (a b : N) : a * b = b * a :=
by
  induction a with
  | zero => 
    rw [zero_eq_zero,zero_mul,mul_zero]
  | succ n ih => 
    rw [succ_mul,mul_succ,ih]


lemma mul_assoc (a b c : N) : a * b * c = a * (b * c):=
by
  induction c with
  | zero => 
    rw [zero_eq_zero,mul_zero,mul_zero,mul_zero]
  | succ n ih => 
    rw [mul_succ,mul_succ,ih,mul_add]
 

/-
Powers are also defined inductively in Lean.
-/

def pow : N → N → N
| _ , 0      =>   1              --  a ^ 0 = 1
| a , succ b => a * (pow a b)    --  a ^ (b + 1) = a*(a ^ b)   -/


-- This allows us to use the notation `a ^ b`
instance : Pow N N where
  pow := pow


lemma pow_zero (n : N) : n ^ 0 = 1 :=
by
  rfl

/-- a ^ (b + 1) = a * a ^ b -/
lemma pow_succ (a b : N) : a ^ b.succ = a * a ^ b:=
by
  rfl

lemma pow_one (n : N) : n ^ 1 = n:=
by 
  rw [one_eq_succ_zero,pow_succ,pow_zero,mul_one]


/-
# New use of tactic : cases 

We don't need induction to prove our next result, but we do need to consider the cases of zero and 
successor separately. The `cases n` tactic does exactly this.   -/

lemma zero_pow (n : N) (h : n ≠ 0) : 0 ^ n = 0:=
by
  cases n with
  | zero => contradiction
  | succ n =>
    rw [pow_succ,zero_mul]

lemma one_pow (n : N) : 1 ^ n = 1:=
by
  induction n with
  | zero => rfl
  | succ n ih => 
    rw [pow_succ,ih,mul_one]

lemma pow_add (a b c: N) : a ^ (b + c) = a ^ b * a ^ c :=
by
  induction c with
  | zero =>
    rw [zero_eq_zero,pow_zero,mul_one,add_zero]
  | succ n ih => 
    rw [add_succ,pow_succ,pow_succ,ih,mul_comm ,mul_comm a,← mul_assoc,mul_comm]
  

lemma pow_mul (a b c : N) : a ^ (b * c) = (a ^ b) ^ c :=
by
  induction c with
  | zero => 
    rw [zero_eq_zero,mul_zero,pow_zero,pow_zero]
  | succ n ih => 
    rw [pow_succ,mul_succ,pow_add,ih,mul_comm]
    

lemma two_eq_succ_one : 2 = succ 1 :=
by
  rfl

lemma two_mul (n : N) : 2 * n = n + n :=
by
  rw [two_eq_succ_one,succ_mul,one_mul]


lemma pow_two (n : N) : n ^ 2 = n * n:=
by
  rw [two_eq_succ_one,pow_succ,pow_one]


lemma add_sq (a b : N) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by
  rw [pow_two,mul_add,add_mul,two_mul,pow_two,pow_two,add_mul,
      mul_comm b,add_mul,add_assoc,add_assoc,add_assoc]
