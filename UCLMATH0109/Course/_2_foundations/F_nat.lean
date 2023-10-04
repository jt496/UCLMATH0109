import Mathlib.Tactic

#check Nat
namespace UCL

/-
In Lean the natural numbers `ℕ` are defined as follows:

This means that there are two ways to construct a natural number `n:N`
Either `n` is `zero` or it is the successor of a previously constructed 
natural number `succ n`. -/

inductive N
| zero : N
| succ (n : N) : N


open N

instance : Zero N where
  zero := zero  


def add : N → N → N
| a , 0   => a                    --  a + 0 := a
| a , succ b => succ (add a b)       --  a + (b + 1) := (a + b) + 1

---------- The next few lines 
instance : Add N where
  add := add


instance : One N where
  one := succ 0 


-- We will use the `dot` notation for the successor function.
/--  n + 1 = n.succ -/
lemma succ_eq_add_one (n : N) :  n.succ = n + 1  :=
by 
  rfl

lemma zero_eq_zero : zero = 0 :=
by
  rfl

lemma succ_zero_eq_one : succ 0 = 1 :=
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
  

lemma succ_add (a b : UCL.N) : a.succ + b = (a + b).succ:=
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
Multiplication is also defined inductively in Lean.
-/
def mul : N → N → N
| _ , 0      =>   0                      --  a * 0 := 0
| a , succ b => (mul a b) + a        --  a * (b + 1) = (a * b) + a  -/

instance : Mul N where
  mul := mul

lemma mul_zero (n : N) : n * 0 = 0:=
by
  rfl



lemma mul_succ (m n : N) : m * n.succ = m * n + m:=
by
  rfl


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
  rw [← succ_zero_eq_one,mul_succ,mul_zero,zero_add]


lemma one_mul (n : N) : 1 * n = n:=
by
  rw [← succ_zero_eq_one,succ_mul,zero_mul,zero_add]


lemma mul_add (a b c: N) : a*(b + c) = a*b + a*c:=
by
  induction a with
  | zero =>
    rw [zero_eq_zero, zero_mul,zero_mul,zero_mul,zero_add]
  | succ n ih => 
    rw [succ_mul,succ_mul,succ_mul,ih, add_assoc,add_assoc,add_comm b,add_comm b,add_assoc]

 
lemma add_mul (a b c: N) : (b + c)*a = b*a +c*a:=
by
  sorry


lemma Mul_comm (a b : N) : a * b = b * a :=
by
  sorry


lemma Mul_assoc (a b c : N) : a * b * c = a * (b * c):=
by
  sorry


lemma Pow_zero (n : N) : n ^ 0 = 1:=
by
  sorry


lemma Pow_succ (a b : N) : a^b.succ= a* a^b:=
by
  sorry


lemma Pow_one (n : N) : n ^ 1 = n:=
by 
  sorry


/-
# New use of tactic : cases 

We don't need induction to prove our next result, but we do need to consider the cases of zero and 
successor separately. The `cases n` tactic does exactly this.   -/

lemma Zero_pow (n : N) (h : n ≠ 0): 0 ^ n = 0:=
by
  cases n with n hn,
  {
    sorry
  },
  {
    sorry
  },



lemma One_pow (n : N) : 1 ^ n = 1:=
by
  sorry



lemma Pow_add (a b c: N): a^(b + c)=a^b*a^c:=
by
  induction c with c hc,
  {
    sorry
  },
  {
    sorry
  },


lemma Pow_mul (a b c : N) : a^(b * c) = (a^b)^c :=
by
  sorry



lemma Two_eq_one_add_one : 2 = 1 + 1:=
by
  sorry


lemma Two_mul (n : N) : 2*n = n + n:=
by
  sorry


lemma Three_mul (n : N) : 3*n = n + n + n:=
by
  have : 3 = 2 + 1, {
    sorry
  },
  sorry


lemma Pow_two (n : N) : n^2 = n*n:=
by
  sorry


lemma Add_sq (a b : N) : (a + b)^2 = a^2 + 2*a*b + b^2 :=
by
  sorry


lemma Pow_three (n : N) : n^3 = n*n*n:=
by
  have : 3 = 2 + 1, {
    sorry
  },
  sorry


lemma Add_cube (a b : N) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3:=
by
  sorry -- ring



