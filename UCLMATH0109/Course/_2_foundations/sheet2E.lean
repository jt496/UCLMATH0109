import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
variable (a b c d e i j k: ℕ)
variable (f : ℕ → ℕ)
/-
In this sheet we will practice using `rw` and `apply` to prove simple results
in ℕ (the natural numbers)

The natural numbers are defined as follows:

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat


You should read this as saything there are two ways to make `k : ℕ`
Either `k` is `zero` or `k` is the successor of a previously constructed
n : ℕ, and we call this `succ n`


In the rest of this sheet you should complete the examples, using the 
theorems that are provided.

Note that we are only using theorems about `ℕ` so they start `Nat.`
Many of these results exist in more general forms, but for now we
only use the `Nat` versions
-/
#check Nat.add_zero      -- ∀ (n : ℕ), n + 0 = n
#check Nat.add_comm      -- ∀ (n m : ℕ), n + m = m + n
#check Nat.add_comm a    -- ∀ (m : ℕ), a + m = m + a
#check Nat.add_assoc     -- ∀ (n m k : ℕ), n + m + k = n + (m + k)   
#check Nat.add_assoc a b -- ∀ (k : ℕ), a + b + k = a + (b + k))
-- 01
example : a + b + c = (a + 0) + c + (b + 0):=
by -- Using `rw` and the theorems above solve this goal
  sorry

#check Nat.mul_comm  -- ∀ (n m : ℕ), n * m = m * n
#check Nat.mul_assoc -- ∀ (n m k : ℕ), n * m * k = n * (m * k)   
#check Nat.add_mul   -- ∀ (n m k : ℕ), (n + m) * k = n * k + m * k
#check Nat.mul_add   -- ∀ (n m k : ℕ),  n * (m + k) = n * m + n * k
#check Nat.one_mul   -- ∀ (n : ℕ), 1 * n = n
#check Nat.zero_mul  -- ∀ (n : ℕ), 0 * n = 0
#check Nat.mul_zero  -- ∀ (n : ℕ), n * 0 = 0
#check Nat.two_mul   -- ∀ (n : ℕ), 2 * n = n + n

/- 
Notice how Mathlib theorems are named to describe their content.

So `Nat.zero_mul` describes multiplication by zero on the left
while `Nat.mul_zero` describes multiplication by zero on the right

Similarly `Nat.add_mul` describes `(n + m) * k`, addition followed by multiplication
while `Nat.mul_add` describes `n * (m + k)` , multiplication followed by addition


-/

--02 
example (h1: a = b*d + c) (h2: c = d*e): a = (e + b)*d:=
by
  sorry
--  rw [h1,h2,Nat.add_mul,Nat.mul_comm d e,Nat.add_comm]

-- 03
example (h1: a + c = d) (h2 : b = 2*c): 2*a + d + b = 3*d   :=
by
  rw [← h1,h2,Nat.two_mul,Nat.two_mul,Nat.succ_mul,Nat.two_mul]
  rw [add_left_comm (a+c),add_left_comm (a + (a+ c + c)) ]
  repeat rw [add_assoc]




--04
example : (a+b)*(a+b) = a*a + 2*a*b + b*b:=
by -- Do this with rewrites using the theorems listed above
--  rw [two_mul,add_mul,add_mul,mul_add,mul_add,mul_comm b a,← add_assoc,← add_assoc]
  sorry


/-
All of theorems listed above are identities so we can use them in rewrites. 

The next list of theorems are implications so we will use `apply` or `exact` 
when using them 
-/
#check Nat.add_le_add 
-- ∀ {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
#check Nat.mul_le_mul
-- ∀ {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : a * c ≤  b * d

-- You may need to do some rewrites first in the proofs below

example (h1: a ≤ b) (h2 : c ≤ d) (h3 : e ≤ f) : a + e + c ≤ b + d + f:=
by
  
  sorry
  -- rw [add_assoc,add_comm e]
  -- apply Nat.add_le_add
  -- · apply Nat.add_le_add h1 h2
  -- · exact h3 

example (h1: a ≤ c) (h2 : b ≤ d) (h3 : e ≤ f) : a*(b + e) ≤ (f + d)*c :=
by
  sorry
  -- rw [Nat.mul_comm,Nat.add_comm]
  -- apply Nat.mul_le_mul
  -- · apply Nat.add_le_add h3 h2 
  -- · exact h1 

#check Nat.le_add_right
-- ∀ (n k : ℕ), n ≤ n + k
#check Nat.le_trans 
-- ∀ {n m k : ℕ} (h1 : n ≤ m) (h2 : m ≤ k) : n ≤ k

example (h1: a ≤ b ) (h2: c ≤ e): a*c ≤ (b + d)*e :=
by
  apply Nat.mul_le_mul
  · apply Nat.le_trans h1
    apply Nat.le_add_right
  · exact h2


#check Nat.le_of_add_le_add_right
-- ∀ {a b c : ℕ}, a + b ≤ c + b → a ≤ c 
#check Nat.le_antisymm 
-- ∀ {n m: ℕ}, n ≤ m → m ≤ n → n = m

example (h1: a ≤ b + c) (h2: e + f + b + c ≤ a + e + f) : a = b + c:=
by
  apply Nat.le_antisymm h1
/- remaining goal is `⊢ b + c ≤ a`  which should follow from `h2` if we
     get it into the correct form to apply `Nat.le_of_add_le_add_right` -/

  sorry



#check Nat.le_succ 
-- ∀ (n : ℕ), n ≤ Nat.succ n 
#check Nat.le_succ 3 -- proves 3 ≤ 4

example (h1: a ≤ b) (h2: c ≤ d) : a + 3*c ≤ 2*b +4*d:=
by
  sorry
  -- apply Nat.add_le_add
  -- · rw [← Nat.one_mul a]
  --   apply Nat.mul_le_mul
  --   · apply Nat.le_succ
  --   · exact h1
  -- · apply Nat.mul_le_mul
  --   · apply Nat.le_succ
  --   · exact h2  
