import Mathlib.Tactic

/-
# Using theorems with rw

As well as performing rewrites using the local context we can also use theorems from Mathlib

Below we use commutativity and associativity of addition in ℕ to prove a simple identity.

[We prove the same result twice, the proofs are identical but the second proof has a detailed commentary.]

-/  
variable (u v w x y: ℕ)
#check Nat.add_comm
/-
Nat.add_comm (n m : ℕ) : n + m = m + n
-/
#check Nat.add_assoc
/-
Nat.add_assoc (n m k : ℕ) : n + m + k = n + (m + k)
-/

lemma short : (u + v) + (x + y)= y + x + v + u:=
by
  rw [Nat.add_comm,Nat.add_comm x,Nat.add_comm u,←Nat.add_assoc]

lemma long : (u + v) + (x + y)= y + x + v + u:=
by
/- Original goal
    ⊢ u + v + (x + y) = y + x + v + u   
 With all implied brackets we have: 
    ⊢ (u + v)  + (x + y) = (((y + x) + v) + u)

                                  =   
                          /              \
                         +                + 
                       /   \            /   \
                      +     +          +     u
                     / \   / \        / \ 
                    u   v x   y      +   v   
                                    / \
                                   y   x          
-/
  rw [Nat.add_comm]
/- New goal 
  ⊢ x + y + (u + v) = y + x + v + u

                                  =   
                          /              \
                         +                + 
                       /   \            /   \
                      +     +          +     u
                     / \   / \        / \ 
                    x   y u   v      +   v   
                                    / \
                                   y   x     
-/  
  rw [Nat.add_comm x]
/- New goal
  ⊢ y + x + (u + v) = y + x + v + u

                                  =   
                          /              \
                         +                + 
                       /   \            /   \
                      +     +          +     u
                     / \   / \        / \ 
                    y   x u   v      +   v   
                                    / \
                                   y   x     
-/
  rw [Nat.add_comm u]
/- New goal
  ⊢ y + x + (v + u) = y + x + v + u

                                  =   
                          /              \
                         +                + 
                       /   \            /   \
                      +     +          +     u
                     / \   / \        / \ 
                    y   x v   u      +   v   
                                    / \
                                   y   x     
Everything is now in the same order on both sides so
we now need to use associativity

-/
  rw [← Nat.add_assoc]
/- This looks for the 1st occurrence of `n + (m + k)` and rewrites it to `(n + m) + k`
   using associativity. 

   It finds this on the LHS with `(y + x)` as `n`, `v` as `m` and `u` as `k`. 

   So `(y + x) + (v + u)` becomes `(y + x) + v + u` which is definitionally the same
   as `y + x + v + u` so Lean closes the goal with rfl


Many theorems implications are of the form `P → Q`, rather than identites (which we can rewrite).

We can apply such theorems with the tactics `exact` or `apply` 

For example   -/
#check Nat.add_le_add_left
/-
`Nat.add_le_add_left {n m : ℕ} (h : n ≤ m) (k : ℕ) : k + n ≤ k + m`

This says that `if n ≤ m then for any k ∈ ℕ we have k + n ≤ k + m` 

Notice the two kinds of brackets `{n m : ℕ}` and `(k : ℕ)`

The `{}` are implicit arguments while `()` denote explicit arguments

We usually need to give the explicit arguments, while the implicit arguments
can be deduced by Lean automatically. 

In this case the inequality `h : n ≤ m` is explicit as is `k` but m and n are implicit.

Once we provide the inequality `h`, Lean can work out what `n` and `m` are automatically. 
-/
example (h1: x ≤ y) : 7 + x ≤ 7 + y:=
by
  -- Using `exact` we can close the goal as follows:
  exact Nat.add_le_add_left h1 7

example (h1: x ≤ y) : 7 + x ≤ 7 + y:=
by
  /- In fact Lean can figure out that we need `k = 7` in this application so
     we can miss it out by using `_` to tell Lean -/
  exact Nat.add_le_add_left h1 _



example (h1: x ≤ y) : 7 + x ≤ 7 + y:=
by
  -- We can also use `apply` 
  apply Nat.add_le_add_left
/-   This is particularly useful if we don't already have a proof of `x ≤ y`
     since it changes our goal to `⊢ x ≤ y` 
     Notice Lean worked out that `k = 7`
     We can complete this with                          -/
  exact h1



#check Nat.add_le_add
/-
Nat.add_le_add {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
-/
example (h1: u ≤ v) (h2: x ≤ y) (h3: s ≤ t): u + x + s ≤ v + y + t:=
by
-- Goal ⊢ u + x + s ≤ v + y + t
  apply Nat.add_le_add
-- Now have goals and we use `·` to focus on each in turn
  · apply Nat.add_le_add
    · exact h1
    · exact h2
  · exact h3 

-- Notice that we could shorten this proof as follows:
example (h1: u ≤ v) (h2: x ≤ y) (h3: s ≤ t): u + x + s ≤ v + y + t:=
by 
  apply Nat.add_le_add (Nat.add_le_add h1 h2) h3



#check Nat.mul_le_mul
/-
Nat.mul_le_mul {n₁ m₁ n₂ m₂ : ℕ} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂
-/

example  (h1: u ≤ v) (h2: x ≤ y) (h3: s ≤ t): (u + x)*(s + t) ≤ (v + y)*(t + t):=
by
-- Goal ⊢ (u + x) * (s + t) ≤ (v + y) * (t + t)
  apply Nat.mul_le_mul
  · apply Nat.add_le_add h1 h2  
  · apply Nat.add_le_add h3 
    -- Final goal is `⊢ t ≤ t` which is true by reflexivity of `≤`
    rfl

