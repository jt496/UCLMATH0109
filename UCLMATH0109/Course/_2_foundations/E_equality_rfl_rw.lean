import Mathlib.Tactic

/-
So far we have only considered abstract propositions and predicates, we now turn
to some actual mathematics, starting with proving equalities. 


# Equality (tactic : rfl)

Mathematicians rarely worry about what the `=` symbol means, but in Lean we need to 
distinguish between three different uses of the `=` symbol.

If two terms are identical we say that they are **syntactically equal** 

If our goal is a syntactic equality: `⊢ a = a` then `rfl` will complete the proof.-/

--01 a synactic equality 
example (i j : ℕ): i + j = i + j :=
by
  rfl

/-
In fact `rfl` can do much more than this. Consider the term `2 + 3 * 3` in `ℕ`.
This reduces to `11` by unfolding the definitions of `+` and `*`.  
[We can check this by using the `#reduce` command]  -/

#reduce 2 + 3 * 3 -- 11

/-
We say that two terms `a` and `b` are **definitionally equal** if they reduce to the same 
term by unfolding definitions. 

If our goal is `⊢ a = b`, where `a` and `b` are definitionally equal, then `rfl` 
will also complete the proof.
-/
-- 01 
example : 1 + 1 = 2:=
by
  rfl


-- 02
example (n : ℕ) : n + 0 = n :=
by
  rfl

/-
The reason that `rfl` works in the last example is that `n + 0` is defined to be `n`
-/
variable (i j k m n : ℕ)
#reduce n + 0 -- n
/-
Unfortunately `0 + n` is not defined to be `n`, 
-/
#reduce 0 + n 

#print Nat.add

/-
Those of you who have played the Natural Numbers Game will recall that
in Lean ℕ addition is defined inductively on the 2nd argument:
 a + 0 => a
 a + (succ b) => succ (a + b)
-/


/-
It is still true that `0 + n = n` but this is a theorem not a definition!
This is an example of a `propositional equality`, and since it is not a definitional
equality `rfl` will fail.
-/
-- 03 
example  : 0 + n = n :=
by
 -- rfl -- does not work!
 -- we need to use a theorem (more on these later)
  exact zero_add n

/- 
`rfl` is short for `reflexivity` and `rfl` can prove any proposition that follows by unfolding 
definitions and applying reflexivity (note that `=` is just one example of a reflexive relation
another common one is `↔`)
-/
-- 04 iff is rflexive 
example (P : Prop) : P ↔ P :=
by
  rfl


-- 05 the definition of `a ∣ b` in ℕ is `∃ k, b = a * k` 
example : 2 ∣ n ↔ ∃ k, n = 2 * k:=
by
  rfl



/-
# Substitution /rewriting (tactics : rw / rwa ) 

One fundamental property of `=` is that if `a = b` then we can substitute `b` for `a`
in any expression containing `a`.

For example, if `a = 3` and we have `c = a + 4` then we know `c = 3 + 4`

The Lean tactic for this is `rw`  (short for rewrite)

Given any hypothesis of the form `h : a = b` we can use `rw [h]` to replace all occurences 
of `a` by `b` in the goal.

For this to work the occurence of `a` in the goal must be syntactically equal to a.
-/
-- 06
example (h1: i = j) (h2 : j = k) : i = k :=
by
  rw [h1]
  exact h2

/-
A variant of `rw` is `rwa` which does a rewrite and then checks to see if one of the terms
in the local context matches the goal, if it finds one then it closes the goal.

The `a` in `rwa` is short for `assumption`
-/
-- 07 
example  (h1: i = j) (h2 : j = k) : i = k :=
by
  rwa [h1]

/-
We can group a sequence of rewrites together as follows `rw [h1, h2]`

After every `rw` Lean will try to use `rfl` to close the goal. 
This explains why the following proof ends so abruptly!
-/
-- 08
example  (h1: i = j + k) (h2 : j = k + k) : i = k + k + k:=
by
  rw [h1, h2] 


/-
The `rw` tactic is very versatile.

If `h : a = b` then `rw [h]`  replaces `a` by `b` in the goal.

We can also do `rw [← h]` to replace `b` by `a` in the goal.

If `h2` is another term in the local context then `rw [h] at h2` replaces
`a` by `b` in `h2`.

-/
-- 09 
example  (h1 : i = j) ( h2: j = k) (h3 : m = k) (h4 : n = m) : n = i :=
by
  rwa [h1,h2, ← h3]


-- 10
example (h1 : i = j) ( h2: j = k) (h3 : m = k) (h4 : n = m) : i = n :=
by
  rw [← h4] at h3 
  rw [← h3] at h2
  rwa [h1]


/- 
If we have a hypothesis (or theorem) of the form `h : ∀ a b , ... = ...`
then we can use `rw [h i j]` to rewrite using this equality in the case 
`a = i` and `b = j`. 

We can also use `rw [h]` and Lean will choose `i` and `j` for us.

This is quite different to the simple substitution that occurs in previous examples, 
since Lean now needs to decide how to choose values for `i` and `j`. 

-/
-- 11 
example (hcomm : ∀ (i j : ℕ), i + j = j + i) : 7 + n = n + 7 :=
by
  rw [hcomm] 

-- 12
example (hcomm: ∀ (i j : ℕ), i + j = j + i) : k + m + n = n + (m + k) :=
by
  -- Original goal ⊢ k + m + n = n + (m + k)
  rw [hcomm]
  -- New goal      ⊢ n + (k + m) = n + (m + k) 
  
  /- Notice that Lean chose to perform the rw at what looks like the 2nd `+` symbol
     in the goal.

    To understand what Lean did here we need to think about how it parses the 
    original goal

    `⊢ k + m + n = n + (m + k)`
    
    We can draw a tree diagram to explain how Lean sees this:
    The goal is a `Prop` asserting `=` so we place this at the top of the 
    tree and then look at each side separately.
    On the LHS we have `k + m + n`, but remember that Lean does not display the implied 
    brackets `(k + m) + n`, so the  first `+` it sees is between `(k+m)` and `n`.

    Lean looks at the tree from top down, taking the left branch first until it finds
    a place were `rw [hcomm]` can be performed

                                   =   
                               /       \
the 1st `+` in the goal -->  `+`        + 
                             / \       / \
                            +   n     n   +
                           / \           / \ 
                          k   m         m   k   

    After the rw the new goal `⊢ n + (k + m) = n + (m + k)` is parsed as

                                   =   
                               /       \
                              +         + 
                             / \       / \
                            n   +     n   +
                               / \       / \ 
                              k   m     m   k   


   If we just did `rw [hcomm]` again we would be back where we started so instead we use -/
  rw [hcomm k]
  /- 
  This finds the 1st occurence of `k + _` and performs the rw here
 
  [If you place your cursor inside the `rw [hcomm k]` you can see the rw performed] 
 
  The goal is now closed by rfl since the two sides of the equality are identical.

  One point this last example misses is that once Lean decides on the values to use in a `rw`
  it then treats this a standard substitution, so it will replace all occurences that match
  this particular choice. The next example shows how this works  -/

example (hcomm: ∀ (i j : ℕ), i + j = j + i) : (k + m) + (k + m) = (m + k) + (m + k) :=
by
/- In the following rewrite Lean is given `i = k` and then needs to choose a value for `j`
   so it can do the rewrtite `hcomm k j`
   It finds `j = m` and then performs the command `rw [hcomm k m]` which 
   changes both occurences of `k + m`  -/ 
  rw  [hcomm k]
/-
# Using theorems (tactics: rw / apply)

As well as performing rewrites using the local context we can
also use theorems from Mathlib

Below we use commutativity and associativity of addition in ℕ
to prove a simple identity.

[We prove the same result twice, the proofs are identical but the
second proof has a detailed commentary.]

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
  rw [Nat.add_comm x]--add_comm u,←add_assoc]
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


/-
# Now do sheet2E.lean
-/
