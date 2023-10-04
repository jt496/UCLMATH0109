import Mathlib.Tactic

/-
So far we have only considered abstract propositions and predicates, we now turn
to some actual mathematics, starting with proving equalities. 


# Equality (tactic : rfl)

Mathematicians rarely worry about what the `=` symbol means, but in Lean we need to 
distinguish between three different uses of the `=` symbol.

If two terms are identical we say that they are **syntactically equal** 

If our goal is a syntactic equality: `⊢ a = a` then `rfl` will complete the proof.-/

-- 01 a synactic equality 
example (i j : ℕ) : i + j = i + j :=
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
-- 02
example : 1 + 1 = 2 :=
by
  rfl


-- 03
example (n : ℕ) : n + 0 = n :=
by
  rfl


/-
The reason that `rfl` works in the last example is that `n + 0` is defined to be `n`
-/
section
variable (i j k m n : ℕ)

#reduce n + 0 -- n
/-
Unfortunately `0 + n` is not defined to be `n`, 
-/
#reduce 0 + n 

#print Nat.add

/-
Those of you who have played the Natural Numbers Game will know that
in Lean ℕ is defined `inductively` by 

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

So `succ 0` is what we call `1` and `succ 1` is `2` etc. 

Addition is then defined inductively on the 2nd argument:

def Nat.add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)

0 + 2 = 0 + (succ 1) => succ (0 + 1) = succ (0 + succ 0) => succ (succ (0 + 0)) => succ (succ 0) = 2

It is still true that `0 + n = n` but this is a theorem not a definition!

This is an example of a `propositional equality`, and since it is not a definitional
equality `rfl` will fail. -/

-- 04 
example  : 0 + n = n :=
by
  exact zero_add n

/- 
`rfl` is short for `reflexivity` and `rfl` can prove any proposition that follows by unfolding 
definitions and applying reflexivity (note that `=` is just one example of a reflexive relation
another common one is `↔`)
-/
-- 05 iff is reflexive 
example (P : Prop) : P ↔ P :=
by
  rfl


-- 06 the definition of `a ∣ b` in ℕ is `∃ k, b = a * k` 
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

-- 07
example  (h1: i = j) (h2 : j = k) : i = k :=
by
  rw [h1]
  exact h2

/-
A variant of `rw` is `rwa` which does a rewrite and then checks to see if one of the terms
in the local context matches the goal, if it finds one then it closes the goal.

The `a` in `rwa` is short for `assumption`
-/
-- 08 
example  (h1: i = j) (h2 : j = k) : i = k :=
by
  rwa [h1]

/-
We can group a sequence of rewrites together as follows `rw [h1, h2]`

After every `rw` Lean will try to use `rfl` to close the goal. 
This explains why the following proof ends so abruptly!
-/
-- 09
example  (h1: i = j + k) (h2 : j = k + k) : i = k + k + k:=
by
  rw [h1,h2]



/-
The `rw` tactic is very versatile.

If `h : a = b` then `rw [h]`  replaces `a` by `b` in the goal.

We can also do `rw [← h]` to replace `b` by `a` in the goal.

-/
-- 10 
example  (h1 : i = j) ( h2: j = k) (h3 : m = k) (h4 : n = m) : n = i :=
by
  rwa [h1, h2,← h3]

/-

If `h2` is another term in the local context then `rw [h] at h2` replaces
`a` by `b` in `h2`.

-/

-- 11
example (h1 : i = j) ( h2: j = k) (h3 : m = k) (h4 : n = m) : i = n :=
by
  rw [← h4] at h3
  rw [← h3] at h2
  rwa [h1]


end

/- 
##  More sophisticated rewrites

If we have a hypothesis (or theorem) of the form `h : ∀ a b , ... = ...`
then we can use `rw [h i j]` to rewrite using this equality in the case 
`a = i` and `b = j`. 

We can also use `rw [h]` and Lean will choose `i` and `j` for us.

This is quite different to the simple substitution in previous examples, 
since Lean now needs to decide how to choose values for `i` and `j`. 

-/
section
variable (k m n : ℕ)
-- 12 
example (hcomm : ∀ (i j : ℕ), i + j = j + i) : 7 + n = n + 7 :=
by
  rw [hcomm]

-- 13
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
    brackets `(k + m) + n`, so the  first `+` it sees is between `(k + m)` and `n`.

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
 
  The goal is now closed by rfl since the two sides of the equality are identical.  -/

-- 14
example (hcomm: ∀ (i j : ℕ), i + j = j + i) : (k + m) + (k + m) + (k + a) = (m + k) + (m + k) + (a + k):=
by
  rw [hcomm k,hcomm k]




end


/-
# Now do sheet2E.lean
-/
