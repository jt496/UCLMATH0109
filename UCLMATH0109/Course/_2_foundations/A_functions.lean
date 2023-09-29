import Mathlib.Tactic.Basic
  
/-
## What is Lean?   

Lean is at least three things: 

1) A programming language in which we can write proofs (and more);

2) A kernel that can verify the correctness of proofs written in this language;

3) A set of tactics that help us to write proofs (automation).

We will gradually introduce the Lean language and we will rely on its kernel to check 
our code/proofs. We will also introduce the various tactics. 

We will see our first tactic `exact` below.

## Comments 

Everything in green or orange text is a comment. 

This means that Lean ignores it.

A single line comment starts with --

A multi-line comment starts with /- and s with -/

A doc-string comment starts with /-- and s with -/

Comments are our way of explaining what our code does.

 
# Types and terms (sets and elements)

Lean is based on type theory. 

Rather than sets and elements, in Lean we have types and terms. 

As mathematicians we write `n ∈ ℕ` to express the fact that n is an element 
of the set of natural numbers. 

In Lean we write `(n : ℕ)` to say that `n` is  a **term** of **type** `ℕ`. 

As you will see everything in Lean has a type.  

Your mental model of this should be that types are sets and terms are elements.


## Infoview: an example

One of the most helpful tools that Lean has is the Infoview.

Open the `Infoview` panel by pressing `Ctrl + Shift + Enter`

You should now have a constructor-window with this Lean code file
on the left and the `Lean Infoview` on the right.

Before we start to introduce the Lean syntax and tactics,
let's first see what information the Infoview provides.

As you move your cursor through the lines of code below, watch how
the Infoview updates. -/

-- 01
example  (A : Type) (x : A) : A := 
by
/-
If you place your cursor anywhere within this comment 
the Infoview should display:
1 goal
A : Type
x : A
⊢ A
-/
  exact x
-- place your cursor here to see `No goals`

/-
# Infoview: local context + goal ⊢ 
There are two parts to the Infoview. 

The top part of the Infoview is called the **local context** and contains a list
of all the terms that are currently available together with their types.

In our example the local context was:

A : Type
x : A

The last line of the Infoview, containing the turnstile symbol `⊢`, is called 
the **goal** and tells us the type of the term that Lean wants us to construct. 

In our example the goal was:

⊢ A

# Function types (tactics: sorry / exact / apply / intro)

If A and B are types, then `A → B` is the type of functions from A to B. 

(If you place your cursor over any symbol, VSCode will tell you how to write it,
for example `→` is `\r`.)  

If `f : A → B` and `a : A` then `f a` is Lean for `f(a)`. 
This may look strange, but will actually make our proofs easier to read.

What does it mean to say that `f : A → B`? 

Well, for each `a : A` we should have `f a : B`

# Tactics 

We have already seen a tactic in the example above: `exact`.

A tactic in Lean is any command that we can use within a `by ... ` block. 

Some tactics are very simple, such as `exact t` which simply tells Lean to use the term `t` to
close the current goal, while others can solve complicated calculation problems.

Our next tactic is `sorry`. This is a magic tactic that will close any goal. 

Unfortunately this is cheating (notice the example below has a yellow wavy-line under it to 
warn us that something is wrong and `sorry` is in bright red).

Throughout this course you will encounter Lean code containing `sorry` that you will need to 
edit, replacing the `sorry` with an actual proof of the required goal.

Can you replace the `sorry` with something that will actually accomplish the goal? 
-/

-- 02
example (A B C : Type) (x : A) (y : B) (z : C) : B :=
by
/- 
1 goal
A B C : Type
x : A
y : B
z : C
⊢ B
-/
  sorry

-- 03
example  (A B : Type) (f : A → B) (a : A) : B :=
by
/-
1 goal
A B : Type
f : A → B
a : A
⊢ B
-/
  exact f a
/- 
A different way to complete the same goal is to use the `apply` tactic.

Our goal is `⊢ B` and we have `f : A → B` and `a : A` so we can construct a term 
of type B by applying f. 
-/
-- 04
example (A B : Type) (f : A → B) (a : A) : B :=
by
/-
1 goal
A B : Type
f : A → B
a : A
⊢ B
-/
  apply f
/-
Our goal has changed from `⊢ B` to `⊢ A`. 
Since our goal is now `⊢ A` we can close it with `exact a` since `a : A`-/
  exact a  


-- 05
example  (A B C : Type) (f : A  → B) (g : B → C) (a : A) : C :=
by
-- goal `⊢ C`
  apply g -- goal changes from `⊢ C` to `⊢ B` 
  apply f -- goal changes from `⊢ B` to `⊢ A`
  exact a -- done!


-- 06
example (A B C D: Type) (f : A  → B) (g : B → C) (h : C → D) (a : A): D :=
by
  sorry

-- 07
example (A B C D E : Type)(f :A → B) (g: B → C) (h: D → E) (i : C → E) (x : A) : E:=
by
  sorry
 


/- So far our examples have involved applying functions to obtain new terms,
 but what if our goal is to construct a function itself?

  In order to define a function we need a new tactic: `intro`    -/

-- 08 
example (A: Type) : A → A :=
by
/-
1 goal
A : Type
⊢ A → A 
-/
  intro x -- Now we have a `x : A`, a term x of type A and our goal is now `⊢ A`
/-
1 goal
A : Type
x : A
⊢ A
-/
  exact x  


-- 09 
example (A B: Type)(b : B) : A → B :=
by
  intro a -- greyed out variable since we don't use it
  exact b


-- 10
example  (A B C : Type) (f : A → B) (g : B → C) : A → C:=
by
  sorry


-- 11
example (A B C D: Type) (f : A → B) (g : C → D) : (A → B) → (C → D):=
by
  sorry
/-
# Now do sheet2A.lean
-/