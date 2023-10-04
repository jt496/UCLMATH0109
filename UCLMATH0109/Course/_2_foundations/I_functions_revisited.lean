import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
/-
# Functions: λ notation
-/
def doubleN : ℕ → ℕ :=
by
  intro n
  exact 2*n

#check doubleN -- ℕ → ℕ

#print doubleN

def doubleN' : ℕ → ℕ := fun n => 2*n

#check doubleN 4 -- doubleN 4 : ℕ

#reduce doubleN 4 -- 8

#eval doubleN 4

#print doubleN -- def double : ℕ → ℕ := 
              -- λ (n : ℕ), 2 * n
/-
In Lean `λ a, b` is a function that maps `a` to `b`, i.e. what most mathematicians 
would write as `a ↦ b`

# Functions of more than one variable (currying) 

If we want to define a function mapping a pair of natural numbers 
to the sum of their squares we could write:

  `f : ℕ × ℕ → ℕ`
  `fun (x, y) =>  x^2 + y^2`

We could also use the following function
  `g : ℕ → ℕ → ℕ` (remember this means `g : ℕ → (ℕ → ℕ)` )
   `fun x y => x^2 + y^2`

In many situations this second version will be much more useful, because it 
can be partially evaluated. 

So why might you want to partially evaluate a function?

One important reason is that it allows us to extend the definition of a function!

# Depent types (polymorphism and more)

In mathematics a function is defined by specifying its domain `X` and codomain
`Y` and then some rule for how to how obtain `f(x) ∈ Y` given `x ∈ X`.

In particular `X` and `Y` are part of the definition and are fixed.

Now consider the identity function we define below.

What are its domain and codomain?
-/

def identity (A : Type) (a : A) :  A :=
by
  exact a


/-
`identity` is a function whose first argument is a Type, called A, and whose 
second argument is a term of type A. 

If we partially apply `identity` to a type A we get the identity function 
on A, `identity A`  -/


#check identity ℕ 4 -- identity ℕ 4 : ℕ

#reduce identity ℕ 4 -- 4

#check identity ℕ -- identity ℕ : ℕ → ℕ

#reduce identity ℕ -- λ (a : ℕ), a 

#check identity (List ℕ) [1,2,4] -- identity (List ℕ) [1, 2, 4] : List ℕ

#check identity (List ℕ) -- : List ℕ → List ℕ 

#reduce identity (List ℕ) -- λ (a : List ℕ), a

#check identity -- identity : Π (A : Type), A → A

#reduce identity -- λ (A : Type) (a : A), a 

/-
# Explicit versus implicit variable

Lean has the ability to infer variable from context.

For example, in `identity ℕ 4`, Lean can infer the type ℕ from 4 (which it knows
is a term of type ℕ).

To get Lean to do this we replace `ℕ` with an `_` (underscore).   -/

#check identity _ 4 -- identity ℕ 4 : ℕ

#check identity _ [1,2,4] -- identity (List ℕ) [1, 2, 4] : List ℕ

/-
In situations like this we can tell Lean to always infer the type A 
by making `A : Type` an implicit variable. 
-/

def identity' {A : Type} (a : A) : A:=
by
  exact a


#check identity' -- identity' : ?M_1 → ?M_1

-- The ?M_1 are meta-variable and we can ask Lean to tell us what they will
-- be by adding the `@` symbol

#check @identity' -- identity' : ?M_1 → ?M_1


#check identity' 3 -- identity' 3 : ℕ

#reduce @identity' -- λ {A : Type} (a : A), a

#check identity' [1,2] -- identity' [1, 2] : List ℕ


def twice (A : Type) : (A → A) → (A → A) :=
by 
  intros f a 
  exact (f (f a))


#print twice -- def twice : (ℕ → ℕ) → ℕ → ℕ :=
              -- λ (f : ℕ → ℕ) (n : ℕ), f (f n)
/-
So λ f n, 
-/      

#reduce twice ℕ (twice ℕ (twice ℕ doubleN)) 3






