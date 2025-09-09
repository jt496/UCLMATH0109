import Mathlib
/-
"Mathlib" is a huge database of mathematical theorems all written in lean.
It currently has well over 3000 files, each containing many theorems.
The first line of this file allows us to use any theorem in Mathlib.

Often, we are faced with proving a very simple goal, which is almost certainly
already in Mathlib. Typing `exact?` will search Mathlib and try to find the
theorem that we need.
-/

variable (x y : ℝ) (h : x < y)
/-
From now on, `x` and `y` will be real numbers and `h` will be a proof that `x < y`.
We can use these variables within any proof, but also outside of a proof
with the `#check` command.
-/

#check x
#check h

/-
Given the hypothesis `h : x < y`, it should be fairly easy to prove that `x ≤ y`.
We can use `exact?` to help us with this.
-/
example : x ≤ y :=
by
  --try searching using Mathlib using `exact?`
  sorry

/-
We can look up the theorem `le_of_lt` in the *API documentation* of
Mathlib to see exactly what it says.
We can also use the command `#check` to do this.
Also "ctrl-click" on `le_of_lt` will take us to the file
in Mathlib where this theorem is proved.
-/
#check le_of_lt

/-
We can think of the theorem `le_of_lt` as a function, which takes a
long list of arguments and returns a proof of the statement `a < b`.
The arguments are listed before the `:`.

Note that some of the arguments are contained in `( )`, some in `{ }`
and some in `[ ]`. The arguments contained in `( )` are called
**explicit arguments**, and the others are called **implicit arguments**.
If we type `le_of_lt h`, then lean will assume that `h` is the explicit
argument. It is usually not necessary to provide the implicit arguments,
because lean can work out for itself what values they need to take.

In the case of `le_of_lt`, the only explicit argument is `h : a < b`.
If we give it a value of `h`, then it can deduce the what `a` and `b`
are, and also that `α = ℝ`, since this is the type of the variables
`a` and `b`.
-/
#check le_of_lt h     -- `x ≤ y`

/-
It sometimes happens that we need to tell lean the values of implicit
variables. For example, to give the values of `a` and `b` but not the
hypothesis `h`, we can type this:
-/

#check le_of_lt (a := x) (b := y)    -- `x < y → x ≤ y`
