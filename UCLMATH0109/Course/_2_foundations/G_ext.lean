import Mathlib.Tactic
/-
# Functions: fun => notation

We have already seen how to define functions using tactics, however it
will be useful to also know the `λ` style function notation that Lean uses
to display functions in infoview.



-/

def triple1 : ℕ → ℕ :=
by
  intro n
  exact 3 * n

def triple2 : ℕ → ℕ := fun n => 3 * n

def triple3 : ℕ → ℕ := fun n => 2*n + n   

def triple4 : ℕ → ℕ := fun n => n + n + n

example : triple1 = triple2 := rfl

example : triple3 = triple4 :=
by
  ext n
  rw [triple3, triple4, two_mul]
  












