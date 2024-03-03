import Mathlib.Tactic

/-
# For students who have already learnt MATH0034 or MATH0035

Construct the ring `R = ℤ[α]`, where `α = (1+√5)/2` and prove
some of its properties.
-/

/-
Every element has the form `x + y * α` with integers `x`, `y`.
-/
@[ext] structure R where
  x : ℤ
  y : ℤ

namespace R

def zero : R := ⟨0,0⟩
def one : R := ⟨1,0⟩
def α : R := ⟨0,1⟩
def add (a b : R) : R := ⟨a.x + b.x, a.y + b.y⟩
def mul (a b : R) : R where
  x := a.x * b.x + a.y * b.y
  y := a.x * b.y + a.y * b.x + a.y * b.y
def neg (a : R) : R := ⟨-a.x, -a.y⟩

instance : CommRing R := sorry

@[simp] lemma alpha_sq : α^2 = α + 1 :=
by
  sorry

def conj : R →+* R where
  toFun a := ⟨a.x + a.y, -a.y⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def norm : R →* ℤ where
  toFun a := a.x ^ 2 + a.x * a.y - a.y ^ 2
  map_one' := sorry
  map_mul' := sorry

lemma norm_eq_self_mul_conj : norm a = a * conj a :=
by
  sorry

lemma norm_eq_zero_iff : norm a = 0 ↔ a = 0 :=
by
  sorry

def u₁ : Rˣ where
  val := α + 1
  inv := -α
  val_inv := sorry
  inv_val := sorry

lemma norm_unit (u : Rˣ) : norm u = 1 ∨ norm u = -1 := by
  sorry

lemma unit_iff_norm : (∃ u : Rˣ, u = a) ↔ (norm a = 1 ∨ norm a = -1) :=
by
  sorry

/-
Now create the embeddings of `R` into `ℝ`.
-/
noncomputable section

def rt5 := Real.sqrt 5
notation "√5" => rt5

def α₁ := (1 + √5)/2
def α₂ := (1 - √5)/2

def σ₁ : R →+* ℝ where
  toFun a := a.x + a.y * α₁
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def σ₂ : R →+* ℝ where
  toFun a := a.x + a.y * α₂
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-
Recover the `x` and `y` coordinated from the field embeddings.
-/
lemma x_eq : a.x = (σ₁ a + σ₂ a) / 2 :=
by
  sorry

lemma y_eq : a.y = (σ₁ a - σ₂ a) / √5 :=
by
  sorry

/-
The Fibonacci sequence is defined in Mathlib as `Nat.fib`.
Show that if we have a solution in natural numbers to the equation
`x^2 - x*y - y^2 = ± 1`, then `x` and `y` are consecutive Finonacci numbers.
-/

lemma u_fundamental (h : |norm a| = 1) : ∃ n : ℤ, a = u₁ ^ n ∨ a = - u₁ ^ n :=
by
  sorry


/-
# Extension

You can try proving that the ring is norm-Euclidean.
I.e. given `a b : R` with `b ≠ 0`, prove that there exist
`q r : R` such that `a = q * b + r` and `|norm r| < |norm b|`.
-/
