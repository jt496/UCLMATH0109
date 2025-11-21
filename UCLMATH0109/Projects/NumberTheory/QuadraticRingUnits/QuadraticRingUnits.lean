import Mathlib.Tactic

/-
Construct the ring `R = ℤ[α]`, where `α = (1 + √13) / 2` and find its units.
-/

/-
Every element has the form `x + y * α` with integers `x`, `y`.
-/
@[ext] structure R where
  x : ℤ
  y : ℤ

namespace R

/-
Definitions of addition, multiplication, etc. in `R`.
-/
def zero : R := ⟨0,0⟩
def one : R := ⟨1,0⟩
def α : R := ⟨0,1⟩
def add (a b : R) : R := ⟨a.x + b.x, a.y + b.y⟩
def mul (a b : R) : R := ⟨a.x * b.x + a.y * b.y,a.x * b.y + a.y * b.x + 3 * a.y * b.y⟩
def neg (a : R) : R := ⟨-a.x, -a.y⟩

/-
Make `R` into a commutative ring with these operations.
-/
instance : CommRing R := sorry

@[simp] lemma alpha_sq : α^2 = α + 3 :=
by
  sorry


def conj : R →+* R where
  toFun a := a.x + a.y * (1 - α)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def norm : R →* ℤ where
  toFun a := a.x ^ 2 + a.x * a.y - 3 * a.y ^ 2
  map_one' := sorry
  map_mul' := sorry

lemma norm_eq_self_mul_conj : norm a = a * conj a :=
by
  sorry

lemma norm_eq_zero_iff : norm a = 0 ↔ a = 0 :=
by
  sorry

def u₁ : Rˣ where
  val := 1 + α
  inv := 2 - α
  val_inv := sorry
  inv_val := sorry

lemma norm_unit (u : Rˣ) : norm u = 1 ∨ norm u = -1 := by
  sorry

lemma unit_iff_norm : (∃ u : Rˣ, u = a) ↔ (norm a = 1 ∨ norm a = -1) :=
by
  sorry

/-
To use inequalities in `R`, we need to think of
elements of `R` as real numbers. This is done using the
following ring homomorphism `R →+* ℝ`.
-/
noncomputable section

def rt13 := Real.sqrt 13
notation3 "√13" => rt13

def α' := (1 + √13) / 2

def σ : R →+* ℝ where
  toFun a := a.x + a.y * α'
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

def x_ : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => x_ n + 3 * x_ (n + 1)

def y_ : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => y_ n + 3 * y_ (n + 1)


/-
Prove the formula for `u₁ ^ n` in terms of `x_ n` and `y_ n`.

Prove that every unit in `R` has the form `± u₁ ^ n`.

Prove the formula for the solutions in natural numbers to

  `x^2 + x*y - 3*y^2 = 1.`

-/
example (x y : ℕ) (h : x ^ 2 + x * y - 3 * y^2 = 1) :
    ∃ n, Even n ∧ x = x_ n ∧ y = y_ n := sorry
