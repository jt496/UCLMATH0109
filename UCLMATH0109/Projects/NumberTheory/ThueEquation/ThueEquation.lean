import Mathlib
namespace Thue
/-
Define `R` to be the ring `ℤ[α]`, where `α` is a cube root of `2`.
Elements of `R` have the form `x + y * α + z * α ^ 2` for integers `x,y,z`.
Find the units in this ring, and hence find all solutions
in integers to the equation `x ^ 3 - 2 * y ^ 3 = 1`.
-/

@[ext]
structure R where
  x : ℤ
  y : ℤ
  z : ℤ
def α : R := ⟨0,1,0⟩

namespace R

def one : R := ⟨1,0,0⟩
def zero : R := ⟨0,0,0⟩
def add (a b : R) : R := ⟨a.x+b.x, a.y+b.y, a.z + b.z⟩
def neg (a : R) : R := ⟨-a.x,-a.y,-a.z⟩
def mul (a b : R) : R where
  x := a.x * b.x + 2* a.y * b.z + 2* a.z * b.y
  y := a.x * b.y + a.y * b.x + 2 * a.z * b.z
  z := a.x * b.z + a.y * b.y + a.z * b.x

instance : One R := ⟨one⟩
instance : Zero R := ⟨zero⟩
instance : Add R := ⟨add⟩
instance : Neg R := ⟨neg⟩
instance : Mul R := ⟨mul⟩

variable (a b c : R)
lemma one_def : (1 : R) = ⟨1,0,0⟩ := rfl
lemma zero_def : (0 : R) = ⟨0,0,0⟩ := rfl
lemma add_def : a + b = ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩ := rfl
lemma neg_def : - a = ⟨-a.x, -a.y, -a.z⟩ := rfl
lemma mul_def : a * b = {
    x := a.x * b.x + 2* a.y * b.z + 2* a.z * b.y
    y := a.x * b.y + a.y * b.x + 2 * a.z * b.z
    z := a.x * b.z + a.y * b.y + a.z * b.x } := rfl

instance : CommRing R := sorry



noncomputable section

/-
`α₁`, `α₂` and `α₃` are the conjugates of `α` in `ℂ`.
-/
def α₁ : ℝ := (2: ℝ) ^ (1/3 : ℝ)
def ω : ℂ := ⟨-1/2 , Real.sqrt 3 / 2⟩
def α₂ : ℂ := α₁ * ω
def α₃ : ℂ := star α₂

@[simp] lemma alpha₁_pow_three : α₁ ^ 3  = 2 := by
  sorry

@[simp] lemma omega_sq : ω ^ 2 = -ω - 1 := sorry

@[simp] lemma omega_pow_three : ω ^ 3 = 1 := sorry

@[simp] lemma alpha₂_pow_three : α₂ ^ 3 = 2 := sorry

/-
For each conjugate there is a corresponding ring homomorphism
from `ℤ[α]` to `ℂ`.
-/
def σ₁ : R →+* ℝ := sorry
def σ₂ : R →+* ℂ := sorry
def σ₃ : R →+* ℂ := sorry

def σ : R →+* ℝ × ℂ := RingHom.prod σ₁ σ₂

/-
Fill in the `sorry`s in the statement and the proof.
-/
lemma sigma_bound (a : R) (c : ℝ) (h₁ : |σ₁ a| ≤ c) (h₂ : Complex.abs (σ₂ a) ≤ c) :
  a.x ≤ sorry * c ∧ a.y ≤ sorry * c ∧ a.z ≤ sorry * c :=
by
  sorry

@[simp] lemma alpha_pow_three : α^3 = 2 := by
  sorry

/--
The fundamental unit in `R` is the element `1 + α + α^2`.
Its inverse is `α - 1`.
-/
def fund : Rˣ where
  val := 1 + α + α^2
  inv := α - 1
  val_inv := sorry
  inv_val := sorry

noncomputable def ℓ : Rˣ → ℝ := fun u ↦ |σ₁ u|.log

lemma ℓ_one : ℓ 1 = 0 := sorry

lemma ℓ_mul : ℓ (u * v) = ℓ u + ℓ v := sorry

lemma step1 : ℓ fund > 1 := sorry

lemma step2 (u : Rˣ) (hu : ℓ u < ℓ fund) : ℓ u ≤ 0 :=
by
  sorry

theorem unit_eq_fund_pow (u : Rˣ) : ∃ n : ℤ, u = fund ^ n ∨ u = - fund ^ n :=
by
  sorry

theorem unit_iff (x y : ℤ) : (∃ u : Rˣ, x - y * α = u) ↔ |x ^ 3 - 2 * y^3| = 1 :=
by
  sorry

theorem Thue (x y : ℤ) (h : x^3 - 2 * y^3 = 1) : (x = 1 ∧ y = 0) ∨ ( x = -1 ∧ y = -1) :=
by
  sorry
