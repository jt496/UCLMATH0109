import Mathlib

/--
We define a structure `R`.
Elements of `R` have three coordinates `x`, `y`, and `z`, each of which is a real number.
-/
@[ext]structure R where
  x : ℝ
  y : ℝ
  z : ℝ

/-
We define a multiplication operation of `R`.
-/
@[simps] instance : Mul R where
  mul a b := {
    x := a.x * b.x + a.y * b.z + a.z * b.y,
    y := a.x * b.y + a.y * b.x + a.z * b.z,
    z := a.x * b.z + a.y * b.y + a.z * b.x
  }

/-
We define an element `1 : R`.
-/
@[simps] instance : One R := ⟨1, 0, 0⟩

/-
With these operations, `R` is a "commutative monoid".
This means that multiplication in `R` is commutative and associative and `1` is the identity element.
-/
instance : CommMonoid R where
  mul_assoc _ _ _       := by ext <;> {dsimp; ring}
  one_mul _             := by ext <;> simp
  mul_one _             := by ext <;> simp
  mul_comm _ _          := by ext <;> {dsimp; ring}


-- # 1 (2 marks)
/-
Prove that the function `N a = a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - (a.x * a.y + a.y * a.z + a.z * a.x)`
is a homomorphism, i.e. this function satisfies the conditions

* `N 1 = 1`, and
* `N (a * b) = (N a) * (N b)`.

-/
@[simp] def N : R →* ℝ where
  toFun a   := a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - (a.x * a.y + a.y * a.z + a.z * a.x)
  map_one'  := sorry
  map_mul'  := sorry

/--
An element `a : R` is constant if `a.x = a.y = a.z`.
-/
@[simp] def IsConstant (a : R) : Prop := a.x = a.y ∧ a.y = a.z



-- # 2 (5 marks)
lemma N_eq_zero_iff (a : R) : N a = 0 ↔ IsConstant a := by
  /-
  Hint : You may find it useful to first prove the formula
    `N a = ((a.x - a.y)^2  + (a.y - a.z)^2 + (a.z - a.x)^2) / 2`.

  -/
  sorry


-- # 3 (2 marks)
/-
Define a homomorphism `Tr` from `R` to `ℝ`,
which takes an element `a` to the real number `a.x + a.y + a.z`.
-/
@[simp] def Tr : R →* ℝ where
  toFun := fun a ↦ a.x + a.y + a.z
  map_one' := sorry
  map_mul' := sorry





-- # 4 (3 marks)
/-
Let `φ : R →* ℝ` be a homomorphism from `R` to `ℝ`.
Prove that if `a * b = 1` in `R`, then `φ a ≠ 0` in `ℝ`.
-/
lemma map_nonzero {a b : R} (φ : R →* ℝ) (h : a * b = 1) : φ a ≠ 0 := by
  sorry



-- # 5 (2 marks)
theorem exists_inv_iff (a b : R) (hb : a * b = 1) : N a ≠ 0 ∧ Tr a ≠ 0 := by
  sorry


@[simp] noncomputable instance : Inv R where
  inv a := {
    x := (a.x ^ 2 - a.y * a.z) / (N a * Tr a)
    y := (a.z ^ 2 - a.x * a.y) / (N a * Tr a)
    z := (a.y ^ 2 - a.x * a.z) / (N a * Tr a)
  }

-- # 6 (6 marks)
/-
The previous lines defined an inverse operation on `R`.
State and prove a theorem, saying that if `N a ≠ 0` and `Tr a ≠ 0` then `a * a⁻¹ = 1`.
-/
