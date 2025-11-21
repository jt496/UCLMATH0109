import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Basic

/-- An Eisenstein integer is a number of the form `x + y * ω`, where `ω = e ^ (2 * π* i / 3)`
and `x y : ℤ`.
We shall write `EisensteinInt` or `ℤ[ω]` for the Type of Eisenstein integers, with an Eisenstein
integer represented by its `x`- and `y`-coordinates.
-/
@[ext]
structure EisensteinInt : Type where
  x : ℤ
  y : ℤ

namespace EisensteinInt
notation3 "ℤ[ω]" => EisensteinInt

/--We give lean a way of displaying elements of `ℤ[ω]` using the command `#eval`.-/
def repr : ℤ[ω] → Lean.Format
| ⟨0,0⟩ => ↑"0"
| ⟨0,1⟩ => ↑"ω"
| ⟨0,-1⟩=> ↑"-ω"
| ⟨0,y⟩ => y.repr ++ " * ω"
| ⟨x,0⟩ => x.repr
| ⟨x,1⟩ => x.repr ++ " + ω"
| ⟨x,-1⟩=> x.repr ++ " - ω"
| ⟨x,y⟩ => x.repr ++ if y > 0 then " + " ++ y.repr ++ " * ω"
                              else " - " ++ (-y).repr ++ " * ω"

instance : Repr ℤ[ω] where
  reprPrec := fun a _ ↦ repr a

#eval (⟨1, 2⟩ : ℤ[ω])
#eval (⟨0, 0⟩ : ℤ[ω])
#eval (⟨-4, 0⟩ : ℤ[ω])
#eval (⟨0, -5⟩ : ℤ[ω])
#eval (⟨3, -5⟩ : ℤ[ω])

/-
To make `ℤ[ω]` into a ring, we need to define addition and
multiplication operations, as well as zero and one elements.
Lean also requires some other operations, such as ways
to coerce a natural number or integer into EisensteinInt.
-/
def zero  : ℤ[ω] := ⟨0, 0⟩
def one   : ℤ[ω] := ⟨1, 0⟩
def ω     : ℤ[ω] := ⟨0, 1⟩
def add (a b : ℤ[ω]) : ℤ[ω] := sorry
def neg (a : ℤ[ω]) : ℤ[ω]   := sorry
def mul (a b : ℤ[ω]) : ℤ[ω] := sorry
/- Note that `ω^2 = -ω-1`, so multiplication should be given by the formula
  `(a.x + a.y*ω) * (b.x + b.y*ω) = (a.x*b.x - a.y*b.y) + (a.x*b.y + a.y*b.x -a.y*b.y) * ω`.
-/



/--
We now package all of this information together to
tell lean that `EisensteinInt` is a commutative ring.
-/
instance : CommRing ℤ[ω] := sorry

/-
We can now use lean as a calculator in the ring `EisensteinInt`.
-/
-- #eval ω ^ 3
-- #eval ω ^ 2 + ω + 1
-- #eval (ω^2+45)^24 + (ω+45)^24

----------------------------------------
open Complex Int
noncomputable section


@[reducible]
def rt3 : ℝ := Real.sqrt 3

@[simp]
theorem rt3_sq : rt3 ^ 2 = 3 := sorry

@[simp]
theorem sqrt3_inv_mul_self : rt3⁻¹ * rt3 = 1 := sorry

def complex_ω : ℂ := ⟨-1 / 2, rt3 / 2⟩

@[simp]
theorem complex_ω_sq : complex_ω ^ 2 = -complex_ω - 1 := sorry

def inclusion : ℤ[ω] →+* ℂ where
  toFun a   := a.x + a.y * complex_ω
  map_one'  := sorry
  map_mul'  := sorry
  map_zero' := sorry
  map_add'  := sorry

notation3 "ι" => inclusion
instance : Coe ℤ[ω] ℂ := ⟨ι⟩


/-
State and prove some useful formulae for working with Eisenstein integers as complex numbers.
For example give a gormula for `ι z` in terms of `z.x` and `z.y`, and formulae for `z.x` and `z.y`
in terms of the real and imaginary parts of `ι z`.
Also prove that `ι z = 0` if and only if `z = 0`.
-/

/--
The `ℤ`-valued norm of an Eisenstein integer.
-/
def Norm (z : ℤ[ω]) : ℤ := z.x^2 - z.x*z.y + z.y^2
def natNorm (z : ℤ[ω]) := natAbs (Norm z)

theorem normSq_coe {a : ℤ[ω]}: normSq a = Norm a := sorry

theorem natNorm_coe : normSq (a : ℤ[ω]) = natNorm a := sorry

/-
Prove that the norm is multiplicative, i.e., that `Norm (a * b) = Norm a * Norm b`.
Also prove the corresponding result for `natNorm`.
Finally, prove that `natNorm a = 0` if and only if `a = 0`.
-/

/--
On of the nearest Eisenstein integers to a given complex number `z`.
To define this, we round the imaginary part of `z` scaled by `2/√3` to get the `y`-coordinate,
and then round the real part of `z` shifted by `y/2` to get the `x`-coordinate.
-/
def nearest_EisInt (z : ℂ) : ℤ[ω] :=
  let y := round (2 * rt3⁻¹ * z.im)
  ⟨round (z.re + 2⁻¹ * y), y⟩

/-
Prove for a real number `x` that `(x - round x)^2 ≤ (1/2)^2`.
Using this, prove that for a real number `x` and a positive real number `c`, we have
`|x - c * round (c⁻¹ * x)| ≤ (1/2) * c`.

Then use these results to prove the following bounds on the real and imaginary parts
of the difference between a complex number `z` and the nearest Eisenstein integer to `z
-/

theorem im_sub_nearest (z : ℂ) : (z - nearest_EisInt z).im ^ 2 ≤ (4⁻¹ * rt3) ^ 2 := sorry

theorem re_sub_nearest (z : ℂ) : (z - nearest_EisInt z).re ^ 2 ≤ 2⁻¹ ^ 2 := sorry

theorem norm_sub_nearest_EisInt_self_lt (z : ℂ) : normSq (z - nearest_EisInt z) < 1 := sorry


/--
Define division with remainder in `ℤ[ω]` using the nearest Eisenstein integer function.
-/
def div (a b : ℤ[ω]) : ℤ[ω] := nearest_EisInt (a / b)
instance : Div EisensteinInt where div := div

/--
Define the modulus operation in `ℤ[ω]` using the division with remainder.
-/
def mod (a b : ℤ[ω]) : ℤ[ω] := a - b * a / b
instance : Mod EisensteinInt where mod := mod

/-
Prove that for all `a b : ℤ[ω]` with `b ≠ 0`, we have
`a = b * (a / b) + (a % b)`, and that `natNorm (a % b) < natNorm b`.
Next, prove that for all `a b : ℤ[ω]` with `b ≠ 0`, we have `natNorm a ≤ natNorm (a * b)`.
Finally, use these results to show that `ℤ[ω]` is a Euclidean Domain.
-/

instance : EuclideanDomain ℤ[ω] := sorry

-- Here is Bezout's theorem for Eucludean Domains
#check EuclideanDomain.gcd_eq_gcd_ab

-- Alternatively, we can prove it ourselves (by strong induction on the norm of `b`).
open Classical
theorem Bezout (a b : ℤ[ω]) : ∃ h k : ℤ[ω], h * a + k * b = EuclideanDomain.gcd a b := by
  sorry

end section
