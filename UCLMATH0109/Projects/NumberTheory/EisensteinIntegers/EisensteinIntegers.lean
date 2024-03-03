import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.EuclideanDomain.Basic

/-- An Eisenstein integer is a number of the form `x+y*ω`, where `ω = e^(2*π*i/3)`
and `x y :ℤ`.
We shall write `EisensteinInt` for the Type of Eisenstein integers, with an Eisenstein
integer represented by its x- and y-coordinates.
-/
@[ext]
structure EisensteinInt : Type where
  x : ℤ
  y : ℤ

namespace EisensteinInt
scoped notation "ℤ[ω]" => EisensteinInt

/-- We give lean a way of displaying elements of `ℤ[ω]` using the command `#eval`.
TO DO : rewrite this using pattern matching.
-/
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



/-- We now package all of this information together to
tell lean that `EisensteinInt` is a ring.
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

@[reducible]
noncomputable def rt3 : ℝ := Real.sqrt 3

@[simp]
theorem rt3_sq : rt3 ^ 2 = 3 := sorry

@[simp]
theorem sqrt3_inv_mul_self : rt3⁻¹ * rt3 = 1 := sorry

noncomputable def complex_ω : ℂ := ⟨-1 / 2, rt3 / 2⟩

@[simp]
theorem complex_ω_sq : complex_ω ^ 2 = -complex_ω - 1 := sorry

noncomputable def to_ℂ (a : ℤ[ω]) : ℂ := a.x + a.y * complex_ω


noncomputable def inclusion : ℤ[ω] →+* ℂ where
  toFun     := to_ℂ
  map_one'  := sorry
  map_mul'  := sorry
  map_zero' := sorry
  map_add'  := sorry

local notation "ι" => inclusion

noncomputable instance : Coe ℤ[ω] ℂ where
  coe := ι

lemma coe_eq : ι z = ⟨z.x - z.y / 2, z.y * rt3 / 2 ⟩ := sorry

theorem y_from_coe {a : ℤ[ω]} : (a.y : ℝ) = 2 * rt3⁻¹ * (a : ℂ).im := sorry

theorem x_from_coe {a : ℤ[ω]} : (a.x : ℝ) = (a : ℂ).re + rt3⁻¹ * (a : ℂ).im := sorry

theorem coe_eq_zero {z : ℤ[ω]} : (z : ℂ) = 0 ↔ z = 0 := sorry

/-- This is the `ℤ`-valued norm of an Eisenstein integer.
-/
def Norm (z : ℤ[ω]) : ℤ := z.x^2 - z.x*z.y + z.y^2

theorem normSq_coe {a : ℤ[ω]}: normSq a = Norm a := sorry

def natNorm : ℤ[ω] → ℕ := λ z ↦ natAbs (Norm z)

theorem natNorm_coe : normSq (a : ℤ[ω]) = natNorm a := sorry

theorem norm_mul : Norm (a * b) = Norm a * Norm b := sorry

theorem natNorm_mul : natNorm (a * b) = natNorm a * natNorm b := sorry

theorem natNorm_eq_zero_iff : natNorm a = 0 ↔ a = 0 := sorry

noncomputable def nearest_EisInt (z : ℂ) : ℤ[ω] :=
  let y := round (2 * rt3⁻¹ * z.im)
  { x := round (z.re + 2⁻¹ * y)
    y := y }

theorem self_sub_round_sq (x : ℝ) : (x - round x) ^ 2 ≤ 2⁻¹ ^ 2 := sorry

/-- We will use this in the case `c = √3/2`.
-/
theorem sub_mul_round {c : ℝ} (x : ℝ) (c_pos : c > 0) : |x - c * round (c⁻¹ * x)| ≤ 2⁻¹ * c := sorry

theorem im_sub_nearest (z): (z - nearest_EisInt z).im ^ 2 ≤ (4⁻¹ * rt3) ^ 2 := sorry

theorem re_sub_nearest (z) : (z - nearest_EisInt z).re ^ 2 ≤ 2⁻¹ ^ 2 := sorry

theorem norm_sub_nearest_EisInt_self_lt (z): normSq (z - nearest_EisInt z) < 1 := sorry

noncomputable def div (a b : ℤ[ω]) : ℤ[ω] := nearest_EisInt (a / b)

noncomputable def mod (a b : ℤ[ω]) : ℤ[ω] := a - b * div a b

noncomputable instance hasModEisensteinInt : Mod EisensteinInt where mod := mod

noncomputable instance hasDivEisensteinInt : Div EisensteinInt where div := div

theorem div_add_mod (a b): (b * (a / b) + a % b : ℤ[ω]) = a := sorry

theorem norm_sq_mod_lt (a b) (h : b ≠ 0) : natNorm (mod a b) < natNorm b :=sorry

theorem my_quotient_zero (a): div a 0 = 0 := sorry

theorem my_mul_left_not_lt (a b) (hb : b ≠ 0) : ¬natNorm (a * b) < natNorm a := sorry

noncomputable instance : EuclideanDomain ℤ[ω] := sorry

open EuclideanDomain

-- Here is Bezout's theorem for Eucludean Domains
#check EuclideanDomain.gcd_eq_gcd_ab

-- Alternatively, we can prove it ourselves.
open Classical
theorem Bezout (a b : ℤ[ω]) : ∃ h k : ℤ[ω], h * a + k * b = EuclideanDomain.gcd a b :=
by
  sorry

end EisensteinInt
