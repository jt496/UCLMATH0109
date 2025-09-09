import Mathlib.Tactic

noncomputable section

class VectorSpace (V : Type) extends Zero V, Neg V, Add V, SMul ℝ V where
  add_zero (v : V)              : v + 0 = v
  neg_add_self (v : V)          : -v + v = 0
  add_comm (v w : V)            : v + w = w + v
  add_assoc (u v w : V)         : (u + v) + w = u + (v + w)
  smul_assoc (a b : ℝ) (v : V)  : a • (b • v) = (a * b) • v
  one_smul (v : V)              : (1 : ℝ) • v = v
  smul_add (a : ℝ) (v w : V)    : a • (v + w) = a • v + a • w
  add_smul (a b : ℝ) (v : V)    : (a + b) • v = a • v + b • v

namespace VectorSpace

section Simple_lemmas

variable {V : Type} [VectorSpace V] (u v w : V)
/-
Prove a few simple statements about abstract vector spaces.
-/

-- #01
lemma add_neg_self : v + -v = 0 :=
by
  sorry

-- #02
lemma zero_add : 0 + v = v :=
by
  sorry

-- #03
lemma eq_neg_of_add_eq_zero (h : v + w = 0) : w = -v :=
by
  sorry


-- #04
lemma add_left_cancel (h : v + w = w) : v = 0 :=
by
  have h2: v = v + w + - w
  · sorry
  sorry

-- #05
lemma zero_smul : (0:ℝ) • v = 0 :=
by
  sorry

-- #06
lemma neg_one_smul : (-1:ℝ) • v = -v :=
by
  sorry

end Simple_lemmas


section Linear_maps

variable (U V W : Type) [VectorSpace U] [VectorSpace V] [VectorSpace W]

structure LinearMap where
  toFun : V → W
  map_add (v w : V) : toFun (v + w) = toFun v + toFun w
  map_smul (x : ℝ) (v : V) : toFun (x • v) = x • toFun v

instance : CoeFun (LinearMap V W) (fun _ ↦ V → W) where
  coe := LinearMap.toFun

lemma map_add (T : LinearMap V W) (v w : V) : T (v + w) = T v + T w :=
  LinearMap.map_add _ _ _

lemma map_smul (T : LinearMap V W) (x : ℝ) (v : V) : T (x • v) = x • T v :=
  LinearMap.map_smul _ _ _


--#07
lemma map_zero (T : LinearMap V W) : T 0 = 0 :=
by
  sorry

--#08
lemma map_neg (T : LinearMap V W) (v : V) : T (-v) = -T v :=
by
  sorry

--#09
def comp (T₁ : LinearMap V W) (T₂ : LinearMap U V) : LinearMap U W where
  toFun := T₁ ∘ T₂
  map_add :=
  by
    intro v w
    dsimp -- without the obvious `rw` won't work
    sorry
  map_smul :=
  by
    sorry

end Linear_maps



/-
Now let's create an instance of a `VectorSpace`
-/

/-
Make `SpaceTime` into a vector space over the real numbers,
with appropriate definitions of addition, scalar multiplication etc.
-/
@[ext]
structure SpaceTime where
  x : ℝ
  y : ℝ
  z : ℝ
  t : ℝ

namespace SpaceTime

--#10 Fill in the definitions of addition, negation and scalar multiplication.
def zero : SpaceTime := ⟨0,0,0,0⟩
def add (P Q: SpaceTime) : SpaceTime := sorry
def neg (P : SpaceTime) : SpaceTime := sorry
def smul (a : ℝ) (P : SpaceTime) : SpaceTime := sorry

--#11 Create instances of the classes `Zero`, `Add`, `Neg` and `SMul`.
instance : Zero SpaceTime := sorry
instance : Add SpaceTime := sorry
instance : Neg SpaceTime := sorry
instance : SMul ℝ SpaceTime := sorry


--#12 State and prove some definitional lemmas.
lemma zero_def : (0 : SpaceTime) = ⟨0,0,0,0⟩ := sorry
lemma add_def (P Q : SpaceTime) : P + Q = sorry := sorry
lemma neg_def (P : SpaceTime) : -P = sorry := sorry
lemma smul_def (a : ℝ) (P : SpaceTime) : a • P = sorry := sorry



--#13 Show that `SpaceTime` is a vector space over the real numbers.
-- Use the definitional lemmas we have just proved, along with `ext`.
instance : VectorSpace SpaceTime := sorry

end SpaceTime
end VectorSpace
