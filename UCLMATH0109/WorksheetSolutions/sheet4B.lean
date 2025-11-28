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
lemma add_neg_self : v + -v = 0 :=by
  rw [add_comm]
  exact neg_add_self _

-- #02
lemma zero_add : 0 + v = v :=by
  rw [add_comm]
  apply add_zero

#check zero_add

-- #03
lemma eq_neg_of_add_eq_zero (h : v + w = 0) : w = -v :=by
  rw [←add_zero (-v),← h ,← add_assoc,neg_add_self,zero_add]

-- #04
lemma add_left_cancel (h : v + w = w) : v = 0 :=by
  have h2: v = v + w + - w
  · rw [add_assoc,add_neg_self,add_zero]
  rw [h] at h2
  rwa [← add_neg_self w]

-- #05
lemma zero_smul : (0:ℝ) • v = 0 :=by
  have : ((0:ℝ) • v) + v = v
  · rw [← one_smul (v),smul_assoc,zero_mul,←add_smul]
    norm_num
  apply add_left_cancel _ _ this


-- #06
lemma neg_one_smul : (-1:ℝ) • v = -v :=by
  apply eq_neg_of_add_eq_zero
  rw [←one_smul v,smul_assoc,←add_smul]
  norm_num
  exact zero_smul _

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
lemma map_zero (T : LinearMap V W) : T 0 = 0 :=by
  rw [← zero_smul (0 : V), T.map_smul,zero_smul]

--#08
lemma map_neg (T : LinearMap V W) (v : V) : T (-v) = -T v :=by
  rw [← neg_one_smul (v) ]
  rw [T.map_smul,neg_one_smul]

--#09
def comp (T₁ : LinearMap V W) (T₂ : LinearMap U V) : LinearMap U W where
  toFun := T₁ ∘ T₂
  map_add :=by
    intro v w
    dsimp
    rw [T₂.map_add,T₁.map_add]
  map_smul :=by
    intro x v
    dsimp;
    rw [T₂.map_smul,T₁.map_smul]

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
def add (P Q: SpaceTime) : SpaceTime := ⟨P.x+Q.x, P.y+Q.y, P.z+ Q.z, P.t+ Q.t⟩
def neg (P : SpaceTime) : SpaceTime := ⟨-P.x,-P.y,-P.z,-P.t⟩
def smul (a : ℝ) (P : SpaceTime) : SpaceTime := ⟨a*P.x,a*P.y,a*P.z,a*P.t⟩

--#11 Create instances of the classes `Zero`, `Add`, `Neg` and `SMul`.
instance : Zero SpaceTime where
  zero := zero

instance : Add SpaceTime where
  add := add

instance : Neg SpaceTime where
  neg := neg

instance : SMul ℝ SpaceTime where
  smul := smul


--#12 State and prove some definitional lemmas.
lemma zero_def : (0 : SpaceTime) = ⟨0,0,0,0⟩ := rfl
lemma add_def (P Q : SpaceTime) : P + Q = ⟨P.x+Q.x, P.y+Q.y, P.z+ Q.z, P.t+ Q.t⟩ := rfl
lemma neg_def (P : SpaceTime) : -P = ⟨-P.x,-P.y,-P.z,-P.t⟩ := rfl
lemma smul_def (a : ℝ) (P : SpaceTime) : a • P = ⟨a*P.x,a*P.y,a*P.z,a*P.t⟩ := rfl



--#13 Show that `SpaceTime` is a vector space over the real numbers.
-- Use the definitional lemmas we have just proved, along with `ext`.
instance : VectorSpace SpaceTime where
  add_zero := by
    intro v
    rw [zero_def,add_def];
    dsimp
    ext; all_goals dsimp; apply _root_.add_zero
  neg_add_self :=by
    intro v
    rw [zero_def,add_def,neg_def]; dsimp;
    ext
    all_goals dsimp ; apply add_left_neg
  add_comm :=by
    intro v w
    rw [add_def,add_def]
    ext
    all_goals dsimp ; apply _root_.add_comm
  add_assoc :=by
    intro u v w
    rw [add_def,add_def,add_def]
    dsimp
    ext;
    all_goals dsimp ; apply _root_.add_assoc
  smul_assoc :=by
    intro a b v
    rw [smul_def,smul_def,smul_def,mul_assoc,mul_assoc,mul_assoc,mul_assoc]
  one_smul :=by
    intro v
    rw [smul_def,one_mul,one_mul,one_mul,one_mul]
  smul_add :=by
    intro a v w
    rw [smul_def,smul_def,smul_def,add_def,add_def,mul_add,mul_add,mul_add,mul_add]
  add_smul :=by
    intro a b v
    rw [smul_def,smul_def,smul_def,add_def,add_mul,add_mul,add_mul,add_mul]

end SpaceTime
end VectorSpace
