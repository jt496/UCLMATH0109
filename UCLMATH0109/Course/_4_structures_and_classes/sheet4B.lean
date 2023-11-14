import Mathlib.Tactic

noncomputable section

class VectorSpace (V : Type) extends AddCommGroup V, SMul ℝ V where
  smul_assoc (a b : ℝ) (v : V)  : a • (b • v) = (a * b) • v
  one_smul (v : V)              : (1 : ℝ) • v = v
  smul_add (a : ℝ) (v w : V)    : a • (v + w) = a • v + a • w
  add_smul (a b : ℝ) (v : V)    : (a + b) • v = a • v + b • v

namespace VectorSpace

/-
Prove a few simple statements about abstract vector spaces.
-/

lemma eq_neg_of_add_eq_zero (V : Type) [VectorSpace V]
    (v w : V) (h : v + w = 0) : w = -v :=
by
  sorry

lemma zero_smul (V : Type) [VectorSpace V] (v : V) :
    (0:ℝ) • v = 0 :=
by
  sorry

lemma neg_one_smul (V : Type) [VectorSpace V] (v : V) :
    (-1:ℝ) • v = -v :=
by
  sorry

/-
Now let's create an example of a `VectorSpace`
-/

instance : VectorSpace ℂ where
  smul_assoc := sorry
  one_smul := sorry
  smul_add := sorry
  add_smul := sorry

/-
The functions `S → ℝ` form an additive commutative group.
Lean already knows this, and it also has a definition of
scalar multiplication of a function `f : S → ℝ` by a real
number.

Show that `S → ℝ` is a vector space over the real numbers.
-/

instance (S : Type) : VectorSpace (S → ℝ) where
  smul_assoc := sorry
  one_smul := sorry
  smul_add := sorry
  add_smul := sorry

/-
Make `SpaceTime` into a vector space ove the real numbers,
with appropriate definitions of addition, scalar multiplication etc.
-/
structure SpaceTime where
  x : ℝ
  y : ℝ
  z : ℝ
  t : ℝ

namespace SpaceTime

def zero : SpaceTime := sorry
def add : SpaceTime → SpaceTime → SpaceTime := sorry
def neg : SpaceTime → SpaceTime := sorry
def smul : ℝ → SpaceTime → SpaceTime := sorry

instance : Zero SpaceTime := sorry
instance : Add SpaceTime := sorry
instance : Neg SpaceTime := sorry
instance : SMul ℝ SpaceTime := sorry

/-
Next, state and prove some definitional lemmas.
-/

/-
After that, show that `SpaceTime` is an additive commutative group.
-/

instance : AddCommGroup SpaceTime := sorry

/-
After that, show that `SpaceTime` is a vector space over the real numbers.
-/

instance : VectorSpace SpaceTime := sorry
