import Mathlib.Tactic --# do not change this line.
namespace Galois
variable (F : Type) [Field F]

/--
`Gal F` is the group of automorphims of a field `F`.
-/
def Gal := F ≃+* F

instance : CoeFun (Gal F) (fun _↦ (F → F)) where
  coe σ := σ.toFun

@[ext]
lemma ext (σ τ : Gal F) (h : ∀ x : F, σ x = τ x) : σ = τ :=
by
  sorry

/-
Prove that `Gal F` is a group.
-/
instance (F : Type) [Field F] : Group (Gal F) := inferInstanceAs (Group (F ≃+* F))

/-
Prove that `Gal ℚ` is trivial.
-/
theorem Gal_rat (σ : Gal ℚ) : σ = 1 := sorry

/-
Prove that `Gal ℝ` is trivial.
-/
theorem Gal_real (σ : Gal ℝ) : σ = 1 := sorry

/-
Define Complex conjugation.
-/
def conj : Gal ℂ := sorry

/-
Show that complex conjugation is a non-trivial element
of `Gal ℂ`.
-/
lemma conj_ne_one : conj ≠ 1 := by
  sorry

/-
Define what it means for an element of `Gal ℂ` to be continuous.
-/
def cts (f : Gal ℂ) : Prop := sorry

/-
Prove that every continuous element of `Gal ℂ` is either the identity element or complex conjugation.
-/
lemma cts_gal_complex (σ : Gal ℂ) (h : cts σ) : σ = 1 ∨ σ = conj :=
  sorry
  /-
  first show that `σ i = s * i`, where `s = ±1`.
  Next show that if `x` and `y` are rational then `σ (x+i*y)= x + s * i * y`.
  Next, use continuity to prove the result.
  -/


/-
There is a field `𝔽₄` with `4` elements.
The elements are `x + y * c` with `x y : ZMod 2`; multiplication is defined by setting `c^2 = c + 1`.
-/
structure 𝔽₄ where
  x : ZMod 2
  y : ZMod 2

def c : 𝔽₄ := ⟨0,1⟩

instance : Zero 𝔽₄ := ⟨0,0⟩
instance : One 𝔽₄ := ⟨1,0⟩
instance : Add 𝔽₄ := ⟨fun a b ↦ ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Neg 𝔽₄ := ⟨id⟩
instance : Mul 𝔽₄ := ⟨fun a b ↦ ⟨a.x * b.x + a.y * b.y, a.x * b.y + a.y * b.x + a.y * b.y⟩⟩
instance : Inv 𝔽₄ := ⟨fun a ↦ ⟨a.x + a.y, a.y⟩⟩

instance : Field 𝔽₄ := sorry

/-
Show that the function `x ↦ x ^ 2` is an element of the Galois group.
-/
def σ : Gal 𝔽₄ := sorry


/-
Prove that the Galois group of `𝔽₄` has only two elements `1` and `σ`, and prove that `σ ≠ 1`.
-/
