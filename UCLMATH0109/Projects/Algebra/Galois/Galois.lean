/-
Let `𝔽` be a field. Define the group of field automorphisms of `𝔽` as a structure.
Do some calculations with this:

Prove that the group is trivial for the fields `ℚ` and `ℝ` but not trivial for the field `ℂ`.

Prove that there are exactly two continuous automorphisms of the complex numbers.
-/
import Mathlib.Tactic --# do not change this line.

variable (F : Type) [Field F]
def Gal := F ≃+* F


@[ext]
lemma ext (σ τ : Gal F) (h : ∀ x : F, σ.toFun x = τ.toFun x) : σ = τ :=
by
  sorry

instance : CoeFun (Gal F) fun _ ↦ (F → F) where
  coe σ := σ.toFun

/-
define the composition of two elements of the Galois group.
-/
def comp (σ τ : Gal F) : Gal F  := sorry

/-
Define the inverse of an element of the Galois group.
-/
def inv (σ : Gal F) : Gal F := sorry

/-
Define the identity element in the Galois group.
-/
def one : Gal F := sorry

/-
Prove that `Gal F` is a group.
-/
instance (F : Type) [Field F] : Group <| Gal F  := sorry

/-
Prove that `Gal ℚ` is trivial.
-/
lemma Gal_rat (σ : Gal ℚ) : σ = 1 := sorry

/-
Prove that `Gal ℝ` is trivial.
-/
lemma Gal_real (σ : Gal ℝ) : σ = 1 := sorry

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
def cts (f : ℂ → ℂ) : Prop := sorry

/-
Prove that every continuous element of `Gal ℂ` is either the identity element or complex conjugation.
-/
lemma cts_gal_complex (σ : Gal ℂ) (h : cts σ) : σ = 1 ∨ σ = conj :=
  sorry
  /-
  first show that σ i = s * i, where s = ±1 .
  Next show that if x and y are rational then σ (x+i*y)= x + s * i * y.
  Next, use continuity to prove the result.
  -/

/-
Next give some examples of your own.
For example, you could try proving that if `F` is a field with `p^n` elements,
where `p` is prime, then the map `x ↦ x^p` is a field automorphism, and that
this element generates the group of all field automorphisms.
-/
