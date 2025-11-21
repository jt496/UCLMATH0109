import Mathlib.Tactic --# do not change this line.
namespace Galois
variable (F : Type) [Field F]

/--
`Gal F` is the group of automorphims of a field `F`.
-/
notation3 "Gal "  F => (F ≃+* F)

/-
Prove that `Gal ℚ` is trivial.
-/
theorem Gal_rat : Subsingleton (Gal ℚ) := sorry

/-
# Prove that `Gal ℝ` is trivial.
-/

/-
Define Complex conjugation.
-/
def conj : Gal ℂ := sorry

/-
# Show that complex conjugation is a non-trivial element of `Gal ℂ`.
-/

/-
Define what it means for an element of `Gal ℂ` to be continuous.
-/
def Cts (f : Gal ℂ) : Prop := sorry

/-
Prove that every continuous element of `Gal ℂ` is either the identity element or complex conjugation.
-/
lemma cts_gal_complex (σ : Gal ℂ) (h : Cts σ) : σ = 1 ∨ σ = conj :=
  sorry
  /-
  first show that `σ i = s * i`, where `s = ±1`.
  Next show that if `x` and `y` are rational then `σ (x+i*y)= x + s * i * y`.
  Next, use continuity to prove the result.
  -/


/-
There is a field `𝔽₄` with `4` elements.
The elements are `x + y * c` with `x y : ZMod 2`; multiplication is defined by setting `c ^ 2 = c + 1`.
-/
structure 𝔽₄ where
  x : ZMod 2
  y : ZMod 2

def c : 𝔽₄ := ⟨0,1⟩

instance : Field 𝔽₄ := sorry

/-
Show that the function `x ↦ x ^ 2` is an element of the Galois group.
-/
def σ : Gal 𝔽₄ := sorry


/-
Prove that `Gal 𝔽₄` has only two elements `1` and `σ`, and prove that `σ ≠ 1`.

More generally, prove that the Galois group of `𝔽_{p^n}` has `n` elements.

Calculate the Galois groups of the fields `ℚ(√2)`, `ℚ(√[3]{2})` and `ℚ(ω)`, where `ω` is a primitive cube root of unity.

-/
