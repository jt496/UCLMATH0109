import Mathlib

section MultiFun

open LinearMap

/-
These questions are on vector spaces and linear maps over the real numbers.
The statement that `V` is a vector space over `ℝ` involves two class instances:

  `AddCommGroup V` and `Module ℝ V`.

If `v` is in a vector space and `x` is a real number, then scalar multiplication of `v`
by `x` is written `x • v` (not `x * v`).

If `V` and `W` are vector spaces over `ℝ`, then the `Type` of linear maps from `V` to `W`
is written `V →ₗ[ℝ] W`. This is a structure with fields `toFun` (the actual function from `V` to `W`),
`map_add'` and `map_smul'` which are proofs that the function is compatible with addition and scalar multiplication.

The next two lines of code say that `U`, `V` and `W` are vector spaces over `ℝ`.
-/

variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module ℝ U] [Module ℝ V] [Module ℝ W]

/--
The questions will also involve a set `X` (in fact a `Type`).
We *could* take `X` to be any non-empty `Type`. We've choosen `X` to be `Fin 100`.
If you change to it to `ℕ` or `ℝ`, then your code will probably still run with no problems.
-/
notation "X" => Fin 100

/-
Mathlib also knows that if `V` is a vector space, then the set of functions `X → V` is also an vector space,
where the addition and scalar multiplication operations on `X → V` are pointwise addition and scalar multiplication of functions.
The following line checks this.
-/
#synth Module ℝ (X → V)

-- # 1
/--
Construct a linear map from `V` to the vector space of functions `X → V`.
The linear map should take `v : V` to the constant function on `X` with value `v`.
-/
def const : V →ₗ[ℝ] (X → V) where
  toFun     := Function.const X
  map_add'  := by sorry
  map_smul' := by sorry

-- # 2
/--
Given a linear map `φ : A →ₗ[ℝ] B`, we define another linear map
`lift φ : (X → A) →ₗ[ℝ] (X → B)`, which takes a function `f : X → A` to `φ ∘ f : X → B`.

In fact the map `lift : (A →ₗ[ℝ] B) → ((X → A) →ₗ[ℝ] (X → B))` is also a linear map.
-/
def lift : (V →ₗ[ℝ] W) →ₗ[ℝ] ((X → V) →ₗ[ℝ] (X → W)) where
  toFun φ := {
    toFun := fun f ↦ φ ∘ f
    map_add' := by
      sorry
    map_smul' := by
      sorry
  }
  map_add' := by
    sorry
  map_smul' := by
    sorry

/-
Here are two very easy lemmas about `lift` and `const`.
Note that if `φ` and `ψ` are two linear maps, then their composition (as a linear map) is written `φ.comp ψ`.
-/

-- # 3
lemma lift_comp_lift (φ : U →ₗ[ℝ] V) (ψ : V →ₗ[ℝ] W) :
    (lift ψ).comp (lift φ) = lift (ψ.comp φ) := sorry

-- # 4
lemma lift_comp_const (φ : V →ₗ[ℝ] W) : (lift φ).comp const = const.comp φ := sorry

/--
`MultiFun X n` is the type of functions of several variables in `X`, with values in `ℝ`.
For example `MultiFun X 1` is `X → ℝ` and `MultiFun X 2` is `X → X → ℝ`, etc.
`MultiFun X 0` is defined to be `ℝ`.
-/
def MultiFun : ℕ → Type
| 0 => ℝ
| n + 1 => X → MultiFun n

notation "V_[" n "]" => MultiFun n

/-
Here are some definitional lemmas for `MultiFun`.
-/

lemma MultiFun_zero : V_[0] = ℝ := rfl

lemma MultiFun_succ : V_[n+1] = (X → V_[n]) := rfl

@[ext] lemma MultiFun.ext {f g : V_[n + 1]} (h : ∀ x, f x = g x) : f = g := funext h

/-
The next few lines of code show lean that `MultiFun n` is a vector space over `ℝ` for each natural number `n`.
-/
instance (n : ℕ) : AddCommGroup V_[n] :=
by
  induction n
  · exact inferInstanceAs (AddCommGroup ℝ)
  · exact inferInstanceAs (AddCommGroup (X → _))

noncomputable instance (n : ℕ) : Module ℝ V_[n] :=
by
  induction n
  · exact inferInstanceAs (Module ℝ ℝ)
  · exact inferInstanceAs (Module ℝ (X → _))

/--
We now define recursively a sequence `d` of linear maps `MultiFun n →ₗ[ℝ] MultiFun (n + 1)`.

  `MultiFun 0   →ₗ[ℝ]   MultiFun 1   →ₗ[ℝ]   MultiFun 2   →ₗ[ℝ]   MultiFun 3   →ₗ[ℝ] ...`

Remember that by definition of `MultiFun`, these are linear maps

  `ℝ    →ₗ[ℝ]   (X → ℝ)   →ₗ[ℝ]   (X → X → ℝ)   →ₗ[ℝ]   (X → X → X → ℝ)   →ₗ[ℝ] ...`.

These linear maps are defined as follows; you might want to think a little about this definition.
-/
def d : ∀ n, V_[n] →ₗ[ℝ] V_[n+1]
| 0     => const
| n + 1 => const - lift (d n)

/--
We shall use the notation `∂[n]` for the linear map `d n : MultiFun n →+ MultiFun (n + 1)`.
If `n` is implicit in the context, then we can write `∂` instead of `∂[n]`.
-/
notation "∂[" n "]" => d n
notation "∂" => d _

/-
Here are some definitional lemmas about the linear maps `d`.
-/
lemma d_zero : ∂[0] = const := rfl

lemma d_zero_apply (f : MultiFun 0) : ∂ f x = f := rfl

lemma d_succ : ∂[n + 1] = const - lift (d n) := rfl

-- # 5
lemma d_succ_apply (f : V_[n+1]) : ∂ f x = f - ∂ (f x) := sorry

-- # 6
lemma d_one_apply (f : V_[1]) : ∂ f x₀ x₁ = f x₁ - f x₀ := by
  sorry

-- # 7
-- you might find the following lemma from Mathlib useful:
#check Pi.sub_apply

lemma d_two_apply (f : V_[2]) : ∂ f x₀ x₁ x₂ = f x₁ x₂ - f x₀ x₂ + f x₀ x₁ := by
  sorry

-- # 8
/-
# To show that you understand the pattern here, state and prove the obvious lemma `d_three_apply`.
-/



-- #         STATE AND PROVE YOUR THEOREM HERE.



-- # 9
/-
You will probably need to prove the next lemma by induction on `n`,
and you might want to write the proof down on paper before you begin.
The proof is not long using the lemms `lift_comp_lift` and `lift_comp_const` proved above.

You might find the following lemmas from Mathlib useful:
-/
#check sub_comp
#check comp_sub
#check map_zero

lemma d_comp_d : ∂.comp ∂[n] = 0 := by
  sorry

#check mem_ker
-- # 10
lemma mem_ker_d (f : MultiFun (n + 1)) :
    f ∈ ker ∂ ↔ ∀ x, ∂ (f x) = f := by
  sorry

#check comp_apply
-- # 11
/-
Prove that the image of the linear map `∂ : MultiFun n →ₗ[ℝ] MultiFun (n + 1)` is
the same as the kernel of the next linear map `∂ : MultiFun (n + 1) →ₗ[ℝ] MultiFun (n + 2)`.
This should be faiirly easy using the lemmas `d_comp_d` and `mem_ker_d` above.
-/
theorem exact_d : range ∂[n] = ker ∂[n+1] := by
  sorry

end MultiFun
