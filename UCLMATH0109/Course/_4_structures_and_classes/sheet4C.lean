import Mathlib.Tactic

variable {G H K : Type} [Group G] [Group H] [Group K]


/-
The first few exercises can be done by `exact?`.
-/

--01
example : (1 : G)⁻¹ = 1 :=
by
  sorry

--02
example (x y : G) : x^2 * x⁻¹ * y = x * y :=
  sorry

--03
example (x y : G) (h : y = x^2 * y⁻¹) : x^2 = y^2 :=
  sorry

--04
example (x y : G) (h : x * y = y * x) : (x * y)^2 = x^2 * y^2 :=
by
  sorry

--05
/-
Show that if `φ : G →* H` and `ψ : H →* K` are homomorphisms
then their composition is also a homomorphism:
-/
example (φ : G →* H) (ψ : H →* K) : G →* K where
  toFun := ψ ∘ φ
  map_one' := sorry
  map_mul' := sorry

--06
/-
Show that if `A` is an Abelian group then
the map `a ↦ a ^ 2` is a group homomorphism from `A` to `A`.
-/
example (A : Type) [CommGroup A] : A →* A where
  toFun     := fun a ↦ a ^ 2
  map_one'  := sorry
  map_mul'  := sorry

--07
/-
Show that if `A` is abelian, then the product of
two homomorphisms `G →* A` is a homomorphism.
-/
example {A : Type} [CommGroup A] (φ ψ : G →* A) : G →* A where
  toFun     := fun g ↦ (φ g) * (ψ g)
  map_one'  := sorry
  map_mul'  := sorry

--08
/-
Show that if `A` is abelian and `φ : G →* A` is a homomorphism,
then the map `g ↦ (φ g)⁻¹` is also a homomorphism.
-/
def homomorphism_inv {A : Type} [CommGroup A] (φ : G →* A) : G →* A where
  toFun     := fun g ↦ (φ g)⁻¹
  map_one'  := sorry
  map_mul'  := sorry

--09
/-
Prove that the set of all elements of `G` is a subgroup of `G`.
(Note that the set of all elements of a given `Type` is called `Set.univ`.)
-/
example : Subgroup G where
  carrier := Set.univ
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

--10
/-
Prove that the image of `f` is a subgroup of `H`
and the kernel is a subgroup of `G`.
-/
def Ker (φ : G →* H) : Subgroup G where
  carrier := {g : G | φ g = 1}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-
# The last few questions are more challenging.
-/

--11
/-
Have a think about this one. Of course you could prove it by a very
long sequence of rewrites. However it is easier to prove a more general
statement by induction.
Alternatively you could try `apply?`, and try to find the most relevant
result.
-/
example (x y : G) (h : x * y = y * x) : x^45 * y^4 = y^4 * x^45 :=
by
  sorry


--12
/-
Suppose `G` is a group in which `z ^ 2 = 1` for every element `z`.
Prove that `G` is abelian.
-/
example (h : ∀ z : G , z ^ 2 = 1) :
    ∀ x y : G, x * y = y * x :=
by
  -- first prove that `z⁻¹ = z` for all elements `z` in the group.
  -- Using this formula in the case `z = y * x`,
  -- we get `(y * x)⁻¹ = y * x`.
  -- Next, simplify the left hand side to get `x⁻¹ * y⁻¹ = y * x`.
  -- After that, rewrite `x⁻¹` and `y⁻¹` as `x` and `y`.
  sorry


--13
/-
We defined the kernel of a homomorphism in question 10.
Prove that a homomorphism `φ` is injective iff its kernel is `{1}`.

In this last example, you might want to use `Set.mem_singleton_iff`.
You might also want to look up `Function.Injective`.
-/
theorem injective_iff (φ : G →* H) :
    Function.Injective φ ↔ (Ker φ : Set G) = {1} :=
by
  sorry



--14
example (x y : G) (h : x * y = y^2 * x) (n : ℕ) : x^n * y = y ^ (2^n) * x^n :=
by
  sorry

--15
example {x y : G} (h : x * y = y⁻¹ * x) : x ^ (2 * n) * y = y * x^(2 * n) :=
by
  sorry
