import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

--## WORK IN PROGRESS
/-
In the previous file, the notion of a group was defined from scratch.
Of course, groups are already defined in Mathlib, and many theorems
about groups are already there. We have imported some of these in the first
line of this file. From now on, we'll work with the Mathlib definition of
a group.
-/

/-Let `G` be a group.-/
variable {G H : Type} [Group G] [Group H]

-- first find the group axioms, using `exact?`
example (x y z : G) : (x * y) * z = x * (y * z) :=
by
  -- exact?
  sorry

example (x : G) : 1 * x = x :=
by
  sorry

example (x : G) : x * 1 = x :=
by
  sorry

example (x : G) : x * x⁻¹ = 1 :=
by
  sorry

example (x : G): x⁻¹ * x = 1 :=
by
  sorry

/-
Many simple consequences of the axioms can also be
found by `exact?`. For example:
-/
example (x : G) : (x⁻¹)⁻¹ = x :=
by
  sorry


example (x : G) (h: x * y = 1) : y = x⁻¹ :=
by
  sorry

-- For the next example, you could use a "have" statement
-- to obtain the previous example as an intermediate step.
example (x y : G) (h : x * y = 1) : y * x = 1 :=
by
  sorry

--to prove a complicated equation which is true in any group
--(with no other hypotheses than the group axioms),
--you can use the high level tactic `group`. For example,
example (x y : G) : x*y*x⁻¹*y^2*y⁻¹^2*x*y⁻¹*x^2 = x^3 :=
by
  sorry

example (x : G) : (x ^ n)⁻¹ = x⁻¹ ^ n :=
by
  sorry

-- note that `group` does not use hypotheses,
-- so it cannot solve the following. Instead,
-- you can use the `rw` tactic.
example (x y : G) (h: x = y) : x ^ 2 = y ^ 2 :=
by
  sorry


/-
If `G` and `H` are groups, then `G →* H` is the `Type` of group
homomorphisms from `G` to `H`.
This is a `structure` with fields:
  `toFun` a function `G → H`,
  `map_mul'` a proof that `toFun (g * g') = toFun g * toFun g'`,
  `map_one'` a proof that `toFun 1 = 1`,
-/

variable (φ : G →* H) -- `φ` is a homomorphism from `G` to `H`


-- Find some standard properties of group homomorphisms in Mathlib.

example : φ (g * h) = φ g * φ h :=
by
  sorry

example : φ g⁻¹ = (φ g)⁻¹ :=
by
  sorry

example : φ (g ^ n) = (φ g) ^ n :=
by
  sorry

/-
Show that the fucntion taking every element of `G` to `1 : H` is
a homomorphism.
-/
def trivial_hom : G →* H where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := by
    intros
    dsimp
    exact self_eq_mul_left.mpr rfl

/-
Show that the identity is a homomorphism.
-/
def id_hom : G →* G where
  toFun := id
  map_one' := by
    rfl
  map_mul' := by
    tauto



#check Subgroup G
/-
In lean, `Subgroup G` is a structure with fields
  `carrier` - a subset of `G`.
  `mul_mem'` a proof that if `g` and `h` are in `carrier` then so is `g*h`,
  `one_mem'` a proof that `1` is in `carrier`,
  `inv_mem'` a proof that if `g ∈ carrier` then `g⁻¹ ∈ carrier`.
-/

/-
Show that `{1}` is a subgroup of `G`
-/
def Trivial_subgroup : Subgroup G where
  carrier := {1}
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_singleton_iff] at *
    rw [ha, hb, one_mul]
  one_mem' := by
    dsimp
    rw [Set.mem_singleton_iff]
  inv_mem' := by
    intro x hx
    dsimp at *
    rw [Set.mem_singleton_iff] at *
    rw [hx, inv_one]

/-
Show that the image of a homomorphism is a subgroup.
-/
def Im (φ : G →* H): Subgroup H where
  carrier := {h : H | ∃ g : G, φ g = h}
  mul_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x*y
    rw [map_mul, hx, hy]
  one_mem' := by
    use 1
    exact map_one φ
  inv_mem' := sorry
