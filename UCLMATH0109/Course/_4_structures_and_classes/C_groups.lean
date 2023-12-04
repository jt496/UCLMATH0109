import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-
In the previous file, the notion of a group was defined from scratch.
Of course, groups are already defined in Mathlib, and many theorems
about groups are in Mathlib. We have imported some of these in the first
line of this file. From now on, we'll work with the Mathlib definition of
a group.
-/

/-Let `G` and `H` be a groups.-/
variable {G H : Type} [Group G] [Group H]

-- first find the group axioms, using `exact?`
example (x y z : G) : (x * y) * z = x * (y * z) :=
by
  exact mul_assoc x y z

example (x : G) : 1 * x = x :=
by
  exact one_mul x

example (x : G) : x * 1 = x :=
by
  exact mul_one x

example (x : G) : x * x⁻¹ = 1 :=
by
  exact mul_inv_self x

example (x : G): x⁻¹ * x = 1 :=
by
  exact mul_left_inv x

/-
Many simple consequences of the axioms can also be
found by `exact?`. For example:
-/
example (x : G) : (x⁻¹)⁻¹ = x :=
by
  exact inv_inv x


example (x : G) (h: x * y = 1) : y = x⁻¹ :=
by
  exact eq_inv_of_mul_eq_one_right h

-- For the next example, you could use a `have` statement
-- to obtain the previous example as an intermediate step.
example (x y : G) (h : x * y = 1) : y * x = 1 :=
by
  have : y = x⁻¹
  · exact eq_inv_of_mul_eq_one_right h
  rw [this]
  exact mul_left_inv x

--To prove a complicated equation which is true in any group
--(with no other hypotheses than the group axioms),
--you can use the high level tactic `group`. For example,
example (x y : G) : x*y*x⁻¹*y^2*y⁻¹^2*x*y⁻¹*x^2 = x^3 :=
by
  group

example (x : G) : (x ^ n)⁻¹ = x⁻¹ ^ n :=
by
  group

-- note that `group` does not use hypotheses,
-- so it cannot solve the following. Instead,
-- you can use the `rw` tactic.
example (x y : G) (h: x = y) : x ^ 2 = y ^ 2 :=
by
  rw [h]



#check Subgroup G
/-
In lean, `Subgroup G` is a `Type`, defined as a structure with fields
  `carrier` - a subset of `G` (the elements of the subgroup).
  `mul_mem'` a proof that if `g` and `h` are in `carrier` then so is `g * h`,
  `one_mem'` a proof that `1` is in `carrier`,
  `inv_mem'` a proof that if `g ∈ carrier` then `g⁻¹ ∈ carrier`.
-/

open Set
/-
Show that `{1}` is a subgroup of `G`
-/
def Trivial_subgroup : Subgroup G where
  carrier := {1}
  mul_mem' := by
    intro a b ha hb
    rw [mem_singleton_iff] at *
    rw [ha, hb, one_mul]
  one_mem' := rfl
  inv_mem' := by
    intro a ha
    dsimp at ha ⊢
    rw [mem_singleton_iff] at *
    rw [ha, inv_one]

/-
If `G` and `H` are groups, then `G →* H` is the `Type` of group
homomorphisms from `G` to `H`.
This is a `structure` with fields:
  `toFun` a function `G → H`,
  `map_mul'` a proof that `toFun (g * g') = toFun g * toFun g'`,
  `map_one'` a proof that `toFun 1 = 1`,
-/
#check G →* H
-- Find some standard properties of group homomorphisms in Mathlib.

example (φ : G →* H) : φ (g * h) = φ g * φ h :=
by
  exact MonoidHom.map_mul φ g h

example (φ : G →* H) : φ g⁻¹ = (φ g)⁻¹ :=
by
  exact MonoidHom.map_inv φ g

example (φ : G →* H) : φ (g ^ n) = (φ g) ^ n :=
by
  exact MonoidHom.map_pow φ g n


/-
Show that the function taking every element of `G` to `1 : H` is
a homomorphism.
-/
def trivial_hom : G →* H where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := by
    intro x y
    dsimp
    exact self_eq_mul_left.mpr rfl

/-
Show that the identity is a homomorphism.
-/
def id_hom : G →* G where
  toFun := id
  map_one' := rfl
  map_mul' := by
    tauto
/-
Show that the image of a homomorphism is a subgroup.
The image of a function `f : X → Y` is `Set.range f`.
-/
def Im (φ : G →* H): Subgroup H where
  carrier := range φ
  mul_mem' := by
    intro a b ha hb
    rw [mem_range] at *
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    use x*y
    rw [map_mul, hx, hy]
  one_mem' := by
    dsimp
    use 1
    exact MonoidHom.map_one φ
  inv_mem' := by
    intro x hx
    dsimp at *
    obtain ⟨a , ha⟩ := hx
    use a⁻¹
    rw [map_inv, ha]
