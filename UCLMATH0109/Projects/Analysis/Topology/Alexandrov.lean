import Mathlib.Tactic
import Mathlib.Topology.Basic

open Set

/-
This project is on general topology. We explore some basic definitions such as discrete
and Alexandrov topologies with a focus on the kinds of topologies that arise in computer
science.

Recall that a topology τ on a set α is a family of subsets of α that contains ∅, univ
and is closed under pairwise intersections and arbitrary unions. The members of this
family are called the open sets. A set is closed iff its complement is open.

In Lean the family of open sets is given by the predicate `IsOpen`

See pdf for more details of this project.
-/

#check IsOpen
#check isOpen_empty
#check isOpen_univ
#check IsOpen.inter
#check isOpen_sUnion

/--
A topological space α is `discrete` iff every set is open  -/
def IsDiscrete (α : Type) [TopologicalSpace α] : Prop :=
  ∀ s : Set α, IsOpen s

/--
In any topological space every union of open sets is open.
A space in which every intersection of open sets is open is said to be `Alexandrov`.
-/
def IsAlexandrov (α : Type) [TopologicalSpace α] :=
  ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)

section withα
variable [TopologicalSpace α]

/-- Any discrete space is Alexandrov -/
lemma IsAlexandrov_of_IsDiscrete  (hA : IsDiscrete α) : IsAlexandrov α:=
by
  sorry

#check biUnion_of_singleton
#check isOpen_biUnion

/-- A space is discrete iff every singleton set is open -/
lemma IsDiscrete_iff : IsDiscrete α ↔ ∀ (a : α), IsOpen ({a}):=
by
  sorry

/-- `Inbhd a` is the intersection of all the open sets containing `a` -/
def Inbhd (a : α) : Set α := ⋂₀ { u : Set α | a ∈ u ∧ IsOpen u }

@[simp]
lemma Inbhd' (a : α) : Inbhd a = ⋂₀ { u : Set α | a ∈ u ∧ IsOpen u }:=  sorry


/-- a belongs to its Inbhd -/
@[simp]
lemma mem_Inbhd (a : α) : a ∈ Inbhd a :=
by
  sorry

/-- If a ∈ u and u is open then Inbhd a ⊆ u -/
lemma Inbhd_subset {a : α} (hu : IsOpen u) (h : a ∈ u) : Inbhd a ⊆ u:=
by
  sorry

/-- In an Alexandrov space every Inbhd is open -/
lemma IsOpen_Alexandrov_Inbhd (hA : IsAlexandrov α) (a : α) : IsOpen (Inbhd a) :=
by
  sorry

/-- If S is a family of open sets then the intersection of the sets in S
is the union of the Inbhds of its elements -/
lemma iInter_of_open_eq_iUnion_Inbhd (hS : ∀ (s : Set α), s ∈ S → IsOpen s) :
 ⋂₀ S = ⋃ (x ∈ ⋂₀ S), Inbhd x:=
by
  sorry


#check isOpen_biUnion

/-- If every Inbhd is open then the space is Alexandrov -/
theorem Alexandrov_of_Inbhd_IsOpen (h : ∀ a : α, IsOpen (Inbhd a)) : IsAlexandrov α:=
by
  sorry

/-- A topological space is Alexandrov iff every Inbhd is open -/
theorem Alexandrov_iff : IsAlexandrov α ↔ ∀ a : α, IsOpen (Inbhd a) :=
by
  sorry

/-
 #  Separation axioms

Separation axioms are a way of imposing conditions on a topological space that
tell us how easy it is to distinguish between points (or sets) using the topology.

They start with T₀-spaces and go up to T₅-spaces. We will only really consider T₀ and T₁
spaces.

A T₁-space is a topological space in which `x ≠ y` implies there exists an open
set `u` such that `x ∈ u and y ∉ u`.

In Lean this is defined equivalently as every singleton set is closed,
which in turn is equivalent to saying `∀ (a : α), IsOpen {a}ᶜ`
-/
#check T1Space
#check isOpen_compl_singleton

/-- In a T₁-space the Inbhd of any point is the singleton set -/
lemma Alexandrov_Inbhd_singleton_T1 [T1Space α] (a : α) : {a} = Inbhd a :=
by
  sorry

/-- Any Alexandrov T₁-space is discrete -/
theorem IsDiscrete_of_T1_Alexandrov [T1Space α] (hA : IsAlexandrov α) : IsDiscrete α:=
by
  sorry

/-
One of the most common separation axioms to be used in is T₂, otherwise known as Hausdorff space.

A space is T₂ iff for any x ≠ y there exists a pair of disjoint open sets u,v such that x ∈ u and y ∈ v.

We won't actually use them but since every T₂-space is a T₁-space we get the next result for free.
-/
#print T2Space

theorem IsDiscrete_of_T2_Alexandrov [T2Space α] (hA : IsAlexandrov α) : IsDiscrete α:=
by
  sorry

/-
Any Metric space is also a T₁-space (and more).
-/

lemma IsDiscrete_of_MetricAlexandrov (α : Type) [MetricSpace α] (hA : IsAlexandrov α) :  IsDiscrete α:=
by
  sorry


/-  # Preorders and topologies

One place where Alexandrov topologies arise naturally is when constructing a topology from
a Preorder.

First we consider how we can define a Preorder from a topology.

If α is a topological space we can define `≤` on `α` by
`a ≤ b` iff `Inbhd b ⊆ Inbhd a`

-/

/-- A Preorder induced by a topology -/
instance  toPre  [TopologicalSpace α] : Preorder α  where
  le := fun a  b => Inbhd b ⊆ Inbhd a
  lt := fun a b => Inbhd b ⊂ Inbhd a
  le_refl := by
    sorry
  le_trans :=by
    sorry
  lt_iff_le_not_le :=by
    sorry

/-- In the `toPre Preorder`, we have `a ≤ b` iff every open set containing a also contains b-/
lemma Top_le_iff (a b : α) : a ≤ b ↔ ∀ u, a ∈ u → IsOpen u → b ∈ u:=
by
  sorry

/-
A T₀-space is a topological space in which x ≠ y implies there exists an open
set u such that either `x ∈ u and y ∉ u` or `x ∉ u and y ∈ u`

If α is a T₀-space then the `toPre Preorder` is in fact a `PartialOrder`
-/
#check exists_isOpen_xor'_mem

instance [T0Space α] : PartialOrder α where
  le_antisymm :=by
    sorry

end withα

/-
We now reverse our point of view and consider how we can define a topology
on a type that has a Preorder.
-/


variable {β : Type}

/-- A topology induced by a Preorder -/
instance toTop  [Preorder β]  : TopologicalSpace β where
  IsOpen := { s | ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, x ≤ y → y ∈ s }
  isOpen_univ :=by
      sorry
  isOpen_inter :=by
      sorry
  isOpen_sUnion :=by
      sorry

/-- The set of points above or equal to b -/
@[simp]
def Up [Preorder β] (b : β): Set β := {x | b ≤ x}

/-- Up b is open-/
lemma Up_isOpen [Preorder β] (b : β) : IsOpen (Up b):=
by
  sorry

/-- The topology induced by a Preorder is Alexandrov-/
theorem IsAlexandrov_of_toTop [Preorder β] : IsAlexandrov β :=
by
  sorry

#check t0Space_iff_inseparable
#check inseparable_iff_forall_open
/-- If we start with a PartialOrder we get a T₀-space -/
instance IsT0Space_of_toTop_of_PartialOrder [PartialOrder β] : T0Space β :=
by
  sorry

/-- In the topolgical space induced by a Preorder, the `Inbhd b` is `Up b = {x | b ≤ x}` -/
@[simp]
lemma Up_eq_Inbhd (b : β) [Preorder β] : Inbhd b = Up b :=
by
  sorry

/--
If we start with a Preorder and form the topological space `toTop β` and then consider
 the Preorder given by that topological space, i.e. `toPre (toTop β)` then we recover
 the original Preorder.
-/
theorem toPre_of_toTop_eq_Pre [Preorder β] (a b : β) : a ≤ b ↔ (Inbhd b ⊆ Inbhd a):=
by
  sorry

/-
The converse of the previous result cannot hold in general since we have already proved that the
`toTop` topological space induced by a Preorder is always Alexandrov (thus if we start with a non-
Alexandrov space β then we cannot hope for `toTop (toPre β)` to be original topological space).

However we can prove that the converse holds for Alexandrov spaces.
-/

/--
If we start with an Alexandrov space β and form the Preorder `toPre β` and then form the topological
 space from this preorder, i.e. `toTop (toPre β)` we recover the original topological space.
-/
theorem toTop_of_toPre_eq_Top_of_Alexandrov [TopologicalSpace β] (hA : IsAlexandrov β) (s : Set β):
  IsOpen s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, x ≤ y → y ∈ s :=
by
  sorry

/-
  Possible extension:

  # A useful example

We now construct a very simple but useful topological space starting with
 a two element set {bot,top} which we order in the obvious way, proving that this
 is a Preorder and so Lean can infer a topology on this type.
-/

inductive Point where
| bot : Point
| top : Point

namespace Point
open Point

instance : LE Point where
  le := fun a b => (a = b) ∨ (a = bot ∧ b = top )

@[simp]
lemma le' (a b : Point) : a ≤ b ↔ (a = b) ∨ ( a = bot ∧ b = top ):=by sorry

instance : LT Point where
  lt := fun a b =>  (a = bot ∧ b = top )

@[simp]
lemma lt' (a b : Point) : a < b ↔ ( a = bot ∧ b = top ) :=by sorry

instance : Preorder Point where
  le_refl :=by
    sorry
  le_trans :=by
    sorry
  lt_iff_le_not_le :=by
    sorry

instance : PartialOrder Point where
  le_antisymm :=by
    sorry


/-- So we have a topological space on Point that is a T₀-space -/
lemma Point_IsT0Space : T0Space Point:=by
  sorry

/-- The definition of open set is from the preorder -/
lemma Point_open (s : Set Point) : IsOpen s ↔ ∀ x, x ∈ s → ∀ y, x ≤ y → y ∈ s:=
by
  sorry

/-- The open sets are exactly ∅, univ and {top}-/
lemma Point_open_iff {s : Set Point} : IsOpen s ↔ s = ∅ ∨ s = univ ∨ s = {top}:=
by
    sorry

/-- In particular {top} is open-/
lemma top_open : IsOpen {top}:=
by
  sorry

/-- Point is not a T₁-space -/
lemma Point_IsNotT1Space : ¬T1Space Point :=
by
  sorry

/-
Prove that given any topological space α there is an equivalence between
the sets in the topology on α and the set of continuous functions from α to Point.
-/


variable {α :Type}
open Classical
noncomputable section

@[simp]
def χ (s : Set α) : α → Point := fun x => ite (x ∈ s) top bot

@[simp]
lemma χ_preimage (s : Set α) : (χ s) ⁻¹' {top} = s:=
by
  sorry

@[simp]
lemma χ_of_preimage {f : α → Point} : χ (f ⁻¹' {top}) = f :=
by
  sorry

/-
The definition of continuous function f : X → Y, where X and Y are topological spaces,
is that the preimage of any open set in Y is open in X.
-/

#check continuous_def
#check preimage_empty
#check preimage_univ

def classifying [TopologicalSpace α] : {s : Set α // IsOpen s} ≃ {f : α → Point // Continuous f}  where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
