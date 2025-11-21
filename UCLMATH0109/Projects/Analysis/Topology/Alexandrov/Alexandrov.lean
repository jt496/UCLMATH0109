import Mathlib.Topology.Basic
import Mathlib.Tactic

open Set


/-
# In this project we will explore the properties of the Alexandrov topology.
# Read the project pdf for details. See below for useful results from Mathlib.

The definition of a topological space in Lean is as follows:

class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

-/

/--
A topological space X is `discrete` iff every set is open  -/
def IsDiscrete (X : Type) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsOpen s

/--
In any topological space every `union` of open sets is open.
A space in which every `intersection` of open sets is open is said to be `Alexandrov`.
-/
def IsAlexandrov (X : Type) [TopologicalSpace X] :=
  ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)

section withX
variable [TopologicalSpace X]


/-- `In a` is the intersection of all the open sets containing `a` -/
def In (a : X) : Set X := ⋂₀ { u : Set X | a ∈ u ∧ IsOpen u }


/-- A topological space is Alexandrov iff every In is open -/
theorem Alexandrov_iff : IsAlexandrov X ↔ ∀ a : X, IsOpen (In a) :=by
  sorry


/-
 #  Separation axioms

Separation axioms are a way of imposing conditions on a topological space that
tell us how easy it is to distinguish between points (or sets) using the topology.

They start with T₀-spaces and go up to T₅-spaces. We will only really consider T₀ and T₁
spaces.

A T₁-space is a topological space in which `x ≠ y` implies there exists an open
set `U` such that `x ∈ U and y ∉ U`.

In Lean this is defined equivalently as every singleton set is closed,
which in turn is equivalent to saying `∀ (a : X), IsOpen {a}ᶜ`

class T1Space (X : Type u) [TopologicalSpace X] : Prop where
--  A singleton in a T₁ space is a closed set.
  t1 : ∀ x, IsClosed ({x} : Set X)
-/

#check T1Space


/-- Any Alexandrov T₁-space is discrete -/
theorem IsDiscrete_of_T1_Alexandrov [T1Space X] (hA : IsAlexandrov X) : IsDiscrete X:=by
  sorry



/-  # Preorders and topologies

One place where Alexandrov topologies arise naturally is when constructing a topology from
a Preorder.

First we consider how we can define a Preorder from a topology.

If X is a topological space we can define `≤` on `X` by
`a ≤ b` iff `In b ⊆ In a`

-/
/-- A Preorder induced by a topology -/
instance  toPre  [TopologicalSpace X] : Preorder X  where
  le := fun a  b => In b ⊆ In a
  lt := fun a b => In b ⊂ In a
  le_refl := by sorry
  le_trans :=by sorry
  lt_iff_le_not_le :=by sorry

/-- In the `toPre Preorder`, we have `a ≤ b` iff every open set containing a also contains b-/
lemma Top_le_iff (a b : X) : a ≤ b ↔ ∀ u, a ∈ u → IsOpen u → b ∈ u:=by
  sorry

/-
A T₀-space is a topological space in which x ≠ y implies there exists an open
set U such that either `x ∈ U and y ∉ U` or `x ∉ U and y ∈ U`

If X is a T₀-space then the `toPre Preorder` is in fact a `PartialOrder`
-/

instance [T0Space X] : PartialOrder X where
  le_antisymm :=by sorry


end withX

/-
We now reverse our point of view and consider how we can define a topology
on a type Y that has a Preorder.
-/


variable {Y : Type}

/-- The topology induced by a Preorder -/
instance toTop  [Preorder Y]  : TopologicalSpace Y where
  IsOpen := { s | ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, x ≤ y → y ∈ s }
  isOpen_univ :=by sorry
  isOpen_inter :=by sorry
  isOpen_sUnion :=by sorry

/-- The set of points above or equal to b -/
@[simp]
def Up [Preorder Y] (b : Y): Set Y := {x | b ≤ x}

/-- Up b is open-/
lemma Up_isOpen [Preorder Y] (b : Y) : IsOpen (Up b):=by
  sorry

/-- The topology induced by a Preorder is Alexandrov-/
theorem IsAlexandrov_of_toTop [Preorder Y] : IsAlexandrov Y :=by
  sorry


/-- If we start with a PartialOrder we get a T₀-space -/
instance IsT0Space_of_toTop_of_PartialOrder [PartialOrder Y] : T0Space Y :=by
  sorry

/--
If we start with a Preorder and form the topological space `toTop Y` and then consider
 the Preorder given by that topological space, i.e. `toPre (toTop Y)` then we recover
 the original Preorder.
-/
theorem toPre_of_toTop_eq_Pre [Preorder Y] (a b : Y) : a ≤ b ↔ (In b ⊆ In a):=by
  sorry

/-
The converse of the previous result cannot hold in general since we have already proved that the
`toTop` topological space induced by a Preorder is always Alexandrov (thus if we start with a non-
Alexandrov space Y then we cannot hope for `toTop (toPre Y)` to be the original topological space).

However we can prove that the converse holds for Alexandrov spaces.
-/

/--
If we start with an Alexandrov space Y and form the Preorder `toPre Y` and then form the topological
 space from this preorder, i.e. `toTop (toPre Y)` we recover the original topological space.
-/
theorem toTop_of_toPre_eq_Top_of_Alexandrov [TopologicalSpace Y] (hA : IsAlexandrov Y) (s : Set Y):
  IsOpen s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, x ≤ y → y ∈ s :=by
  sorry


/-
Possible extension:

Construct a very simple but useful topological space starting with
a two element set `{bot, top}` which we order in the obvious way, proving that this
is a Preorder and so Lean can infer a topology on this type.
-/

inductive Point where
| bot : Point
| top : Point

namespace Point
open Point

instance : LE Point where
  le := fun a b => (a = b) ∨ (a = bot ∧ b = top )

instance : LT Point where
  lt := fun a b =>  (a = bot ∧ b = top )

instance : Preorder Point where
  le_refl :=by sorry
  le_trans :=by sorry
  lt_iff_le_not_le :=by sorry

instance : PartialOrder Point where
  le_antisymm :=by sorry


/-- So we have a topological space on Point that is a T₀-space -/
lemma Point_IsT0Space : T0Space Point:=by
  sorry


/-- Point is not a T₁-space -/
lemma Point_IsNotT1Space : ¬T1Space Point :=by sorry


/-
Prove that given any topological space X there is an equivalence between
the sets in the topology on X and the set of continuous functions from X to Point.
-/


variable {X :Type}
open Classical
noncomputable section

/-
The definition of continuous functions f : X → Y, where X and Y are topological spaces,
is that the preimage of any open set in Y is open in X.
-/
#check continuous_def
#check preimage_empty
#check preimage_univ

def classifying [TopologicalSpace X] : {s : Set X // IsOpen s} ≃ {f : X → Point // Continuous f} :=
  sorry
