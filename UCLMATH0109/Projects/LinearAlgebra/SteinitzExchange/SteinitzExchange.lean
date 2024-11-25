import Mathlib.Tactic

/-
# The main goal of this project is to prove the Steinitz Exchange Lemma and deduce
# that any two bases of a finite dimensional vector space have the same cardinality.
# See the pdf for details.

Define a class `VectorSpace` to consist of
vector spaces over `ℝ`.

In this project you will develop the theory of vector spaces and
prove the Steinitz Exchange Lemma.

-/


class VectorSpace (V : Type) extends AddCommGroup V, DistribMulAction ℝ V where
  add_smul (x y : ℝ) (v : V) : (x + y) • v = x • v + y • v
  zero_smul (v : V) : (0 : ℝ) • v = 0

variable {V : Type} {A B : Finset V} [VectorSpace V] [DecidableEq V]

namespace VectorSpace
open VectorSpace

/-- (-1) • v = -v -/
lemma neg_one_smul (v : V) : (-1 : ℝ) • v = -v:=
by
  rw [← add_left_inj ((1:ℝ)•v), ← add_smul _ 1 v]
  simp only [add_left_neg, one_smul, isUnit_zero_iff, zero_ne_one]
  exact zero_smul _

/-- (-a) • v = - (a • v)-/
lemma neg_smul  (v : V) (a : ℝ): (-a)• v = -(a• v) :=
by
  rw [neg_eq_neg_one_mul a, ← smul_smul, neg_one_smul (a • v)]


instance : Module ℝ V where
  smul := fun r v => r • v
  one_smul :=by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  smul_add :=by sorry
  add_smul := by sorry
  zero_smul := by sorry

open BigOperators Set Finset

/-- A linearCombination of a Finset of vectors is: ∑ a in A, c a • a -/
@[simp]
def linearCombination (A : Finset V) (c : V → ℝ) : V :=
∑ a in A, c a • a

/-- The span of a Finset of vectors is the Set V := {y | ∃ c, linearCombination A c = v }-/
@[simp]
def span (A : Finset V) : Set V := range (linearCombination A)


/-
You will need to prove quite few results that involve defining particular
linearCombinations. Many of these will use `if - then - else` descriptions.
Results about these usually have `ite` in their name.
Below we give a few useful examples
-/
#check ite_true
#check ite_smul
#check ite_eq_left_iff
#check sum_ite
#check sum_ite_mem
#check sum_ite_eq
#check sum_ite_eq'
/-
If `A : Finset V` then `insert v A` is the Finset V given by inserting v into A.

You should use this rather than `A ∪ {v}` in most cases.

Lean has lots of useful results about `insert` (and its counterpart `erase`).
Here are some examples:
-/
#check mem_insert
#check mem_insert_of_mem
#check insert_eq_of_mem
#check sum_insert

#check mem_erase
#check not_mem_erase
#check mem_erase_of_ne_of_mem
#check sum_erase

/-
You will probably also need to use Finset.filter in some places.
Given a Finset S and a predicate P : S → Prop,
 `S.filter P` is the Finset `{ x | x ∈ S ∧ P x }`
-/
#check filter_true_of_mem
#check sum_filter
/-
A vector w belongs to span (insert v A) iff it can be expressed as a vector in
span A + a scalar multiple of v.
-/

/-- w ∈ span (insert v A) ↔ ∃ w₁ ∈ span A, ∃ c : ℝ, w = w₁ + c • v -/
@[simp]
lemma mem_span_insert (A : Finset V) (v : V) {w : V} :
    w ∈ span (insert v A ) ↔ ∃ w₁ ∈ span A, ∃ c : ℝ, w = w₁ + c • v :=by
  sorry

/-- If v ∈ span A then span (insert v A) = span A -/
lemma span_insert_of_mem_span (h : v ∈ span A) :
    span (insert v A) = span A :=by
  sorry

/-- A Spans iff ∀ v, ∃ c, ∑ a in A, c a • a = v -/
@[simp]
def Spans (A : Finset V) : Prop :=
∀ (v : V), ∃ c : V → ℝ , linearCombination A c = v

-- A useful lemma for the proof of Steinitz later.
/--
If v ∉ span A but v ∈ span B then ∃ c, ∑ b in B, c b • b = v and ∃ b₀ ∈ B \ A, c b₀ ≠ 0 -/
lemma mem_span_super  (hnA : v ∉ span A) (hB: v ∈ span B) :
∃ c, linearCombination B c = v ∧ ∃ b₀ ∈ B \ A, c b₀ ≠ 0:=by
  sorry

/-- A is Dependent if there is a non-trivial linear combination of the elements of
  A that equals the zero vector-/
@[simp]
def Dependent (A : Finset V) : Prop :=
  ∃ c : V → ℝ, linearCombination A c = 0 ∧  ∃ a ∈ A, c a ≠ 0

/-- A is Independent iff it is not Dependent -/
@[simp]
def Independent (A : Finset V) : Prop := ¬ Dependent A

/-- The empty set is Independent -/
@[simp]
lemma Independent_empty : Independent (∅ : Finset V) :=by
  sorry


/-- If v ∉ A but v ∈ span A then `insert v A` is Dependent -/
lemma Dependent_insert_mem_span (hv : v ∈ span A) (hnin: v ∉ A ): Dependent (insert v A):=by
  sorry

/--If A is independent and v ∉ span A then `insert v A` is independent -/
lemma Independent_insert_not_mem (hl : Independent A) (hv : v ∉ span A) :
    Independent (insert v A) :=by
  sorry

/-
For the next proof you could use `Finset.induction_on`
-/
#check Finset.induction_on
/-
This expresses the obvious fact that to prove
`∀ A : Finset V, P A`
it is sufficient to prove that:

`empty`: `P ∅`
`insert`: Whenever `P S` and `a ∉ S` then `P (S.insert a)`
-/

/-- Any Finset A, contains an independent subset with the same span -/
theorem exists_independent_subset (A : Finset V) :
  ∃ B, B ⊆ A  ∧ span B = span A ∧ Independent B :=by
  induction A using Finset.induction_on
  case empty =>
    sorry
  case insert v A hnin ih =>
    sorry

/-- A basis is a spanning set that is independent -/
def IsBasis (A : Finset V) : Prop := Spans A ∧ Independent A

variable (V)
/-- V is FiniteDimensional if there exists a spanning Finset A -/
def FiniteDim :Prop := ∃ A : Finset V, Spans A
variable {V}

/-- If V is finite-dimensional there exists a basis -/
theorem finite_dim_iff_exists_basis : FiniteDim V ↔ ∃ A : Finset V, IsBasis A  :=by
  sorry


/-- The Steinitz Exchange Lemma: if A is independent and span A ⊆ span B then we can
find a set (A ∪ C) with C ⊆ B such that span (A ∪ C) = span B and |A ∪ C| = |B| -/
theorem Steinitz' (hA : Independent A) (hB : span A ⊆ span B) :
    ∃ C : Finset V, C ⊆ B ∧ span (A ∪ C) = span B ∧ (A ∪ C).card = B.card :=by
  induction A using Finset.induction_on
  case empty =>
    sorry
  case insert v A hnin ih =>
    sorry

theorem Steinitz (hA : Independent A) (hB : Spans B) :
    ∃ C : Finset V, C ⊆ B ∧ Spans (A ∪ C) ∧ (A ∪ C).card = B.card :=by
  sorry

/-- If A is independent and B is spanning then |A| ≤ |B| -/
theorem independent_le_spans (hl : Independent A) (hm : Spans B) : A.card ≤ B.card := by
  sorry

/-- Any two bases have the same (finite) cardinality -/
theorem card_basis_eq (hA : IsBasis A) (hB : IsBasis B) :
    A.card = B.card :=
 sorry

lemma spans_le_is_basis (hA : IsBasis A) (hB : Spans B) (hle : B.card ≤ A.card) :
    IsBasis B := by
  sorry



variable (V)
open Classical in
noncomputable
def Dimension : ℕ∞ := if h : (∃ A : Finset V, IsBasis A) then h.choose.card else ⊤
variable {V}


lemma dimension_spec (hA : IsBasis A) : Dimension V = A.card := by
  sorry


/-
There are many possible extensions:
For example, you could define a structure `Subspace V`.
Construct `span A` as a term of type `Subspace V`.

Define an instance of `Add (Subspace V)` (the sum of two subspaces)
and `Inter (Subspace V)` (the intersection of two subspaces).

Prove the dimension formula `dim (A + B) + dim (A ∩ B) = dim A + dim B`.
-/
