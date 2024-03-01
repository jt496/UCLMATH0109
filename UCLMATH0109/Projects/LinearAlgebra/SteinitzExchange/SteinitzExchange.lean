import Mathlib.Tactic

/-
Define a class `VectorSpace` to consist of
vector spaces over `ℝ`.

In this project you will develop the theory of vector spaces and
prove the Steinitz Exchange Lemma.

-/
class VectorSpace (V : Type) extends AddCommGroup V, DistribMulAction ℝ V where
  add_smul (x y : ℝ) (v : V) : (x + y) • v = x • v + y • v
  zero_smul (v : V) : (0 : ℝ) • v = 0

variable {V : Type} [VectorSpace V] [DecidableEq V]

namespace VectorSpace
open VectorSpace

/-- (-1) • v = -v -/
lemma neg_one_smul (v : V) : (-1 : ℝ) • v = -v:=
by
  sorry

/-- (-a) • v = - (a • v)-/
lemma neg_smul  (v : V) (a : ℝ): (-a)• v = -(a• v) :=
by
  sorry


open BigOperators Set Finset

/-- A linearCombination of a Finset of vectors is: ∑ a in A, c a • a -/
@[simp]
def linearCombination (A : Finset V) (c : V → ℝ) : V :=
∑ a in A, c a • a

/-- The span of a Finset of vectors is the Set V := {y | ∃ c, linearCombination A c = v }-/
@[simp]
def span (A : Finset V) : Set V := range (linearCombination A)

/-- v ∈ span A ↔ there exists a linear combination of A equal to v-/
@[simp]
lemma mem_span {A : Finset V} :  v ∈ span A ↔ ∃ (c : V → ℝ), ∑ a in A, c a • a = v :=
by
  sorry

/-- span ∅ = {0} -/
@[simp]
lemma span_empty : span (∅ : Finset V) = {0} :=
by
  sorry


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

/-- span is monotone on Finsets -/
@[simp]
lemma span_mono {A B : Finset V} (h: A ⊆ B) : span A ⊆ span B :=
by
  sorry

/-- If v ∉ span A then v ∉ A -/
lemma not_mem_of_not_mem_span {A : Finset V} {v : V} (h: v ∉ span A) : v ∉ A:=
by
  sorry

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
 `S.filter P` is the Finset `{ x | x ∈ S and P x = True}`
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
    w ∈ span (insert v A ) ↔ ∃ w₁ ∈ span A, ∃ c : ℝ, w = w₁ + c • v :=
by
  sorry

/-- If v ∈ span A then span (insert v A) = span A -/
lemma span_insert_of_mem_span {A : Finset V} {v : V} (h : v ∈ span A) :
    span (insert v A) = span A :=
by
  sorry

/-- A Spans iff ∀ v, ∃ c, ∑ a in A, c a • a = v -/
@[simp]
def Spans (A : Finset V) : Prop :=
∀ (v : V), ∃ c : V → ℝ , linearCombination A c = v

/-- A Spans iff span A = univ : Set V -/
lemma Spans_iff {A : Finset V} : Spans A ↔ span A = Set.univ :=
by
  sorry

/-- If A Spans then every vector is in span A-/
lemma mem_Spans {A : Finset V} (hS : Spans A) (v : V) : v ∈ span A:=
by
  sorry

/--
  A useful lemma for the proof of Steinitz later.

If A ⊆ B and v ∉ span A but v ∈ span B then ∃ c, ∑ b in B, c b • b = v and ∃ b ∈ B \ A, c b ≠ 0 -/
lemma mem_span_super {A B : Finset V} (hAB: A ⊆ B) (v : V) (hnA : v ∉ span A) (hB: v ∈ span B) :
∃ c, linearCombination B c = v ∧ ∃ b ∈ B \ A, c b ≠ 0:=
by
  sorry


/-- A is Dependent if there is a non-trivial linear combination of A that equals the zero vector-/
@[simp]
def Dependent (A : Finset V) : Prop :=
  ∃ c : V → ℝ, linearCombination A c = 0 ∧  ∃ a ∈ A, c a ≠ 0


/-- A is Independent iff it is not Dependent -/
@[simp]
def Independent (A : Finset V) : Prop := ¬ Dependent A


/-- The empty set is Independent -/
@[simp]
lemma Independent_empty : Independent (∅ : Finset V) :=
by
  sorry

/-- If A is Dependent and A ⊆ B then B is Dependent (it is `monotone`)-/
lemma Dependent_mono {A B : Finset V} (h: A ⊆ B) (hI : Dependent A) : Dependent B :=
by
  sorry


/-- If B is Independent and A ⊆ B then A is Independent (this is called `antitone`)-/
@[simp]
lemma Independent_anti {A B : Finset V} (h: A ⊆ B) (hI : Independent B) : Independent A :=
by
  sorry

/-- If v ∉ A but v ∈ span A then `insert v A` is Dependent -/
lemma Dependent_insert_mem_span {A : Finset V} {v : V} (hv : v ∈ span A) (hnin: v ∉ A ): Dependent (insert v A):=
by
  sorry

/--If A is independent and v ∉ span A then `insert v A` is independent -/
lemma Independent_insert_not_mem {A : Finset V} {v : V} (hl : Independent A) (hv : v ∉ span A) :
    Independent (insert v A) :=
by
  sorry


/-
For the next proof it is sensible to use `Finset.induction_on`
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
  ∃ B, B ⊆ A  ∧ span B = span A ∧ Independent B :=
by
  sorry

/-- A basis is a spanning set that is independent -/
def IsBasis (A : Finset V) : Prop := Spans A ∧ Independent A


variable (V)
/-- V is FiniteDimensional if there exists a spanning Finset A -/
def FiniteDim :Prop := ∃ A : Finset V, Spans A
variable {V}


/-- If V is finite-dimensional there exists a basis -/
theorem finite_dim_iff_exists_basis  : FiniteDim V ↔ ∃ A : Finset V, IsBasis A  :=
by
  sorry


/-- The Steinitz Exchange Lemma: if A is independent and B is spanning then we can
find a new spanning set (A ∪ C) with C ⊆ B and |A ∪ C| = |B| -/
theorem Steinitz {A B : Finset V} (hA : Independent A) (hB : Spans B) :
    ∃ C : Finset V, C ⊆ B ∧ Spans (A ∪ C) ∧ (A ∪ C).card = B.card :=
by
  sorry

/-- If A is independent and B is spanning then |A| ≤ |B| -/
theorem independent_le_spans {A B: Finset V} (hl : Independent A) (hm : Spans B) :
    A.card ≤ B.card :=
by
  sorry

/-- Any two bases have the same (finite) cardinality -/
theorem card_basis_eq {A B : Finset V} (hA : IsBasis A) (hB : IsBasis B) :
    A.card = B.card :=
by
  sorry


/-
There are many possible extensions, e.g.:

Define the external direct sum `V ⊕ W` as a vector space
and prove that `dim V ⊕ W = dim V + dim W`.

Define a structure `Subspace V`.
Construct `span A` as a term of type `Subspace V`.

Define a structure `Linear V W` of linear maps from `V` to `W`.
Construct the image and kernel of a linear map as a subspace.
Prove the rank-nullity theorem.

Define an instance of `Add (Subspace V)` (the sum of two subspaces).
Prove that addition of subspaces is commutative and associative.

Define the intersection of two subspaces as a subspace.
Prove the dimension formula `dim (A + B) + dim (A ∩ B) = dim A + dim B`.

-/
