import Mathlib.Tactic
import UCLMATH0109.Projects.LinearAlgebra.ElemMatRow.ElemMatRow

/-
In this project we explore a simplified version of Gaussian Elimination
 (essentially the forwards part of standard Gaussian elimination)

Given an n × n matrix M over a field 𝔽 we describe an algorithm (i.e. a computable function)
to produce an equivalent matrix that is upper triangular using two basic elementary row operations.

Our goal is to prove that this algorithm works (in the sense that the final matrix is upper triangular)
and that this can always be done in at most n * (n + 1) steps.

A single step will be performed by `GaussStep` and (using iteration)
we will prove that `GaussStep^[n*(n+1)] M` is upper-triangular.

(Here f^[k] x = f(f(f(⋯ (x)))) is f iterated k times on input x.)

Our matrices will be indexed by `Fin n` the type of natural numbers less than n.

See pdf for more details.

-/

variable {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]

open Finset Matrix


/-- A matrix is Not Upper Triangular iff ∃ i < j, such that M i j ≠ 0 -/
@[reducible]
def Matrix.nut (M : Matrix (Fin n) (Fin n) 𝔽) : Prop := ∃ i j, j < i ∧ M i j ≠ 0


/- A matrix is Upper Triangular iff ∀ i j, j < i → M i j = 0 -/
@[reducible]
def Matrix.ut (M :  Matrix (Fin n) (Fin n) 𝔽) : Prop := ∀ i j, j < i → M i j = 0

/-
We will mainly be dealing with not upper triangular matrices
-/

/-- M is upper triangular iff it is not not upper triangular -/
lemma ut_iff_not_nut {M :  Matrix (Fin n) (Fin n) 𝔽} : M.ut ↔ ¬ M.nut :=
by
  sorry

/-- Being not upper triangular is Decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽) : Decidable M.nut:=inferInstance

/-
We will use two basic row operations: `swap` and `sub_mul_inv`
-/

#check swap
#check sub_mul_inv
/-
We have already a simplification result for `swap` but you need to do this for `sub_mul_inv`
-/
#check swap_apply
#check Matrix.updateRow_apply

/-- The k l entry of the M.sub_mul_inv i j is given by ... -/
lemma Matrix.sub_mul_inv_apply (M : Matrix (Fin n) (Fin n) 𝔽) : (M.sub_mul_inv i j) k l = if k = i then
((M i l) - (M i j) * (M j j)⁻¹ * (M j l)) else M k l :=
by
  sorry


/- To simplify our notation we introduce a type of NotUpperTriangular matrices.
This will allow us to prove results for not upper-triangular matrices without needing to constantly
carry around the assumption that the matrix is indeed not upper-triangular -/


/-- If `M : NUT n 𝔽` then `M.mat` is an n x n matrix over 𝔽 and `M.nut'` is a proof that the
matrix `M.mat` is not upper triangular -/
@[ext]
structure NUT (n : ℕ) (𝔽 : Type) [Field 𝔽] where
mat : Matrix (Fin n) (Fin n) 𝔽
nut' : mat.nut


namespace NUT
open NUT

/-- If M : NUT n 𝔽 then there is column k such that there exists a non-zero entry below
the diagonal in column k of M.mat -/
lemma non_zero_cols_nonempty (M : NUT n 𝔽):
((univ : Finset (Fin n)).filter (fun k => ∃ i, k < i ∧ M.mat i k ≠ 0)).Nonempty:=
by
  sorry

/-
Our GaussStep algorithm needs to find the `pivot` (see pdf for terminology).
Our next definition finds the column index.
-/

/-- The index of the first column of M.mat in which there exists a
non-zero entry below the diagonal -/
def J (M : NUT n 𝔽) : Fin n :=
by
  let K : Finset (Fin n):=(univ : Finset (Fin n)).filter (fun k => ∃ i, k < i ∧ M.mat i k ≠ 0)
  exact K.min' M.non_zero_cols_nonempty

/-- Properties of M.J: (1) there is a non-zero entry in this column below the diagonal and
(2) no column to the left of it contains a non-zero entry below the diagonal -/
lemma J_spec (M : NUT n 𝔽) : ∃ i, M.J < i ∧ M.mat i M.J ≠ 0 ∧ ∀ k l, l <  M.J → l < k → M.mat k l = 0:=
by
  sorry

/-- The non-zero column contains a non-zero entry below the diagonal so this Finset is Nonempty -/
lemma non_zero_entry_of_non_zero_col (M : NUT n 𝔽) :
 ((univ : Finset (Fin n)).filter (fun l => (M.J < l ∧ M.mat l M.J ≠ 0))).Nonempty:=
by
  sorry
/-
Our next definition finds the row index of the pivot
-/
/-- The first non-zero entry below the diagonal in the first non-zero column -/
def I (M : NUT n 𝔽) : Fin n :=
by
  let L : Finset (Fin n):= (univ : Finset (Fin n)).filter (fun l => M.J < l ∧ M.mat l M.J ≠ 0)
  exact L.min' M.non_zero_entry_of_non_zero_col


/-
We can now compute the pivot as (M.I, M.J) where (M : NUT n 𝔽).
-/

/- The properties of M.I and M.J (see below for more useful versions)-/
lemma I_J_spec (M : NUT n 𝔽) :
 M.J < M.I ∧ M.mat M.I M.J ≠ 0 ∧ (∀ k l, l < M.J → l < k → M.mat k l = 0) ∧ (∀ m, m < M.I → M.J < m → M.mat m M.J = 0) :=
by
  sorry

/-- The pair (M.I, M.J) are below the diagonal -/
lemma j_lt_i (M : NUT n 𝔽) : M.J < M.I :=
by
  sorry

/-- The entry in position M.I M.J is non-zero-/
lemma ij_ne_zero (M : NUT n 𝔽) : M.mat M.I M.J ≠ 0 :=
by
  sorry

/-- Every entry to the left of M.J and below the diagonal is zero -/
lemma zero_left_below (M : NUT n 𝔽) (hl : l < M.J) (hk: l < k) : M.mat k l = 0:=
by
  sorry

/-- Every entry in the M.J above M.I but below the diagonal is zero -/
lemma zero_above (M : NUT n 𝔽) (hk : k < M.I) (hkdiag: M.J < k) : M.mat k (M.J) = 0:=
by
  sorry


/-
We introduce a notion of weight, a natural number, that is clearly bounded above and below.

We will later show that applying our two elementary row operations to a
non-upper-triangular matrix (in a sensible way) will strictly increase this weight.
-/

@[reducible]
def weight (M : NUT n 𝔽) : ℕ := M.I + n * M.J

/-- Since I and J are both < n so M.weight ≤ n * (n + 1) -/
lemma weight_le (M : NUT n 𝔽) : M.weight ≤ n*(n + 1):=
by
  sorry

/-- Later when we introduce a weight for all matrices the following will be useful -/
@[simp]
lemma weight_lt (M : NUT n 𝔽) : M.weight < n*(n+1)+1 :=
by
  sorry

/-- Since I < J we have 1 ≤ J so the weight is positive -/
lemma weight_pos (M : NUT n 𝔽) : 0 < M.weight :=
by
  sorry

/-- If M.J < N.J then weight M < weight N-/
lemma weight_lt_weight_col (M N : NUT n 𝔽)  (hjlt:  M.J < N.J) : M.weight < N.weight :=
by
  sorry

/-- If M.J = N.J then weight M < weight N iff M.I < N.I -/
lemma weight_lt_weight_row (M N: NUT n 𝔽)  (hjeq:  M.J = N.J) :
 M.weight < N.weight ↔ M.I < N.I :=
by
  sorry

/-- If weight M ≤ weight N then either M.J < N.J or M.J = N.J ∧ M.I ≤ N.I-/
lemma weight_le_weight (M N : NUT n 𝔽) (hle : M.weight ≤ N.weight) :
M.J < N.J ∨ (M.J = N.J ∧ M.I ≤ N.I) :=
by
  sorry


/-
The next two lemmas are the key results that will allow us to prove that the algorithm will terminate
-/

/-- Swapping rows I and J increases the weight (if the corresponding diagonal entry is zero ) -/
lemma lt_weight_swap (M N : NUT n 𝔽) (hz : M.mat M.J M.J = 0) (hN : N.mat = M.mat.swap M.I M.J) :
  M.weight < N.weight :=
by
  sorry


/-- Subtracting the correct inverse multiple of row J from row I increases the weight
  (if the corresponding diagonal entry is non-zero ) -/
lemma lt_weight_sub_mul_inv (M N : NUT n 𝔽) (hz : M.mat M.J M.J ≠ 0) (hN : N.mat = M.mat.sub_mul_inv M.I M.J) :
 M.weight < N.weight :=
by
  sorry

/-- A single step of our algorithm :
If M is not upper triangular then GaussStep is either a swap or a sub_mul_inv depending on whether or not M j j = 0.
If M is upper triangular it does nothing.  -/
@[reducible]
def GaussStep (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
by
  by_cases hnut: M.nut
  · let N : NUT n 𝔽 := ⟨M,hnut⟩
    let i := N.I
    let j := N.J
    exact if M j j = 0 then M.swap i j else (M.sub_mul_inv i j)
  · exact M

section
variable {M : Matrix (Fin n) (Fin n) 𝔽}

/-- If M is upper triangular then a GaussStep leaves M unchanged-/
@[simp]
lemma GaussStep_ut (hut : ¬ M.nut) : GaussStep M = M :=
by
  sorry

/-- If M is not upper triangular then a GaussStep is a swap or a sub_mul_inv -/
@[simp]
lemma GaussStep_nut (M : NUT n 𝔽) : GaussStep M.mat = if M.mat M.J M.J = 0 then M.mat.swap M.I M.J else (M.mat.sub_mul_inv M.I M.J):=
by
  sorry

/-- If M and N are not upper triangular and N.mat =  GaussStep M.mat then M.weight < N. weight -/
lemma GaussStep_weight_inc (M N : NUT n 𝔽)
(hN : N.mat = GaussStep M.mat) : M.weight < N.weight:=
by
  sorry

/-
Our `weight` function is only defined for objects of type `NUT n 𝔽`.
We need a new version that works for all matrices.

It will be convient to make this new ` weight' ` decrease at each useful GaussStep so we
define it be `n * (n + 1) + 1 - weight M` for M not upper triangular and `0` otherwise
Note this weight is still bounded above by `n * (n + 1)` and below by `0` -/

/-- The weight' of a matrix -/
def weight' (M : Matrix (Fin n) (Fin n) 𝔽) : ℕ :=
if h : M.nut then (n * (n + 1) + 1 - (⟨M, h⟩ : NUT n 𝔽).weight) else 0

/-- The weight' of a not upper triangular matrix is.. -/
@[simp]
lemma weight'_nut  (h : M.nut) : weight' M = n*(n + 1) + 1 - (⟨M,h⟩ : NUT n 𝔽).weight:=
by
  sorry

/-- The weight' of an upper triangular matrix is.. -/
@[simp]
lemma weight'_ut (h : ¬M.nut) : weight' M = 0:=
by
  sorry

/-- Any matrix has weight' at most n * (n + 1)-/
@[simp]
lemma weight'_le  : weight' M ≤ n*(n+1) :=
by
  sorry

/-- If M is not upper triangular then its weight' is positive-/
@[simp]
lemma weight'_pos (hnut : M.nut) : 0 < weight' M:=
by
  sorry
/-- If weight' M = 0 then M is upper triangular -/
@[simp]
lemma weight'_zero (h: weight' M = 0) : ¬ M.nut :=
by
  sorry

/-- For any not upper triangular matrix a GaussStep strictly decreases weight -/
lemma weight'_lt_of_GaussStep (hnut: M.nut) : weight' (GaussStep M) < weight' M:=
by
  sorry

end section
open Function


/-- If we iteratively apply `GaussStep` weight' M (or more) times then we obtain an upper triangular matrix -/
theorem GaussStep_steps_le_weight (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) (hk : weight' M ≤ k) :
(GaussStep^[k] M).ut :=
by
  sorry

/-- So `weight' M` steps the matrix is upper triangular -/
theorem GaussStep_term (M : Matrix (Fin n) (Fin n) 𝔽) : (GaussStep^[weight' M] M).ut :=
by
  sorry


/-- In particular n(n+1) steps suffice to put M into upper triangular form -/
theorem upperbound_on_steps (M : Matrix (Fin n) (Fin n) 𝔽) : (GaussStep^[n*(n+1)] M).ut :=
by
  sorry


end
end NUT


/-
Possible extensions:

1. Prove a better upper bound on the number of steps required. (For example n.choose 2)

2. Extend the algorithm to rectangular matrices and row echelon form (hard)
-/
