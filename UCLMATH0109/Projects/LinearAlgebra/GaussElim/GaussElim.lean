import Mathlib

/-
# This project is on Gaussian elimination and upper triangular form
# See the pdf for details.

In this project we explore a simplified version of Gaussian Elimination (essentially the forwards part
of standard Gaussian elimination)

Given an n × n matrix M over a field 𝔽 we describe an algorithm (i.e. a computable function)
to produce an equivalent matrix that is upper triangular using two basic elementary row operations:

Our goal is to prove that this algorithm works (in the sense that the final matrix is upper triangular)
and that this can always be done in at most n² - 1 steps.

A single step will be performed by `GaussStep` and (using iteration: see Function.iterate)
we will prove that `GaussStep^[n² - 1] M` is upper-triangular

Our matrices will be indexed by `Fin n` the type of natural numbers less than n.
-/

variable {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]

open Finset Matrix

namespace Matrix

/-- `M.swap i j` is M with the i and j rows swapped-/
@[reducible]
def swap (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m): Matrix (Fin m) (Fin n) 𝔽:=
 (M.updateRow i (M j)).updateRow j (M i)

/--
 `M.sub_mul_inv i j` is M with  i-th row equal to `(row i)-(M i j)* (M j j)⁻¹ *(row j)`  -/
@[simp]
def sub_mul_inv (M : Matrix (Fin n) (Fin n) 𝔽) (i j : Fin n) : Matrix (Fin n) (Fin n) 𝔽:=
  M.updateRow i (M i - (fun l => (M i j)* (M j j)⁻¹*(M j l)))


/-- The k l entry of M.swap i j is given by ... -/
lemma swap_apply (M : Matrix (Fin m) (Fin n) 𝔽) :
(M.swap i j) k l = if k = j then M i l else (if k = i then M j l else M k l) :=by
  simp only [swap, updateRow_apply]

/-- The k l entry of the M.sub_mul_inv i j is given by ... -/
lemma sub_mul_inv_apply (M : Matrix (Fin n) (Fin n) 𝔽) : (M.sub_mul_inv i j) k l = if k = i then
((M i l) - (M i j) * (M j j)⁻¹ * (M j l)) else M k l :=by
  simp only [sub_mul_inv, updateRow_apply]
  rfl


/-- A matrix is Not Upper Triangular iff ∃ i < j, such that M i j ≠ 0 -/
@[reducible]
def nut (M : Matrix (Fin n) (Fin n) 𝔽) : Prop := ∃ i j, j < i ∧ M i j ≠ 0

/- A matrix is Upper Triangular iff ∀ i j, j < i → M i j = 0 -/
@[reducible]
def ut (M :  Matrix (Fin n) (Fin n) 𝔽) : Prop := ∀ i j, j < i → M i j = 0
end Matrix

/-- Being not upper triangular is Decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽) : Decidable M.nut:=inferInstance


section example_from_pdf
/-
In Lean we can describe the matrix from the pdf as follows:

!![1,2,1,0;0,1,2,1;1,3,3,0;2,4,1,2]

| 1 2 1 0 |
| 0 1 2 1 |
| 1 3 3 0 |
| 2 4 1 2 |

Note that when we use this notation Lean can work out the
dimensions of the matrix automatically but we still need to tell
Lean which field we are working over.
-/
def M₀ := (!![1,2,1,0;0,1,2,1;1,3,3,0;2,4,1,2] : Matrix _ _ ℚ)

/- You can follow the steps of the algorithm below in your Infoview -/
#eval M₀
#eval M₀.ut --false
def M₁ := M₀.sub_mul_inv 2 0
#eval M₁
#eval M₁.ut --false
def M₂ := M₁.sub_mul_inv 3 0
#eval M₂
#eval M₂.ut --false
def M₃ := M₂.sub_mul_inv 2 1
#eval M₃
#eval M₃.ut --false
def M₄ := M₃.swap 3 2
#eval M₄
#eval M₄.ut --true

end example_from_pdf

/-
We will mainly be dealing with not upper triangular matrices

To simplify our notation we introduce a Subtype of `N`ot`U`pper`T`riangular matrices.
This will allow us to prove results for not upper-triangular matrices without needing to
constantly carry around the assumption that the matrix is indeed not upper-triangular -/


/-- If `M : NUT n 𝔽` then `M.val` is an n x n matrix over 𝔽 and `M.prop` is a proof that
`M.val` is not upper triangular -/

def NUT (n : ℕ) (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] : Type :=
   {M : Matrix (Fin n) (Fin n) 𝔽 // M.nut}

namespace NUT
open NUT

/-- We can coerce `M : NUT n 𝔽` to a `Matrix (Fin n) (Fin n) 𝔽` in the obvious way -/
instance hasCoeToMatrix : Coe (NUT n 𝔽) (Matrix (Fin n) (Fin n) 𝔽) :=
  ⟨fun M => M.val⟩

/-- We can coerce `M : NUT n 𝔽` to a function from `Fin n → Fin n → 𝔽` in the obvious way
i.e. `M i j` is the ij-th entry of the matrix -/
instance instCoeFun : CoeFun (NUT n 𝔽) fun _ => (Fin n) → (Fin n) → 𝔽 where coe M := M.val

/--
If `M : NUT n 𝔽` then there exists a column of M containing a non-zero entry below the diagonal -/
lemma exists_non_zero_col (M : NUT n 𝔽):
((univ : Finset (Fin n)).filter (fun k => ∃ i, k < i ∧  M i k ≠ 0)).Nonempty:=by
  sorry

/-- The index of the first non-zero column of M -/
def J (M : NUT n 𝔽) : Fin n :=by
  let K : Finset (Fin n):=(univ : Finset (Fin n)).filter (fun k => ∃ i, k < i ∧ M i k ≠ 0)
  exact K.min' M.exists_non_zero_col

/-- Properties of M.J:
(1) there is a non-zero entry in this column below the diagonal and
(2) no column to the left of it contains a non-zero entry below the diagonal -/
lemma j_spec (M : NUT n 𝔽) : ∃ i, M.J < i ∧ M i M.J ≠ 0 ∧ ∀ k l, l <  M.J → l < k → M k l = 0:=by
  sorry

/-- The first non-zero column contains a non-zero entry below the diagonal -/
lemma exists_non_zero_entry_of_first_non_zero_col (M : NUT n 𝔽) :
 ((univ : Finset (Fin n)).filter (fun l => (M.J < l ∧ M l M.J ≠ 0))).Nonempty:=by
  sorry

/-- The index of the first non-zero entry below the diagonal in the first non-zero column -/
def I (M : NUT n 𝔽) : Fin n :=by
  let L : Finset (Fin n):= (univ : Finset (Fin n)).filter (fun l => M.J < l ∧ M l M.J ≠ 0)
  exact L.min' M.exists_non_zero_entry_of_first_non_zero_col

/-
You will need to insert and prove lemmas about the properties of I and J
-/


/-- The weight of a not upper triangular matrix. -/
@[reducible]
def weight (M : NUT n 𝔽) : ℕ := M.I + n * M.J

/-- Any not upper triangular matrix M has weight < n^2 -/
lemma weight_lt (M : NUT n 𝔽) : M.weight < n * n:=by
  sorry


/-- If weight M ≤ weight N then either M.J < N.J or M.J = N.J ∧ M.I ≤ N.I-/
lemma weight_le_weight (M N : NUT n 𝔽) (hle : M.weight ≤ N.weight) :
M.J < N.J ∨ (M.J = N.J ∧ M.I ≤ N.I) :=by
  sorry

/-
The next two lemmas are the key results that will allow us to prove that the algorithm will terminate
-/

/-- Swapping rows I and J increases the weight (if the corresponding diagonal entry is zero ) -/
lemma lt_weight_swap (M N : NUT n 𝔽) (hz : M M.J M.J = 0) (hN : N = M.val.swap M.I M.J) :
  M.weight < N.weight :=by
  sorry

/-- Subtracting the correct inverse multiple of row J from row I increases the weight
  (if the corresponding diagonal entry is non-zero ) -/
lemma lt_weight_sub_mul_inv (M N : NUT n 𝔽) (hz : M M.J M.J ≠ 0) (hN : N = M.val.sub_mul_inv M.I M.J) :
 M.weight < N.weight :=by
  sorry

/--
If M is not upper triangular then `GaussStep` is either a swap or a sub_mul_inv depending on
whether or not M j j = 0. If M is upper triangular it does nothing.  -/
@[reducible]
def GaussStep (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 := by
  by_cases hnut: M.nut
  · let N : NUT n 𝔽 := ⟨M,hnut⟩
    let i := N.I
    let j := N.J
    exact if M j j = 0 then M.swap i j else (M.sub_mul_inv i j)
  · exact M

section withM
variable {M : Matrix (Fin n) (Fin n) 𝔽}


/-
Our `weight` function is only defined for objects of type `NUT n 𝔽`.
We need a new version that is defined for all n x n matrices over 𝔽.

It will be convient to make this new ` weight' ` decrease at each GaussStep so we
define it be `n * n - weight M` for M not upper triangular and `0` otherwise
Note this weight is still bounded above by `n * n - 1` and below by `0` -/

/-- The weight' of a matrix -/
def weight' (M : Matrix (Fin n) (Fin n) 𝔽) : ℕ :=
if h : M.nut then (n * n - weight ⟨M, h⟩) else 0

/-- For any not upper triangular matrix a GaussStep strictly decreases weight' -/
lemma weight'_lt_of_GaussStep (hnut: M.nut) :
weight' (GaussStep M) < weight' M:=by
  sorry


end withM
open Function
/-
The next result is our main theorem (the other two theorems follow trivially from it).
-/
/-- If we iteratively apply `GaussStep` weight' M (or more) times then we obtain an upper triangular matrix -/
theorem GaussStep_steps_le_weight (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) (hk : weight' M ≤ k) :
(GaussStep^[k] M).ut :=by
  sorry

/-- So after `weight' M` steps the matrix is upper triangular -/
theorem GaussStep_term (M : Matrix (Fin n) (Fin n) 𝔽) : (GaussStep^[weight' M] M).ut :=by
  sorry

/-- In particular n² - 1 steps suffice to put M into upper triangular form -/
theorem upperbound_on_steps (M : Matrix (Fin n) (Fin n) 𝔽) : (GaussStep^[n*n-1] M).ut :=by
  sorry


/-
Possible extension(s):

1) Describe a function that computes the transition matrix P such that P*M is the upper triangluar
form of M (and prove that P is invertible).

2) Adapt the algorithm to compute the inverse of an invertible matrix

-/

end NUT
