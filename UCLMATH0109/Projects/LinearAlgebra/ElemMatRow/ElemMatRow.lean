import Mathlib.Tactic

/-
In this project we introduce the basic elementary row operations and corresponding
elementary matrices required for Gaussian elimination.

There versions of many of the results we saw for ℕ or groups that also
hold for matrices (of appropriate dimensions). Some of these are listed below.
Note they are ofter protected in the Matrix namespace (so you have to use their
full name e.g. `Matrix.one_mul`)

-/
open Matrix
#check Matrix.one_mul
#check Matrix.add_mul
#check Matrix.sub_mul

#check updateRow_apply

/-
When you need more results about matrix operations the best place to look is
`Mathlib.Data.Matrix.Basic` where you will find those listed above and much more.
-/

/- ------------------------------------------------------------------------------------------------
    Definitions of elementary row operations for m x n matrices
    and the corresponding elementary matrices
---------------------------------------------------------------------------------------------------/

namespace Matrix
variable {m n : ℕ} {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

/-- Add c * row j onto row i -/
@[reducible]
def add_mul_row (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m) (c : 𝔽) : Matrix (Fin m) (Fin n) 𝔽:=
  M.updateRow i (M i + (fun l => c * M j l))

/-- Swap rows i and j of the matrix M -/
@[reducible]
def swap (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m): Matrix (Fin m) (Fin n) 𝔽:=
 (M.updateRow i (M j)).updateRow j (M i)

/-- Swap rows i and j of the matrix M -/
@[reducible]
def mul_row (M : Matrix (Fin m) (Fin n) 𝔽) (i : Fin m) (c : 𝔽): Matrix (Fin m) (Fin n) 𝔽:=
 M.updateRow i (c•(M i))

/-- In Gaussian Elimination the following (special case of add_mul_row) is useful
(note that this only defined for square matrices here)
 `M.sub_mul_inv i j` is M with  i-th row equal to `(row i)-(M i j)* (M j j)⁻¹ *(row j)`  -/
@[simp]
def sub_mul_inv (M : Matrix (Fin n) (Fin n) 𝔽) (i j : Fin n) : Matrix (Fin n) (Fin n) 𝔽:=
  M.updateRow i (M i - (fun l => (M i j)* (M j j)⁻¹*(M j l)))


open StdBasisMatrix

#check stdBasisMatrix


/-- The elementary matrix corresponding to adding c * row i onto row j -/
def AddMul (i j : Fin m) (c : 𝔽) : Matrix (Fin m) (Fin m) 𝔽 := 1 + stdBasisMatrix i j c

/-- The elementary matrix Swap i j is the matrix such that left-multiplication swaps rows i and j -/
def Swap (i j : Fin m) : Matrix (Fin m) (Fin m) 𝔽:= 1 + (stdBasisMatrix i j 1) + (stdBasisMatrix j i 1) -
(stdBasisMatrix i i 1) - (stdBasisMatrix j j 1)

/-- The elementary matrix corresponding to multiplying row i by c -/
def MulRow (i : Fin m) (c : 𝔽) : Matrix (Fin m) (Fin m) 𝔽 := 1 + stdBasisMatrix i i (c-1)


/- ------------------------------------------------------------------------------------------------
      We now establish the basic properties of
      elementary row operations and matrices for m x n matrices.

      In particular showing that each operation is equivalent to
      left multiplication by the corresponding elementary matrix.
---------------------------------------------------------------------------------------------------/



/-- The k l entry of `M.add_mul_row i j c` is given by ... -/
lemma add_mul_row_apply (M : Matrix (Fin m) (Fin n) 𝔽) : (M.add_mul_row i j c) k l = if k = i then
(M i l  +  c * M j l) else M k l :=
by
  sorry


/-- The k l entry of the M.swap i j is given by ... -/
lemma swap_apply (M : Matrix (Fin m) (Fin n) 𝔽) :
(M.swap i j) k l = if k = j then M i l else (if k = i then M j l else M k l) :=
by
  sorry


/-- The k l entry of the M.mul_row i c is given by ... -/
lemma mul_row_apply (M : Matrix (Fin m) (Fin n) 𝔽) (i : Fin m)(c : 𝔽) :
(M.mul_row i c) k l = if k = i then c*(M i l) else  M k l :=
by
  sorry


/- If we swap row i with row i then nothing changes -/
lemma swap_same (M : Matrix (Fin m) (Fin n) 𝔽) (hij: i = j) : M.swap i j = M :=
by
  sorry


/-
The following only work for square matrices but we need them for m x n
-/
#check mul_left_apply_same
#check mul_left_apply_of_ne

@[simp]
theorem mul_left_apply_same' (i j : Fin m) (b : Fin n) (c : 𝔽) (M : Matrix (Fin m) (Fin n) 𝔽) :
    (stdBasisMatrix i j c * M) i b = c * M j b :=
by
  sorry

@[simp]
theorem mul_left_apply_of_ne' (i j a: Fin m) (b : Fin n) (h : a ≠ i) (c : 𝔽) (M : Matrix (Fin m) (Fin n) 𝔽) :
    (stdBasisMatrix i j c * M) a b = 0 :=
by
  sorry

/-- Left multiplication by Swap i j swaps rows i and j -/
lemma Swap_mul_left_eq  (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m): (Swap i j) * M = M.swap i j:=
by
  sorry


/-- Left multiplication by `AddMul i j c` adds `c * row j onto row i`-/
lemma AddMul_mul_left_eq (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m) (c : 𝔽)  : (AddMul i j c) * M = M.add_mul_row i j c:=
by
  sorry


/--Left multiplication by `AddMul i j c` adds `c * row i onto row j` -/
lemma MulRow_mul_left_eq (M : Matrix (Fin m) (Fin n) 𝔽) (i : Fin m) (c : 𝔽)  : (MulRow i c) * M = M.mul_row  i c:=
by
  sorry


/-- swapping twice gives back the original matrix -/
lemma swap_swap (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m) : (M.swap i j).swap i j = M :=
by
  sorry

/-- adding -c * row i to row j after adding c * row i on to row j gives back the original matrix -/
lemma add_mul_row_add_mul_row_neg (M : Matrix (Fin m) (Fin n) 𝔽) (i j : Fin m) (c : 𝔽) (hij : i ≠ j) :
(M.add_mul_row  i j c).add_mul_row i j (-c) = M :=
by
  sorry

/-- If you multiply row i by c ≠ 0 and then by c⁻¹ you get the original matrix back -/
lemma mul_row_mul_row_inv (M : Matrix (Fin m) (Fin n) 𝔽) (i : Fin m) (hc : c ≠ 0) : (M.mul_row i c).mul_row i c⁻¹ = M :=
by
  sorry

/-- Swap i j is its own inverse -/
lemma Swap_inv (i j : Fin m) : Swap i j * Swap i j = (1 : Matrix (Fin m) (Fin m) 𝔽):=
by
  sorry

/-- `AddMul i j -c` is the left inverse of `AddMul i j c`-/
lemma AddMul_left_inv (i j : Fin m) (hij : i ≠ j) (c : 𝔽): AddMul i j (-c) * AddMul i j (c) = (1 : Matrix (Fin m) (Fin m) 𝔽):=
by
  sorry

/-- `AddMul i j -c` is also the right inverse of `AddMul i j c`-/
lemma AddMul_right_inv (i j : Fin m) (hij : i ≠ j) (c : 𝔽) : AddMul i j (c) * AddMul i j (-c) = (1 : Matrix (Fin m) (Fin m) 𝔽):=
by
  sorry

/-- `MulRow i c⁻¹` is the left inverse of `MulRow i c` (for c ≠ 0)-/
lemma MulRow_left_inv (i  : Fin m) (c : 𝔽) (hc : c ≠ 0): MulRow i c⁻¹ * MulRow i  c = (1 : Matrix (Fin m) (Fin m) 𝔽):=
by
  sorry


/-- `MulRow i c⁻¹` is the right inverse of `MulRow i c` (for c ≠ 0)-/
lemma MulRow_right_inv (i : Fin m) (c : 𝔽) (hc : c ≠ 0): MulRow i c * MulRow i  c⁻¹ = (1 : Matrix (Fin m) (Fin m) 𝔽):=
by
  sorry

/-- In terms of standard elementary row operations sub_mul_inv is ...-/
lemma sub_mul_inv_eq  (M : Matrix (Fin m) (Fin m) 𝔽) (i j : Fin m) : M.sub_mul_inv i j =
M.add_mul_row  i j (-(M i j)*(M j j)⁻¹) :=
by
  sorry

/-- Left multiplication of `M` by `AddMul  j i (-(M i j)*(M j j)⁻¹)` equals `M.sub_mul_inv i j`  -/
lemma sub_mul_inv_equiv_left_mul (M : Matrix (Fin m) (Fin m) 𝔽) (i j : Fin m) :  AddMul i j (-(M i j)*(M j j)⁻¹) * M = M.sub_mul_inv i j :=
by
  sorry


/-!

Possible extension: start the Gaussian Elimination project
making use of these results about elementary matrices.

-/
