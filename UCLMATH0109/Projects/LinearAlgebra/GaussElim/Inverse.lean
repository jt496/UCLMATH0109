import Mathlib.Tactic
import UCLMATH0109.Projects.LinearAlgebra.GaussElim.GaussStep



/-

The aim of this project is to describe an algorithm that computes the
inverse of a matrix, or outputs 0 if the matrix is not invertible.

See pdf for details.
-/


variable {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]

open Matrix Finset BigOperators

#check Matrix.one_mul
#check Matrix.add_mul
#check Matrix.sub_mul
#check updateRow_apply



/-- A matrix M is invertible iff it has a two-sided inverse -/
@[reducible]
def Matrix.invertible (M : Matrix (Fin n) (Fin n) 𝔽) : Prop := ∃ N, M * N = 1 ∧ N * M = 1


/-- If M and N are invertible then so is M * N -/
lemma mul_invertible {M N: Matrix (Fin n) (Fin n) 𝔽} (hM : M.invertible) (hN : N.invertible) : (M*N).invertible:=
by
  sorry

/-- M is invertible iff its transpose is invertible -/
lemma transpose_invertible_iff {M : Matrix (Fin n) (Fin n) 𝔽} : M.invertible ↔ Mᵀ.invertible :=
by
  sorry

/-- A Matrix M is lower triangular iff ∀ i < j, M i j = 0 or equivalently Mᵀ is upper
triangular -/
@[reducible]
def Matrix.lwt (M : Matrix (Fin n) (Fin n) 𝔽) : Prop := ut Mᵀ

/-- M is upper triangular iff Mᵀ is lower triangular-/
lemma ut_iff_transpose_lwt {M : Matrix (Fin n) (Fin n) 𝔽} : M.ut ↔ Mᵀ.lwt :=
by
  sorry

/-- Being lower triangular is decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽) : Decidable M.lwt:=inferInstance

/-- M is no_zero_on_diag iff all diagonal entries are non-zero -/
@[reducible]
def Matrix.no_zero_on_diag (M : Matrix (Fin n) (Fin n) 𝔽) :Prop:= ∀ i, M i i ≠ 0

/-- M has no zero diagonal entries iff Mᵀ does -/
lemma no_zero_on_diag_iff_transpose (M : Matrix (Fin n) (Fin n) 𝔽) : M.no_zero_on_diag ↔  Mᵀ.no_zero_on_diag:=
by
  sorry

/-- M is diagonal iff all off-diagonal entries are zero-/
@[reducible]
def Matrix.is_diagonal (M : Matrix (Fin n) (Fin n) 𝔽) :Prop:= ∀ i j, i ≠ j → M i j = 0

/-- Being diagonal is decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽) : Decidable M.is_diagonal :=inferInstance


/-- M is diagonal iff Mᵀ is diagonal -/
lemma is_diagonal_iff_transpose (M : Matrix (Fin n) (Fin n) 𝔽) : M.is_diagonal ↔ Mᵀ.is_diagonal :=
by
  sorry

/-- The transpose of a diagonal matrix is itself -/
lemma transpose_eq_diagonal {M : Matrix (Fin n) (Fin n) 𝔽} (hd: M.is_diagonal) : M = Mᵀ:=
by
  sorry

/-- M is diagonal iff it is upper and lower triangular-/
lemma is_diagonal_iff_ut_and_lwt (M : Matrix (Fin n) (Fin n) 𝔽) : M.is_diagonal ↔ M.ut ∧ M.lwt :=
by
  sorry

/-- Having no zeros on the diagonal is decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽) : Decidable M.no_zero_on_diag:=inferInstance

/-- If a diagonal matrix is invertible then its diagonal entries are non-zero -/
lemma diagonal_invertible {M : Matrix (Fin n) (Fin n) 𝔽} (hd : M.is_diagonal) (hinv: M.invertible) : M.no_zero_on_diag :=
by
  sorry

/-- The inverse of a diagonal matrix is ... -/
def Matrix.InverseDiag (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
diagonal (fun i => (M i i)⁻¹)

/-- M.InverseDiag is the inverse of M if M is diagonal and has no zeros on its diagonal -/
lemma InverseDiag_spec {M : Matrix (Fin n) (Fin n) 𝔽} (hd : M.is_diagonal) (hdnz: M.no_zero_on_diag) :
 M * M.InverseDiag = 1 ∧ M.InverseDiag * M = 1 :=
by
  sorry



open NUT
/-
In order to invert a matrix M we will compute `G = GaussStep^[weight' M] M` (this is GaussStep iterated `weight' M` times)
and then compute  `H = GaussStep^[weight' Gᵀ] Gᵀ`

We will refer to this as `GaussUt` since it is the forward part of standard Gaussian elimination
-/
@[reducible]
def Matrix.GaussUt (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=GaussStep^[n*(n+1)] M

lemma GaussUt'  (M : Matrix (Fin n) (Fin n) 𝔽) : M.GaussUt = GaussStep^[n*(n+1)] M :=
by
  sorry


/-
Note that G is upper triangular so Gᵀ is lower triangular. Moreover, if M is invertible
then the G has no zero entry on its diagonal and hence neither does Gᵀ.

If you check how GaussStep works you see that this implies that GaussStep (Gᵀ)
will use only `sub_mul_inv` steps (the `swap` step will not be used).

We need to check that as we apply repeated GaussSteps, the matrices remain lower triangular
and hence we never perform a `swap` step.
-/

/-- If M is lower triangular then so is M.sub_mul_inv i j for j < i -/
lemma sub_mul_inv_lwt {M : Matrix (Fin n) (Fin n) 𝔽} (hlwt : M.lwt ) (hij: j < i) : (M.sub_mul_inv i j).lwt :=
by
  sorry

/-
We check next that the diagonal entries do not change
-/

/-- If M is lower triangular and then applying sub_mul_inv i j , j < i does not change the diagonal -/
lemma sub_mul_inv_diag_eq {M : Matrix (Fin n) (Fin n) 𝔽} (hlwt : M.lwt ) (hij: j < i) (a : Fin n): (M.sub_mul_inv i j) a a = M a a :=
by
  sorry

/-- If M is lower triangular and no_zero_on_diag then so is M.sub_mul_inv i j for j < i -/
lemma sub_mul_inv_no_zero_on_diag {M : Matrix (Fin n) (Fin n) 𝔽} (hlwt : M.lwt ) (h: M.no_zero_on_diag) (hij: j < i) :
 (M.sub_mul_inv i j).no_zero_on_diag :=
by
  sorry


/-- If M is lower triangular and has non-zero diagonal then so is GaussStep M -/
lemma GaussStep_of_lwt_no_zero_on_diag {M : Matrix (Fin n) (Fin n) 𝔽} (hlwt : M.lwt ) (hdnz : M.no_zero_on_diag) : (GaussStep M).lwt ∧ (GaussStep M).no_zero_on_diag:=
by
  sorry

/-- If M is lower triangular and has non-zero diagonal then so is GaussStep^[k] M for any k-/
lemma GaussStep_of_lwt_no_zero_on_diag_iterate {M : Matrix (Fin n) (Fin n) 𝔽} (hlwt : M.lwt ) (hdnz : M.no_zero_on_diag) (k : ℕ):
(GaussStep^[k] M).lwt ∧ (GaussStep^[k] M).no_zero_on_diag:=
by
  sorry


/-
Our next goal is to compute the matrices corresponding to the GaussSteps
-/

/-- The elementary matrix corresponding to the next GaussStep step -/
def GaussStepMat (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
by
  by_cases hnut: M.nut
  · let M' : NUT n 𝔽 := ⟨M,hnut⟩
    let i := M'.I
    let j := M'.J
    exact if M j j = 0 then Swap i j else  AddMul i j (-(M i j)*(M j j)⁻¹)
  · exact 1

/-- If M is nut and the diagonal entry is zero then the GaussStepMat is Swap I J -/
lemma GaussStepMat_nut_zero (M : NUT n 𝔽) (hz : M.mat M.J M.J = 0) : GaussStepMat M.mat = Swap M.I M.J:=
by
  sorry

/-- If M is nut and the diagonal entry is zero then the GaussStepMat is E I J c for an explicit value of c -/
lemma GaussStepMat_nut_non_zero (M : NUT n 𝔽) (hz : M.mat M.J M.J ≠ 0) : GaussStepMat M.mat = AddMul M.I M.J (-(M.mat M.I M.J)*(M.mat M.J M.J)⁻¹):=
by
  sorry

/-- If M is upper triangular then the GaussStepMat is the identity-/
lemma GaussStepMat_ut (M : Matrix (Fin n) (Fin n) 𝔽) (hut : ¬ M.nut) : GaussStepMat M = 1:=
by
  sorry

/-- Applying GaussStep to M is the same as left multiplication by GaussStepMat M -/
lemma GaussStepMat_spec (M : Matrix (Fin n) (Fin n) 𝔽)  : GaussStep M = (GaussStepMat M) * M :=
by
  sorry


/-- All the matrices output by GaussStep algorithm are invertible  -/
lemma GaussStepMat_invertible (M : Matrix (Fin n) (Fin n) 𝔽)  : (GaussStepMat M).invertible:=
by
  sorry


/-- The kth GaussStep iterated matrix is the product of the first k GaussStep_matrices
so  (M.GaussStepIterMat k) * M = GaussStep^[k] M -/
def Matrix.GaussStepIterMat (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) : Matrix (Fin n) (Fin n) 𝔽 :=
by
  induction k with
  | zero => exact 1 -- the identity
  | succ k Mk => exact (GaussStepMat (GaussStep^[k] M)) * Mk -- Mk is the matrix for k steps

/-- The 0th GaussStepIterMat is the identity -/
@[simp]
lemma GaussStepIterMat_zero  (M : Matrix (Fin n) (Fin n) 𝔽) : M.GaussStepIterMat 0 = 1:=
by
  sorry

/-- The (k+1)th GaussStepIterMat is the product of the GaussStep matrix for the (k+1)th step and
the kth GaussStepIterMat -/
@[simp]
lemma GaussStepIterMat_succ  (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) : M.GaussStepIterMat (k + 1) =
GaussStepMat (GaussStep^[k] M) * M.GaussStepIterMat k :=
by
  sorry

/--(M.GaussStepIterMat k) * M = GaussStep^[k] M -/
lemma GaussStepIter_spec (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) : (M.GaussStepIterMat k) * M = GaussStep^[k] M:=
by
  sorry


/-- All the matrices output by GaussStep algorithm are invertible  -/
lemma GaussStepIter_invertible (M : Matrix (Fin n) (Fin n) 𝔽) (k : ℕ) :
 (M.GaussStepIterMat k).invertible:=
by
  sorry


/-
Given M, `M.GaussDiag = M.GaussUtᵀ.GaussUt`

So `M.GaussDiag` is the result of applying GaussStep to termination to M then applying
 GaussStep to termination to the transpose of the result.

Note that in general `M.GaussDiag` will not be diagonal, but we will prove that it is diagonal
 if `M.GaussUt` has no zeros on its diagonal.
-/

/-- Apply the GaussStep iteration to termination to M and then repeat with the transpose of the resulting matrix-/
def Matrix.GaussDiag (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
    M.GaussUtᵀ.GaussUt

/-- If `M.GaussUt` has no zeros on its diagonal then `M.GaussDiag` is a diagonal matrix
with no zeros on its diagonal -/
lemma ut_no_zero_on_diag_diagonal (M : Matrix (Fin n) (Fin n) 𝔽) (hnz: M.GaussUt.no_zero_on_diag ):
 M.GaussDiag.is_diagonal ∧ M.GaussDiag.no_zero_on_diag:=
by
  sorry


/-- We define U to be the transition matrix that puts M into its `M.GaussUt` upper triangular form by left multiplication -/
def Matrix.U (M : Matrix (Fin n) (Fin n) 𝔽) :  Matrix (Fin n) (Fin n) 𝔽 :=M.GaussStepIterMat (n*(n+1))

/-- U * M is the upper triangular form of applying GaussStep to M -/
lemma U_spec (M : Matrix (Fin n) (Fin n) 𝔽) : M.U * M = M.GaussUt:=
by
  sorry

/-- L is the transition matrix that puts M into diagonal form (if invertible) -/
def Matrix.L (M : Matrix (Fin n) (Fin n) 𝔽) :  Matrix (Fin n) (Fin n) 𝔽 := (M.U * M)ᵀ.U

/-- The key equation relating M.GaussDiag with Mᵀ, M.Uᵀ and M.L -/
lemma GaussDiag_eq (M : Matrix (Fin n) (Fin n) 𝔽) : M.GaussDiag = M.L * Mᵀ * M.Uᵀ :=
by
  sorry

/-- The key equation relating M.GaussDiagᵀ  with M, M.U and M.Lᵀ -/
lemma UMLT (M : Matrix (Fin n) (Fin n) 𝔽) :  M.U * M * M.Lᵀ  = M.GaussDiagᵀ   :=
by
  sorry

/- To compute the inverse of M we first apply GaussStep to get an ut matrix `G = M.GaussUt`.
If this has a zero on the diagonal then the matrix is not invertible so we output 0
otherwise we apply GaussStep to Gᵀ to get a diagonal matrix
 `M.GaussDiag = M.GaussUtᵀ.GaussUt` that still has no zeros on its diagonal and hence can
 easily be inverted: as `M.Inverse = M.Lᵀ * M.GaussDiag.InverseDiag* M.U` -/

/-- The computable inverse of M (when M is invertible)-/
def Matrix.Inverse  (M : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) (Fin n) 𝔽 :=
if M.GaussUt.no_zero_on_diag then (M.Lᵀ * M.GaussDiag.InverseDiag* M.U) else 0

/-- If `M.GaussUt`  has no zeros on its diagonal then M.Inverse is the computable inverse of M -/
lemma inverse_spec_no_zero_on_diag {M : Matrix (Fin n) (Fin n) 𝔽} (hnz : M.GaussUt.no_zero_on_diag) :
M * M.Inverse = 1 ∧ M.Inverse * M = 1 :=
by
  sorry

/--  If `M.GaussUt`  has no zeros on its diagonal then M is invertible -/
lemma is_invertible {M : Matrix (Fin n) (Fin n) 𝔽} (hnz : M.GaussUt.no_zero_on_diag) :
  M.invertible:=
by
  sorry


/-!
Possible extension: deal with the case when M is not invertible
(see project NotInvertible for details).
-/
