import Mathlib.Tactic
import UCLMATH0109.Projects.LinearAlgebra.GaussElim.Inverse



variable {𝔽 : Type} {n : ℕ} [Field 𝔽] [DecidableEq 𝔽]

open Matrix Finset BigOperators

-------------------------------------------------------------------------------
/-
In this file we prove a criterion for invertibility of a matrix M over a field 𝔽.

  `invertible_iff`

  M is invertible iff the upper triangular matrix obtained by Gaussian elimination has
  no zeros on its leading diagonal.

We have already proved sufficiency so we now need to prove necessity.

We first prove that if M is invertible then the only solution to M*B = 0 is  B = 0.

Let M be an n x n matrix over 𝔽. We form the matrix `G = M.GaussUt` which is the
result of applying Gaussian elimination to M to obtain an upper-triangular matrix.

We now suppose that G has a zero on its diagonal. So we can define `k : Fin n` to be the index
 of the 1st zero on the diagonal of G.

We form (an invertible) block n x n matrix `G.Block k` which will agree with G on the columns before
k and agrees with the identity matrix on the columns from k onwards.

#     G.Block k  =   | Gₖ |   0  |
#                    | 0  | Iₙ₋ₖ |

This is invertible (since it is upper triangular and has no zeros on its leading diagonal)
and its inverse is `N := (G.Block k).Inverse`

We then define  `x` to be  the (non-zero) vector given by:
`xᵢ = -(N*G) i k` for i < k, `xₖ = 1` and `xᵢ = 0` for k < i.

We can check that the first k columns of `N * G` agree with the identity matrix while
 column `k` of `N * G` equals `-xᵢ` for `i < k` and `0` otherwise.

This implies that `(N*G)*x = 0`

Since `N` is invertible this implies that `G` is not invertible, and so when applied
to `G = U * M`, with `U` invertible establishes that `M` is not invertible.
(In our application `U` will be the transition matrix putting M into upper-triangular
 form via the Gauss Step algorithm.)

We then prove that computing `x` above with `G = M.GaussUt` gives a non-trivial zero
solution to `M * x = 0` proving that `M` is not invertible.

See pdf for details and an example.
-/


#check updateRow_apply
#check Matrix.one_mul
#check Matrix.add_mul
#check Matrix.sub_mul



/--
If A is invertible and A * B = 0 then B = 0, where B can be any matrix with n rows and a finite number of columns
-/
lemma mul_zero_invertible  {cols : Type} [Fintype cols] (M : Matrix (Fin n) (Fin n) 𝔽) (hM : M.invertible) (B : Matrix (Fin n) cols 𝔽) (hz: M * B = 0) : B = 0:=
by
  sorry

/-- The block matrix `M.Block k` is defined to agree with M on columns j < k and to agree with the identity on columns k onwards -/
@[reducible]
def Matrix.Block (M : Matrix (Fin n) (Fin n) 𝔽) (k : Fin n) : Matrix (Fin n) (Fin n) 𝔽 :=
Matrix.of (fun i j => if (j < k) then (M i j) else (if (i = j) then 1 else 0))

/-- M.Block k agrees with M on columns j < k -/
@[simp]
lemma Block_lt_apply {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (i j : Fin n) (hlt : j < k) :
(M.Block k) i j = M i j:=
by
  sorry

/-- M.Block k is zero in any non-diagonal entry in columns k onwards-/
@[simp]
lemma Block_le_ne_apply {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (i j : Fin n) (hlt : ¬j < k) (hij : i ≠ j) :
(M.Block k) i j = 0:=
by
  sorry

/-- M.Block k is one in any diagonal entry in columns k onwards-/
@[simp]
lemma Block_le_eq_apply {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (i j : Fin n) (hlt : ¬j < k) (hij : i = j) :
(M.Block k) i j = 1:=
by
  sorry

/-- If M is upper triangular then so is M.Block k -/
@[simp]
lemma Block_ut {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) : (M.Block k).ut:=
by
  sorry

/-- If M has no zero diagonal entry before column k then M.Block k is non-zero-diagonal -/
@[simp]
lemma Block_no_zero_on_diag {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hnz: ∀ i, i < k → M i i ≠ 0) : (M.Block k).no_zero_on_diag :=
by
  sorry

/-
At this point we need to use some of the Gaussian elimination and Inverse code
-/
open NUT
#check GaussStep
#check inverse_spec_no_zero_on_diag

/-- If M is uppertriangular and has no zeros on the diagonal before column k then M.Block k has a computable inverse -/
lemma Block_invertible  {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0) :
(M.Block k) * (M.Block k).Inverse = 1 ∧ (M.Block k).Inverse * (M.Block k) = 1  :=
by
  sorry

------------------- ASIDE: filters and sums
/-

When evaluating matrix multiplications we inevitably need to consider sums. These sums will often
involve matrices whose definition in turn depends on whether a row or column index is < or = to
some particular value so we  want to split these sums at a particular index.

One way to do this is with
-/
#check sum_filter_add_sum_filter_not
/-
This splits a sum based on a predicate p, which in our case will typically be of the form
`(fun x => x < k)` ie the predicate that is true iff x < k

This will split a sum into two parts

`∑ i in univ, f i = ∑ i < k, f i  + ∑  k ≤ i, f i`

Often these sums will be zero, since they consist of terms that are all zero. If this is the
case then we can use
-/
#check sum_eq_zero
/-

In other cases a sum may have a single non-zero term, in which case we may be able to use one or other of
-/
#check sum_eq_single_of_mem
#check sum_eq_single

/-
These sums will be using Finsets so rather than summing over a `Set` such as `{ x ∈ Fin n | x < k}`
we will sum over  `(univ : Finset (Fin n)).filter (fun x => x < k)` which is the Finset of all `Fin n`
 `filtered` according to being less than k. For this reason we introduce a few simplication lemmas for
 relevant filtered Finsets.
-/

/-- The set of Fin n satisfying k ≤ i and i = k is just {k} -/
lemma filter_le_of_eq (k : Fin n) : (univ : Finset (Fin n)).filter (fun i => k ≤ i ∧  i = k) = {k}:=
by
  sorry

/-- The set of Fin n satisfying i ≤ k and ¬i < k is just {k} -/
lemma filter_not_lt_of_le (k : Fin n) : (univ : Finset (Fin n)).filter (fun i =>i ≤ k ∧ ¬i < k) = {k}:=
by
  sorry

/-- The set of Fin n satisfying i ≤ k and i < k is just the the set satisfying i < k  -/
lemma filter_le_and_lt (k : Fin n) : filter (fun i => i ≤ k ∧ i < k) = filter (fun i => i < k) :=
by
  sorry


/-- Split a sum over Fin n into i < k and ¬ i < k -/
lemma sum_split_lt (k : Fin n) {f : Fin n → 𝔽} : ∑ i in s, f i =
∑ i in s.filter (fun i => i < k),f i + ∑ i in s.filter (fun i => ¬ i < k),f i :=
by
  sorry

/-- Split a sum over Fin n into i ≤ k and ¬ i ≤ k -/
lemma sum_split_le (k : Fin n) {f : Fin n → 𝔽} : ∑ i in s, f i =
∑ i in s.filter (fun i => i ≤ k),f i + ∑ i in s.filter (fun i => ¬ i ≤ k),f i :=
by
  sorry


/-- Split a sum over Fin n into i < k, i = k  and  k < i -/
lemma sum_split_at_mem (k : Fin n) (h: k ∈ s) {f : Fin n → 𝔽} : ∑ i in s, f i =
∑ i in s.filter (fun i => i < k), f i + f k +  ∑ i in s.filter (fun i => k < i ),f i :=
by
  sorry

---------------------- Back to Matrices

/-- The inverse of the Block matrix is zero in the first k columns from row k down -/
@[simp]lemma Block_inverse_is_block {M : Matrix (Fin n) (Fin n) 𝔽} {i j k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0)
(hij : k ≤ i) (hjk : j < k): (M.Block k).Inverse i j = 0:=
by
  sorry

/-- The first k columns of B⁻¹ * M are the same as B⁻¹* B = 1 -/
@[simp]lemma Block_inverse_mul_left_apply  {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0)
(i j : Fin n) (hjk : j < k): ((M.Block k).Inverse * M) i j = if (i = j) then 1 else 0:=
by
  sorry

/-- The first k diagonal entries of B⁻¹ * M are 1 -/
@[simp]lemma Block_inverse_mul_left_same_apply  {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0)
(j : Fin n) (hjk : j < k): ((M.Block k).Inverse * M) j j = 1:=
by
  sorry


/-- The first k columns of B⁻¹ * M are zero off the diagonal -/
@[simp]lemma Block_inverse_mul_left_ne_apply  {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0)
(i j : Fin n) (hjk : j < k) (hij : i ≠ j): ((M.Block k).Inverse * M) i j = 0:=
by
  sorry

/-- column k of B⁻¹ * M has zeros from row k down-/
@[simp]
lemma Block_inverse_mul_col  {M : Matrix (Fin n) (Fin n) 𝔽} {k : Fin n} (hut: M.ut) (hnz: ∀ i, i < k → M i i ≠ 0) (hkz : M k k = 0)
(i : Fin n) (hik : k ≤ i) : ((M.Block k).Inverse * M) i k = 0:=
by
  sorry



variable [NeZero n]

/-- For a matrix with a zero on the diagonal this returns the index of the first zero-/
def Matrix.fz (M : Matrix (Fin n) (Fin n) 𝔽)  : Fin n:=
by
  by_cases hninv : M.no_zero_on_diag
  · exact 0 --- This is where we need [NeZero n] because Fin 0 is empty so there is nothing to return
  · let _Z : Finset (Fin n):=(univ : Finset (Fin n)).filter (fun i =>  M i i = 0)
    rw [no_zero_on_diag] at hninv; push_neg at hninv
    have Zne: _Z.Nonempty
    · obtain ⟨i,hiz⟩:=hninv
      refine ⟨i, mem_filter.2 ⟨mem_univ _ ,hiz⟩⟩
    exact _Z.min' Zne

/-- If M has a zero on its diagonal then `M M.fz M.fz = 0` -/
lemma fz_zero (M : Matrix (Fin n) (Fin n) 𝔽) (hninv : ¬M.no_zero_on_diag) :
M (M.fz)  (M.fz) = 0:=
by
  sorry

/--M never has a zero on the diagonal before the first zero  -/
lemma fz_first (M : Matrix (Fin n) (Fin n) 𝔽)  (hi: i < M.fz):
 M i i ≠ 0:=
by
  sorry

/-
In our definition of the column vector `Matrix.x` below,  `x` is an (n x 1) matrix over 𝔽.

Hence `G.x i`, which we would think of as the ith entry of x (so of type 𝔽), is of type `Unit → 𝔽`,
and equal to the constant function from the type with one element (Unit) to the element of 𝔽
given in the definition.
-/

/-- A non-trivial zero of G if G is not invertible -/
@[reducible]
def Matrix.x (G : Matrix (Fin n) (Fin n) 𝔽) : Matrix (Fin n) Unit 𝔽 :=
(fun i  _  => if i < G.fz then -((G.Block G.fz).Inverse * G) i G.fz else (if i = G.fz then 1 else 0))

@[simp]
lemma x_eq  (G : Matrix (Fin n) (Fin n) 𝔽): G.x = (fun i  _ => if i < G.fz then -((G.Block G.fz).Inverse * G) i G.fz else (if i = G.fz then 1 else 0)):=
by
  sorry

@[simp]
lemma x_eq_lt (G : Matrix (Fin n) (Fin n) 𝔽) (hi : i < G.fz): G.x i  = (fun _ => -((G.Block G.fz).Inverse * G) i G.fz) :=
by
  sorry

/-- Entries of x below G.fz are all zero -/
@[simp]
lemma x_zero_apply (G : Matrix (Fin n) (Fin n) 𝔽) (hkc: G.fz < i) : G.x i  = 0:=
by
  sorry

/-- The entry at G.fz is 1-/
@[simp]
lemma x_one_apply (G : Matrix (Fin n) (Fin n) 𝔽) : G.x G.fz  = 1:=
by
  sorry

/-- x is never the zero vector -/
lemma x_ne_zero (G : Matrix (Fin n) (Fin n) 𝔽) : G.x ≠ 0:=
by
  sorry


/-- This is a big computation .... -/
lemma Block_mul_non_triv (G : Matrix (Fin n) (Fin n) 𝔽)  (hut: G.ut) (hninv : ¬G.no_zero_on_diag) :
∃ (N : Matrix (Fin n) (Fin n) 𝔽),  N.invertible ∧ (N * G) * G.x = 0 :=
by
  sorry

/-- If M in not invertible then M.GaussUt.x is a non-trivial zero of M -/
theorem x_is_nontrivial_zero (M: Matrix (Fin n) (Fin n) 𝔽) (hninv : ¬ M.GaussUt.no_zero_on_diag) :
 M * (M.GaussUt.x)  = 0 ∧  M.GaussUt.x ≠ 0:=
by
  sorry

/-- A matrix is invertible iff the upper-triangular matrix obtained by Gauss elimination has no zero diagonal entries-/
theorem invertible_iff (M : Matrix (Fin n) (Fin n) 𝔽) : M.invertible ↔ M.GaussUt.no_zero_on_diag:=
by
  sorry

/-- Hence, whether or not a matrix is invertible is decidable -/
instance (M : Matrix (Fin n) (Fin n) 𝔽 ): Decidable M.invertible :=
by
  sorry

/-!
Possible extension: give some examples of deciding invertibility of small matrices
using the code in this project.
-/
