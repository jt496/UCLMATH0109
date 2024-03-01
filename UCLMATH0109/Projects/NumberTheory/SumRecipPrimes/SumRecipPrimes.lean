import Mathlib.Tactic.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Classical

open Nat hiding pow_succ' mul_le_mul_left mul_le_mul_right pow_zero add_div add_le_add
open Finset


/-
Main result of project:

# The sum of the reciprocals of the primes less than 2⁴ᵐ + 1 is at least log (m + 1/2)
-/

/-
Throughout we will need basic rewriting lemmas about membership of Finsets.
These all follow a standard pattern: -/

#check mem_range
#check mem_powerset
#check mem_Ioo
#check mem_filter

/-- The primes < n -/
def Nat.PrimesLt (n : ℕ) : Finset ℕ :=
 (range n).filter (fun p => Nat.Prime p)

#check PrimesLt 20
#eval PrimesLt 20

@[simp]
lemma PrimesLt_zero : PrimesLt 0 = ∅ :=
by
  sorry

/-- rw mem of Primes < n -/
lemma mem_PrimesLt {n x : ℕ} : x ∈ n.PrimesLt ↔ x < n ∧ Nat.Prime x :=
by
  sorry

/-- A is a subset of the primes less than n iff ...-/
lemma subset_PrimesLt {n : ℕ} {A : Finset ℕ} : A ⊆ n.PrimesLt ↔ ∀ a ∈ A, a < n ∧ a.Prime:=
by
  sorry

/-- A natural number n is Squarefree iff the only square that divides it is 1
 Squarefree nats < n -/
def Nat.SqFreesLt (n : ℕ) : Finset ℕ:=
 (range n).filter (fun a => Squarefree a)


#check SqFreesLt 20
#eval SqFreesLt 20

/-- rw mem of squarefree n-/
lemma mem_SqFreesLt (n : ℕ) {x : ℕ} : x ∈ n.SqFreesLt  ↔ x < n  ∧ Squarefree x :=
by
  sorry

/-- SqFreeLt a ⊆ SqFreeLt b for a ≤ b -/
lemma SqFreesLt_mono (h : a ≤ b) : SqFreesLt a  ⊆ SqFreesLt b  :=
by
  sorry

/-- 1 ∈ SqFreesLt n for 2 ≤ n -/
lemma one_mem_SqFreesLt (h : 2 ≤ n) : 1 ∈ n.SqFreesLt  :=
by
  sorry

#check not_squarefree_zero

/-- If k ∈ SqFreesLt n then 0 < k -/
lemma pos_of_mem_SqFreesLt {n k : ℕ} (hk: k ∈ n.SqFreesLt) : 0 < k :=
by
  sorry

#check sq_mul_squarefree
/-- The decomposition of `n : ℕ` into `(a , b) : ℕ × ℕ` such that `a * b² = n`
with `a` squarefree -/
noncomputable -- This uses `choice` so is noncomputable
def Nat.decomp : ℕ → ℕ × ℕ :=
by
  intro n
  let a:= n.sq_mul_squarefree.choose
  let b:= n.sq_mul_squarefree.choose_spec.choose
  exact (a,b)

/-- The 1st part of the decomp is squarefree -/
lemma decomp_sqfree (n : ℕ) : Squarefree n.decomp.1 :=
by
  sorry

/-- The defining property of the decomp function -/
lemma decomp_mul_sq  (n : ℕ) : n.decomp.1 * n.decomp.2 ^ 2 = n:=
by
    sorry

/-- decomp as an embedding (it is injective) -/
noncomputable
def Nat.decomp' : ℕ ↪ ℕ × ℕ where
toFun := decomp
inj' :=
by
  sorry


/-- {1,...,n-1} ⊆ {0,..,n-1} -/
lemma Ioo_subset_range {n : ℕ} : Ioo 0 n ⊆ range n:=
by
  sorry

#check le_mul_of_pos_left

/-- If 0 < k then both parts of decomp k are at most k -/
lemma decomp_pos {k : ℕ} (hkpos : 0 < k) : k.decomp'.1 ≤ k ∧ k.decomp'.2 ≤ k :=
by
  sorry


/--
The (injective) image of `decomp` applied to {1,..,n-1} is contained in the
cartesian product of SqFreesLt n and range n
-/
lemma subset_decomp {n : ℕ} : (Ioo 0 n).map decomp' ⊆ n.SqFreesLt ×ˢ range n :=
by
  sorry


section with_f

#check MonoidWithZeroHom -- the type of multiplicative homomorphisms that send 0 to 0

variable (f : ℕ →*₀ ℝ) (hfnonneg : ∀ x, 0 ≤ f x)

/-- The sum of f k over SqFreesLt 2 equals 1 -/
lemma sum_SqFrees_two_eq (f : ℕ →*₀ ℝ): ∑ k in SqFreesLt 2, f k = 1:=
by
  sorry

-- Given `k : ℕ`, k.factors is the prime factorisation of k as a List ℕ.
-- Given a list l , l.toFinset is the Finset given by removing duplicates.
#check factors_unique -- a version of the Fundamental theorem of arithmetic.
/-
If the product of a list l of primes equals n then, `l ~ factors n`
i.e. l is a permutation of the prime factorisation of n
[Note that `~` is not a special character it is on your keyboard!]
-/
/-
The next two results involve a certain amount of converting between
a Lists and Finsets. Note that we haven't opened the `List` namespace.
-/
#check List.map_id
#check prod_to_list
#check mem_toList
#check toList_toFinset
#check List.toFinset_eq_of_perm
/--
If A is a Finset of primes and ∏ p in A, p = k then A = k.factors.toFinset
-/
lemma prod_inj_on_PrimesLt {n : ℕ}{A : Finset ℕ} (k : ℕ) (hA : A ∈ n.PrimesLt.powerset)
(hk: k = A.prod id) : A = k.factors.toFinset:=
by
  sorry

#check prod_factors_toFinset_of_squarefree
#check List.mem_toFinset
#check prime_of_mem_factorization

/-- Any squarefree less than n is the product of a subset of the primes less than n -/
lemma sqFreesLt_subset_prod_primesLt (n : ℕ) : n.SqFreesLt ⊆ n.PrimesLt.powerset.image (fun B => B.prod id):=
by
  sorry

/-
We now want to use `log` and `exp` so we open the `Real` namespace.
-/
open Real

#check log_le_iff_le_exp
#check sum_le_sum_of_subset_of_nonneg
#check sum_image
#check prod_add
#check prod_le_prod
#check add_one_le_exp
#check exp_sum

/--
The log of the sum of f over squarefrees < n is at most the sum of f over primes < n.
-/
theorem log_sum_SqFreesLt_le_sum_PrimesLt (hn : 2 ≤ n) :
log (∑ k in n.SqFreesLt, f k) ≤ ∑ p in n.PrimesLt, f p :=
by
  sorry


#check sum_subset
#check sum_mul_sum
#check decomp'
#check sum_map

/--
The sum of f over range n is at most the product of the sum of SqFreesLt n and the
sum of the squares
-/
theorem sum_range_le_sumSF_mul_sumSq :
∑ k in range n, f k ≤ (∑ a in n.SqFreesLt, f a) * (∑ b in range n, f b^2):=
by
  sorry

end with_f

/-- The basic telescopic sum formula:
∑ k < n, 1/(k+1)(k+2) = n / (n+1) -/
lemma sum_telescope_eq (n : ℕ) : ∑ k in range n, ((k+1)*(k+2) : ℝ)⁻¹ = n / (n+1) :=
by
  sorry

/-- The sum of reciprocals of squares is ≤ 2 -/
theorem sum_inv_sq_le_two {n : ℕ} : ∑ k in range n,  ((k : ℝ)⁻¹)^2 ≤ 2 :=
by
  sorry

#check card_eq_sum_ones
#check mul_sum
#check sum_le_sum

/-- Given a lower bound b ≤ f x on a Finset S, we have a lower bound for the sum of f over S -/
lemma lb_mul_card_le_sum {S : Finset ℕ} {f : ℕ → ℝ} (lb : ∀ i, i ∈ S → b ≤ f i) : b * S.card ≤ ∑ i in S, f i :=
by
  sorry


/-- The sum of 1/k over {2^k+1,...,2^(k+1)} is at least 1/2 -/
lemma half_le_sum_inv_nat_Ico (k : ℕ): 1 / 2 ≤ ∑ i in Ico (2^k+1) (2^k.succ + 1), (i : ℝ)⁻¹ :=
by
  sorry

/-- The harmonic series ≤ 2^m  is at least m / 2 + 1 -/
theorem sum_inv_pow_two (m : ℕ) : m / 2 + 1 ≤ ∑ k in range (2^m+1),(k : ℝ)⁻¹ :=
by
  sorry

/--
We define `inv` to be reciprocal function `fun (n : ℕ) => (n : ℝ)⁻¹` as a MonoidWithZeroHom
-/
noncomputable
def inv : ℕ →*₀ ℝ where
toFun := fun n => (n : ℝ)⁻¹
map_zero' :=
by
  sorry
map_one' :=
by
  sorry
map_mul' :=
by
  sorry

@[simp]
lemma inv' (n : ℕ) : inv n = (n : ℝ)⁻¹:=rfl

/-- `inv` is nonnegative -/
lemma inv_nonneg' (n : ℕ) :  0 ≤ inv n :=
by
  sorry

open Real
#check log_le_log'
#check sum_pos

/--
# The sum of the reciprocals of the primes less than 2⁴ᵐ + 1 is at least log (m + 1/2)
-/
theorem log_le_sum_inv_primes (m : ℕ) :
log ((m : ℝ) + 1 / 2) ≤ ∑ p in (2^(4*m) + 1).PrimesLt, (p : ℝ)⁻¹:=
by
  sorry

/-!
Possible extension: improve the bound in this result.
-/
