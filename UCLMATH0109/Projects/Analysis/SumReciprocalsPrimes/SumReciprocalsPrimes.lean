import Mathlib
open scoped BigOperators Classical List

open Nat hiding mul_le_mul_left pow_succ' add_div add_le_add
open Finset

/-

# In this project we will prove that the sum of the reciprocals of the primes less
# than 2⁴ᵐ + 1 is at least log (m + 1/2)
# Read the project pdf for details. See below for useful results from Mathlib.

You will need to add many intermediate results of your own to get to the main result.
-/
-- Facts about various Finsets (Finite sets)
#check mem_range
#check mem_powerset
#check mem_Ioo
#check mem_filter

-- Facts about squarefree numbers
#check Squarefree
#check not_squarefree_zero
#check squarefree_iff_nodup_factors
#check squarefree_one


-- Facts about prime numbers
#check factors -- the prime factors of a number as a List ℕ
#check factors_unique
#check factorization_prod_pow_eq_self
#check support_factorization
#check mem_primeFactors
#check pos_of_mem_primeFactors
#check prime_of_mem_factors
#check Nat.not_prime_zero

-- Facts about even / odd
#check even_iff_two_dvd
#check odd_iff_not_even
#check two_mul_div_two_add_one_of_odd

-- Facts about products and sums
#check prod_filter
#check prod_mul_distrib
#check prod_congr
#check prod_mul_distrib
#check sum_singleton
#check sum_le_sum_of_subset_of_nonneg
#check sum_map
#check sum_image
#check prod_add
#check prod_le_prod
#check prod_const_one
#check map_prod
#check sum_subset
#check sum_mul_sum
#check sum_pos
#check single_le_sum

-- Facts about Lists (and Finsets)
#check mem_toList
#check List.Perm.nodup_iff
#check nodup_toList
#check List.map_id
#check prod_to_list
#check toList_toFinset
#check List.toFinset_eq_of_perm
#check List.mem_toFinset

/-- The primes < n -/
@[reducible]
def Nat.PrimesLt (n : ℕ) : Finset ℕ :=
 (range n).filter (fun p => Nat.Prime p)

/-- rw mem of Primes < n -/
lemma mem_PrimesLt {n x : ℕ} : x ∈ n.PrimesLt ↔ x < n ∧ Nat.Prime x :=by
  sorry

/-- A natural number n is Squarefree iff the only square that divides it is 1
 Squarefree nats < n -/
@[reducible]
def Nat.SqFreesLt (n : ℕ) : Finset ℕ:= (range n).filter (fun a => Squarefree a)

def sqf : ℕ → ℕ := fun n => ∏ p ∈ (n.factorization.support) with (Odd (n.factorization p)), p

def squ : ℕ → ℕ := fun n => ite (n = 0) 0  (∏ p ∈ (n.factorization.support), p ^ ((n.factorization p)/2))

/-- The crucial property of sqf, squ -/
lemma sqf_mul_squ_sqd  : (sqf n) * (squ n)^2 = n:=by
  sorry

/-- The factorisation of any Finset of primes has no duplicates -/
lemma prime_prod {A : Finset ℕ} (hA : ∀ a, a ∈ A → Nat.Prime a) : (∏ a ∈ A, a).factors.Nodup:=by
  sorry

/-- The decomposition of `n : ℕ` into `(a , b) : ℕ × ℕ` such that `a * b² = n`
with `a` squarefree -/
def Nat.decomp : ℕ → ℕ × ℕ:= fun n => (sqf n, squ n)

/-- decomp as an embedding (it is injective) -/
noncomputable
def Nat.decomp' : ℕ ↪ ℕ × ℕ where
toFun := decomp
inj' :=by sorry

section with_f

#check MonoidWithZeroHom -- the type of multiplicative homomorphisms that send 0 to 0

variable (f : ℕ →*₀ ℝ) (hfnonneg : ∀ x, 0 ≤ f x)

/-
We now want to use `log` and `exp` so we open the `Real` namespace.
-/
open Real
-- Facts about the log and exp functions in the Real numbers
#check log_le_iff_le_exp
#check add_one_le_exp
#check exp_sum

/--
The log of the sum of f over squarefrees < n is at most the sum of f over primes < n.
-/
lemma log_sum_SqFreesLt_le_sum_PrimesLt (hn : 2 ≤ n) :
log (∑ k ∈ n.SqFreesLt, f k) ≤ ∑ p ∈ n.PrimesLt, f p :=
  sorry


/--
The sum of f over range n is at most the product of the sum of SqFreesLt n and the
sum of the squares
-/
lemma sum_range_le_sumSF_mul_sumSq :
∑ k ∈ range n, f k ≤ (∑ a ∈ n.SqFreesLt, f a) * (∑ b ∈ range n, f b^2):=by
  sorry

end with_f

/-- The harmonic series ≤ 2^m  is at least m / 2 + 1 -/
lemma sum_inv_pow_two (m : ℕ) : m / 2 + 1 ≤ ∑ k ∈ range (2^m+1),(k : ℝ)⁻¹ :=by
  sorry


/-- The sum of reciprocals of squares is ≤ 2 -/
lemma sum_inv_sq_le_two {n : ℕ} : ∑ k ∈ range n,  ((k : ℝ)⁻¹)^2 ≤ 2 :=by
  sorry



/--
We define `inv` to be reciprocal function `fun (n : ℕ) => (n : ℝ)⁻¹` as a MonoidWithZeroHom
-/
noncomputable
def inv : ℕ →*₀ ℝ where
toFun := fun n => (n : ℝ)⁻¹
map_zero' := by sorry
map_one' :=by sorry
map_mul' :=by sorry


open Real
/--
# The sum of the reciprocals of the primes less than 2⁴ᵐ + 1 is at least log (m + 1/2)
-/
theorem log_le_sum_inv_primes (m : ℕ) :
log ((m : ℝ) + 1/2) ≤ ∑ p ∈ range (2 ^ (4 * m) + 1) with Nat.Prime p, (p : ℝ)⁻¹:=by
  sorry
