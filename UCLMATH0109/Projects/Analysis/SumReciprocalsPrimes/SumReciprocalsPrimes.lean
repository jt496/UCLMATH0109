import Mathlib
open scoped BigOperators Classical List

open Nat hiding mul_le_mul_left pow_succ' add_div add_le_add
open Finset
/-
Main result of project:
# The sum of the reciprocals of the primes less than 2⁴ᵐ + 1 is at least log (m + 1/2)
-/
/-- The primes < n -/
@[reducible]
def Nat.PrimesLt (n : ℕ) : Finset ℕ := (range n).filter (Nat.Prime ·)

/-- rw mem of Primes < n -/
lemma mem_PrimesLt {n x : ℕ} : x ∈ n.PrimesLt ↔ x < n ∧ Nat.Prime x :=by
  rw [PrimesLt, mem_filter, mem_range]

/-- A natural number n is Squarefree iff the only square that divides it is 1
 Squarefree nats < n -/
@[reducible]
def Nat.SqFreesLt (n : ℕ) : Finset ℕ := (range n).filter (Squarefree ·)

/- # Computable version of square-free * square decomposition -/

def sqf : ℕ → ℕ := fun n => ∏ p ∈ (n.factorization.support) with (Odd (n.factorization p)), p

def squ : ℕ → ℕ := fun n => ite (n = 0) 0  (∏ p ∈ (n.factorization.support), p ^ ((n.factorization p)/2))

/-- See Lemma (A) in pdf -/
lemma sqf_mul_squ_sqd  (n : ℕ) : (sqf n) * (squ n)^2 = n:=by
  sorry


/-- Decompose `n` into squarefree and square parts as an embedding (it is injective) -/
@[simp]
noncomputable
def Nat.decomp : ℕ ↪ ℕ × ℕ where
toFun := fun n => (sqf n, squ n)
inj' :=by
  sorry

open Real
section with_f
variable (f : ℕ →*₀ ℝ) (hfnonneg : ∀ x, 0 ≤ f x)

/-- The log of the sum of f over squarefrees < n is at most the sum of f over primes < n.
(See Lemma (B) in pdf.) -/
lemma log_sum_SqFreesLt_le_sum_PrimesLt (hn : 2 ≤ n) :
log (∑ k ∈ n.SqFreesLt, f k) ≤ ∑ p ∈ n.PrimesLt, f p := by
  sorry

/-- The sum of f over range n is at most the product of the sum of SqFreesLt n and the
sum of the squares.(See Lemma (C) in pdf.) -/
theorem sum_range_le_sumSF_mul_sumSq :
∑ k ∈ range n, f k ≤ (∑ a ∈ n.SqFreesLt, f a) * (∑ b ∈ range n, f b^2):= by
  sorry

end with_f


/--
We define `inv` to be reciprocal function `fun (n : ℕ) => (n : ℝ)⁻¹` as a MonoidWithZeroHom -/
noncomputable
def inv : ℕ →*₀ ℝ where
toFun := fun n => (n : ℝ)⁻¹
map_zero' :=by
  sorry
map_one' :=by
  sorry
map_mul' :=by
  sorry

/--
# The sum of the reciprocals of the primes less than 2⁴ᵐ + 1 is at least log (m + 1/2) -/
theorem log_le_sum_inv_primes (m : ℕ) :
log ((m : ℝ) + 1/2) ≤ ∑ p ∈ range (2 ^ (4 * m) + 1) with Nat.Prime p, (p : ℝ)⁻¹:=by
  sorry
