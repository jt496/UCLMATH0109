import Mathlib
open Set Nat

/-
# This project is on Fursternberg's proof of the infinitude of primes.
# Read the project pdf for details. See below for useful results from Mathlib.
-/


/-- an arithmetic progression is the set {b, a + b, 2a + b, 3a + b,...} -/
def AP (a b : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, n = a * k + b}

/-- every  n ∈ ℕ \ {1} has a prime divisor, so `ℕ \ {1} = ⋃ p, AP p 0` -/
lemma prime_AP_iUnion : (univ : Set ℕ) \ {1} = ⋃ p ∈ {n : ℕ | n.Prime}, AP p 0 :=by
  sorry

/-
You will need to add lemmas about arithmetic progressions here.
See the pdf for some that will be useful, but you can/should add others. -/


/-
We want to define a topology on ℕ and the next definition will be the
key notion of which sets of ℕ are open in this topology. -/

/-- `U ⊆ ℕ` is `Fopen` iff for every n ∈ U there is a non-trivial
 AP containing n and contained in U. -/
def Fopen : Set ℕ → Prop := fun U => ∀ n ∈ U, ∃ a, a ≠ 0 ∧ AP a n ⊆ U


/-- The Furstenberg topology on ℕ -/
instance furstenberg : TopologicalSpace ℕ
    where
  IsOpen := Fopen
  isOpen_univ :=by sorry
  isOpen_inter :=by sorry
  isOpen_sUnion := by sorry

/-- Definitional rewriting for `IsOpen`  -/
theorem isOpen_iff_Fopen (S : Set ℕ) : IsOpen S ↔ Fopen S := by rfl



/-- If there were only finitely many primes then {1} would be open
in Furstenberg topology on  ℕ -/
theorem fin_prime_imp_one_open (hfin : (setOf Nat.Prime).Finite) : IsOpen ({1} : Set ℕ) :=by
  sorry


/-
For the next proof you are *not* allowed to use anything that isn't
contained in this file
-/

/-- There are infinitely many primes -/
theorem infinitely_many_primes : (setOf Nat.Prime).Infinite :=by
  sorry




/-
Possible extension:
Explore the topological properties of this space, for example
show that it is Hausdorff (T2) and not compact.
See pdf for details.
-/

#check disjoint_iff_forall_ne

instance : T2Space ℕ where
  t2 :=by sorry



/- Compactness using FIP of closed sets -/
#check isCompact_univ_iff
#check isCompact_of_finite_subfamily_closed
#check Nat.chineseRemainderOfFinset

theorem NotCompact : ¬CompactSpace ℕ :=by
  sorry
