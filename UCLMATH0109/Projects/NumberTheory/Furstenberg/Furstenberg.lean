import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Prime

open Set Nat

/-

`Furstenberg's proof of infinitude of primes`.

or

`How to make a meal of Euclid's proof but learn a bit about topological spaces`

-/
/-- an arithmetic progression is the set {b, a+b, 2a+b,3a+b,...} -/
def AP (a b : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k : ℕ, n = a * k + b}

@[simp]
lemma AP' : AP a b =  {n : ℕ | ∃ k : ℕ, n = a * k + b}:=
by
  sorry
/-
We say `AP a b` is `non-trivial` iff `a ≠ 0` although we don't actually define
 this formally it will be useful for these comments.
-/

/-- The intersection of any pair of APs with first term b is also an AP
(and if the APs are non-trivial so is this AP)-/
theorem AP_mul_sub_int (a₁ a₂ b : ℕ) : AP (a₁ * a₂) b ⊆ AP a₁ b ∩ AP a₂ b :=
by
  sorry

#check mod_eq_of_lt
#check div_add_mod
#check add_mul_mod_self_left

/-- For 0 ≤ b < a we have `n ∈ AP a b iff n = b mod a` -/
theorem mem_AP_iff (a b n : ℕ) (h : b < a) : n ∈ AP a b ↔ n % a = b :=
by
  sorry


#check exists_prime_and_dvd
#check mem_iUnion₂
#check mul_eq_one
#check Nat.Prime.ne_one

/-- every  n ∈ ℕ \ {1} has a prime divisor, so `ℕ \ {1} = ⋃ p, AP p 0` -/
theorem prime_AP_iUnion : (univ : Set ℕ) \ {1} = ⋃ p ∈ {n : ℕ | n.Prime}, AP p 0 :=
by
  sorry


/-- If `b < a` then `AP a b` is the complement of a union of APs  -/
theorem AP_eq_compl_iUnion (a b : ℕ) (hb : b < a) :
    AP a b = (univ : Set ℕ) \ ⋃ j ∈ {k : ℕ | k < a ∧ k ≠ b}, AP a j :=
by
  sorry

/-
We want to define a topology on ℕ and the next definition will be the
key notion of which sets of ℕ are open in this topology
-/

/-- `U ⊆ ℕ` is `Fopen` iff for every n ∈ U there is a non-trivial
 AP containing n and contained in U. -/
def Fopen : Set ℕ → Prop := fun U => ∀ n ∈ U, ∃ a, a ≠ 0 ∧ AP a n ⊆ U

/-- The Furstenberg topology on ℕ -/
instance furstenberg : TopologicalSpace ℕ
    where
  IsOpen := Fopen
  isOpen_univ :=by
    sorry
  isOpen_inter :=by
    sorry
  isOpen_sUnion :=by
    sorry

/-- Definitional rewriting for `IsOpen`  -/
theorem isOpen_iff_Fopen (S : Set ℕ) : IsOpen S ↔ Fopen S :=
by
  sorry


/-- Any non-trivial AP a b is open -/
theorem AP_isOpen (a b : ℕ) (h : a ≠ 0) : IsOpen (AP a b) :=
by
  sorry

/-- If b < a then AP a b is  closed -/
theorem AP_isClosed (a b : ℕ) (hb : b < a) : IsClosed (AP a b) :=
by
  sorry




/-- If there were only finitely many primes then {1} would be open
in Furstenberg topology on  ℕ -/
theorem fin_prime_imp_one_open : {p : ℕ | p.Prime}.Finite → IsOpen ({1} : Set ℕ) :=
by
  sorry


/-- The set {1} is not open (if it were open it would contain a non-trival AP) -/
theorem one_not_open : ¬IsOpen ({1} : Set ℕ) :=
by
  sorry

-- For the next proof you are *not* allowed to use anything that isn't contained in this file

/-- At last... there are infinitely many primes -/
theorem infinitely_many_primes : {p : ℕ | p.Prime}.Infinite :=
by
  sorry


/-
Possible extension: explore the topological properties of this space, for example
show that it is Hausdorff.
-/

instance : T2Space ℕ := sorry
