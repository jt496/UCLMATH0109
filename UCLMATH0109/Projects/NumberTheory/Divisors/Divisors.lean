import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Finset.Basic


open Finset Nat
/-
If S ⊆ {1,.., 2n} with n ≤ 1 and  n + 1 ≤ |S| then ∃ a, b ∈ S st a ∣ b

Define f: S → {1,3,..,2n-1} by f(x) = maximum odd factor of x

If f(a)=f(b) then a|b or b|a (since a= 2^r f(a) and b = 2^s f(b)

Hence if |S| > n then by pigeonhole principle we have a,b ∈ S with a ≠ b and a∣b -/

/-- S is `Divisible` iff there exist a,b ∈ S such a ≠ b and a ∣ b-/
def Divisible (S : Finset ℕ) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b


/-
We will use `ord_compl[2] n` which is defined to be n divided by
the highest power of 2 in the prime factorisation of n.
-/

#eval Nat.factorization 100 3
#eval Nat.factorization 500 5
#eval Nat.factorization 100 2

#check ord_compl[2] 10 -- 10 / 2 ^ ↑(Nat.factorization 10) 2
#eval ord_compl[2] 10 -- 5

#check ord_proj[2] 10 -- 2 ^ ↑(Nat.factorization 10) 2
#eval ord_proj[2] 10 -- 2

/-- maximum odd factor-/
def max_odd_factor : ℕ → ℕ := fun n => ord_compl[2] n


/- definitional lemma for max_odd_factor-/
@[simp]
lemma max_odd_factor' : max_odd_factor n = ord_compl[2] n:=
by
  sorry

/-- max_odd_factor is odd -/
lemma odd_of_max_odd_factor (h : a ≠ 0) : Odd (max_odd_factor a) :=
by
  sorry

/-- max_odd_factor a ≤ a -/
lemma max_odd_factor_le_self (a : ℕ) : max_odd_factor a ≤ a :=
by
  sorry

/-- 0 < max_odd_factor a for a ≠ 0-/
lemma pos_of_max_odd_factor (h : a ≠ 0) : 0 < max_odd_factor a :=
by
  sorry

/-- If a and b have the same max_odd_factor and the highest power of 2 dividing a
is at most that dividing b then a divides b-/
lemma max_odd_factor_eq_le_imp_dvd (heq : max_odd_factor a = max_odd_factor b)
    (h2 : a.factorization 2 ≤ b.factorization 2) : a ∣ b :=
by
  sorry

/-- max_odd_factor a = max_odd_factor b → a | b or b | a -/
lemma max_odd_factor_eq_imp_dvd (heq : max_odd_factor a = max_odd_factor b) : a ∣ b ∨ b ∣ a :=
by
  sorry

/--
If S is not Divisible then max_odd_factor is injective on S
-/
lemma max_odd_factor_injOn_not_div (hd : ¬Divisible S) : Set.InjOn max_odd_factor S :=
by
  sorry

#check Ioc_filter_dvd_card_eq_div
/-- the number of even integers in [1,2n] is n -/
lemma even_in_Ioc (n : ℕ) : ((Ioc 0 (2 * n)).filter fun x => 2 ∣ x).card = n :=
by
  sorry

/-- the number of odd nats in [1,2n] is n-/
lemma card_odd_le_2n (n : ℕ) : ((Ioc 0 (2 * n)).filter Odd).card = n :=
by
  sorry

/-- Main result: if S ⊆ {1,...,2n} is not Divisible then |S| ≤ n -/
theorem not_div_bdd_card_le (hb : S ⊆ Ioc 0 (2 * n)) (hd : ¬Divisible S) :
    S.card ≤ n :=
by
  sorry

/-
We end by proving that for any n there exists an example proving our
theorem is best possible.
-/
/-- There exists S ⊆ {1,...,2n} not Divisible of size exactly n -/
theorem exists_not_div_card_eq : ∃ S, S ⊆ Ioc 0 (2 * n) ∧ ¬Divisible S ∧ S.card = n :=
by
  sorry

/-!
Possible extension: consider S ⊆ {1,...,2ᵏ⁺¹n}  if S does not contain k + 2 pairwise divisors
then |S| ≤  (2^(k+1)-1)*n.

(We just proved the case k = 0 of this result.)
-/
