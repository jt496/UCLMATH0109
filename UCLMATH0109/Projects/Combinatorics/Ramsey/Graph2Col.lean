import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Tauto

open Finset Nat
open BigOperators


local notation "|" x "|" => Finset.card x

/-

The main result in this project is the Erdos-Szekeres upper bound for the 2-colour
Ramsey number:

    R(s+1,t+t) ≤ (s+t).choose s

On the way we prove R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t).

We finish by proving some constructive lower bounds (by giving examples of 2-colourings
that do not contain monochromatic cliques and having Lean check the details).

We use Fin 2 = {0,1} as our two colours - 0 as red and 1 as blue.
(We use this rather than the more obvious Bool = {true,false} since we
want to extend to more colours later.)

Note that if `a : Fin 2` then `a` is a pair `a = ⟨a.val,a.isLt⟩` where
`a.val : ℕ` and `a.isLt` is a proof that `a < 2`

We define 2-colourings as maps from all finite subsets of ℕ to {0,1}
i.e.
 `col : Finset ℕ → Fin 2`

We only really care (at the moment) about the colour given to pairs {x,y} where x ≠ y

If `A : Finset ℕ` then `A.powersetLen 2` is the `Finset (Finset ℕ)` of all subsets of A
  of size 2. [We use the notation `A^(2)` for this in these comments and the pdf.]
-/

section Mathlib_examples

variable {A : Finset ℕ} {a n : ℕ}

#check A.powersetLen 2 -- the collection of subsets of size 2 from A
#check insert n A -- The Finset formed by inserting n into A (aka A ∪ {n})
#check insert n ({a} : Finset ℕ) -- this is Lean's definition of {n, a} as a Finset ℕ

end Mathlib_examples

open Finset Nat

/-- A 2-colouring `col` is monoOn a set `A` iff every pair in the set receives the same colour `c`  -/
@[reducible]
def Finset.monoOn (A : Finset ℕ) (col : Finset ℕ → Fin 2) (c : Fin 2) :  Prop:=
∀ (e : Finset ℕ), e ∈ A.powersetLen 2  → col e = c


/-- A 2-colouring col satisfies `RamseyCol col N s t` if every set of size at least N
 contains an s-set with all pairs red or a t-set with all pairs blue -/
def RamseyCol (col : Finset ℕ → Fin 2) (N s t : ℕ) : Prop :=
∀ {V : Finset ℕ}, N ≤ |V| →
(∃ (A : Finset ℕ), A ⊆ V ∧ ((A.monoOn col 0 ∧ s ≤ |A|) ∨ (A.monoOn col 1 ∧ t ≤ |A|)))

/-- N is RamseyOf for s,t if every 2-colouring is a RamseyCol for N s t -/
def RamseyOf (N s t : ℕ): Prop:= ∀ (col : Finset ℕ → Fin 2), RamseyCol col N s t

/-- given a 2-colouring col, a colour c : Fin2 , V : Finset ℕ  and n : ℕ
the `nbhd col c V n` is `{ w ∈ V | col {w, n} = c}` as a Finset ℕ -/
def nbhd  (col : Finset ℕ → Fin 2) (c : Fin 2) (V : Finset ℕ) (n : ℕ) :
 Finset ℕ:= V.filter (fun w => col (insert w {n}) = c)

/- `notC` is the opposite colour to colour  `c` -/
def notC (c : Fin 2) : Fin 2 := if (c = 0) then 1 else 0

/-- flip all the colours in a 2-colouring -/
def notCol (col : Finset ℕ → Fin 2) : Finset ℕ → Fin 2 :=  notC ∘ col

#check one_le_iff_ne_zero
#check Fin.val_eq_val

/-- If a ∈ {0, 1} and a ≠ 0 iff a = 1 but proved in `Fin 2`-/
lemma  Fin_two_not (a : Fin 2) : ¬ a = 0 ↔ a = 1 :=
by
  sorry

/-- notC (notC c) = c  -/
lemma not_notC (c : Fin 2) : notC (notC c) = c:=
by
  sorry


#check powersetLen_mono

/-- If a 2-colouring is monoOn A with colour c this also true of any subset of A -/
lemma mono_of_monoOn {A : Finset ℕ} (h: A.monoOn col c) (hB: B ⊆ A ) : B.monoOn col c:=
by
  sorry


#check powersetLen_empty

/-- Trivially if |A| < 2 so A is empty or a singleton any 2-colouring is mono on it-/
lemma monoOn_subsingleton {A : Finset ℕ} (h: |A| < 2) (col : Finset ℕ → Fin 2) (c : Fin 2) :
 A.monoOn col c:=
by
  sorry


/-- We have `A.monoOn col c` iff its flipped version is monoOn with the opposite colour -/
lemma monoOn_iff_notCol  {A : Finset ℕ} : A.monoOn col c ↔
A.monoOn (notCol col) (notC c):=
by
  sorry


/-- if N is Ramsey for s,t and N ≤ M then M is also Ramsey for s,t -/
lemma mono_RamseyOf  (h : RamseyOf N s t) (hm: N ≤ M) : RamseyOf M s t :=
by
  sorry

#check mem_filter
/-- rw lemma for nbhd -/
lemma nhbd_col' (hw: w ∈ nbhd col c V n) : col (insert w {n}) = c:=
by
  sorry

/-- Any vertex in nbhd is in the original set V -/
lemma mem_of_mem_nbhd (hv : v ∈ nbhd col c V n): v ∈ V:=
by
  sorry

/-- Any subset of nbhd is a subset of V -/
lemma subset_nbhd (hA: A ⊆ nbhd col c V n) : A ⊆ V:=
by
  sorry

#check pair_comm
#check mem_image
#check mem_powersetLen
#check card_eq_one
#check mem_singleton_self

/-- Given an edge from n to the c-coloured nbhd of n it has colour c-/
lemma mono_nbhr  (hnb: A ⊆ nbhd col c V n)
(he: e ∈ image (insert n) (powersetLen 1 A)): col e = c:=
by
  sorry


#check powersetLen_succ_insert
#check mem_union
#check not_mem_mono

/--
If n ∉ V, A.monoOn col c and A ⊆ nbhd col c V n then every pair inside A
is already coloured c and so are all pairs `{n, a}` where `a ∈ A` so `col`
is monoOn `(insert n A)` which is Lean for `A ∪ {n}`.
-/
lemma monoOn_insert (hV: n ∉ V) (hm : A.monoOn col c) (hnb: A ⊆ nbhd col c V n) :
(insert n A).monoOn col c:=
by
  sorry

#check disjoint_filter_filter_neg

/-- red and blue nbhds are disjoint-/
lemma  nbhd_disj  (col : Finset ℕ → Fin 2) (V : Finset ℕ) (n : ℕ) : Disjoint (nbhd col 0 V n) (nbhd col 1 V n):=
by
  sorry

#check filter_union_filter_neg_eq

/- The union of red and blue nbhds is V -/
lemma  nbhd_union_eq (col : Finset ℕ → Fin 2) (V : Finset ℕ) (n : ℕ):
 (nbhd col 0 V n) ∪ (nbhd col 1 V n) = V :=
by
  sorry

#check card_union_eq

/-- Hence the sum of sizes of red and blue nbhds is |V| -/
lemma card_nbhd (col : Finset ℕ → Fin 2) (V : Finset ℕ) (n : ℕ) :
|V| = |nbhd col 0 V n| + |nbhd col 1 V n| :=
by
  sorry

/-
Passing comment:

The next lemma is very easy, but can also be seen as the version of
Ramsey's theorem for singletons (rather than pairs).

If you colour {1,...,c + d} red/blue and a + b - 1 ≤ c + d then you
either coloured at least a elements red or at least b elements blue.
-/

#check add_lt_add_of_le_of_lt
#check le_pred_of_lt
/-- The inequality we require for the inductive step in Ramsey's theorem -/
lemma nbhd_cases :  a + b - 1 ≤ c + d  → a ≤ c ∨ b ≤ d:=
by
  sorry


#check card_pos
#check Finset.erase
#check not_mem_erase
#check card_erase_of_mem
#check pred_le_pred
#check insert_subset
#check erase_subset
/-
The next result is the key step in the proof of Ramseys theorem that
 R (s+1, t+1) ≤ R(s,t+1) + R(s+1,t) but phrased in terms of `RamseyOf`
-/

/-- Key step R (s+1,t+1) ≤ R(s,t+1) + R(s+1,t) -/
lemma Ramsey_step (hab : 1 ≤ a + b): RamseyOf a s (t + 1)
→ RamseyOf b (s + 1) t → RamseyOf (a + b) (s + 1) (t + 1):=
by
  sorry


/-- Symmetry in (s,t) -/
lemma Ramsey_symm {n s t : ℕ} : RamseyOf n s t → RamseyOf n t s:=
by
  sorry

#check exists_smaller_set

/-- R(0,t) ≤ 0 and R(1,t) ≤ 1 -/
lemma Ramsey_lt_two (h : s < 2): RamseyOf s s t:=
by
  sorry


/-- R(0,t) ≤ 0 -/
lemma Ramsey_zero (t : ℕ): RamseyOf 0 0 t:=
by
  sorry


/-- R(1,t) ≤ 1 -/
lemma Ramsey_one (t : ℕ): RamseyOf 1 1 t:=
by
  sorry


/-- R(s,2) ≤ s -/
lemma Ramsey_two (s : ℕ) : RamseyOf s s 2:=
by
  sorry

/-
For this theorem you need to use facts about Nat.choose
-/
#check choose_zero_right
#check choose_self
#check choose_succ_succ

/-- The Erdos--Szekeres version of Ramsey's theorem -/
theorem Erdos_Szekeres_Ramsey (s t : ℕ)  : RamseyOf ((s + t).choose s) (s + 1) (t + 1) :=
by
  sorry




/-- R(3,3) ≤ 6-/
lemma R33 : RamseyOf 6 3 3:=
by
  sorry

/-- R(3,4) ≤ 10 -/
lemma R34 : RamseyOf 10 3 4:=
by
  sorry

/-- R(4,4) ≤ 20 -/
lemma R44 : RamseyOf 20 4 4:=
by
  sorry

/-- R(5,5) ≤ 70 -/
lemma R55 : RamseyOf 70 5 5:=
by
  sorry

/-- R(6,6) ≤ 252 -/
lemma R66 : RamseyOf 252 6 6:=
by
  sorry

/-
Possible extension:

# Constructive lower bounds

We can prove that n < R(s,t) by exhibiting a 2-colouring that has no red K_s or blue K_t in {0,1,...,n-1}

We introduce this as a definition; prove that it implies ¬ RamseyOf n s t
and then give some actual examples of 2-colourings that Lean can check to prove various lower bound
on small Ramsey numbers.

-/

/--
If a 2-colouring has no red K_s and no blue K_t in {0,1,...,n-1} then it will allow us to prove
that n < R(s,t) (or equivalently ¬ RamseyOf n s t)
-/
@[reducible]
def not_RamseyOf_col (n s t : ℕ) (col: Finset ℕ → Fin 2): Prop :=
(∀ V ∈ (range n).powersetLen s, ¬V.monoOn col 0) ∧ (∀ V ∈ (range n).powersetLen t, ¬V.monoOn col 1)


theorem not_RamseyOf_exists (hcolbad: ∃ (col : Finset ℕ → Fin 2), not_RamseyOf_col n s t col):
 ¬ RamseyOf n s t:=
by
  sorry


lemma R33_gt_5 : ¬ RamseyOf 5 3 3 :=
by
  sorry

lemma R34_gt_8 : ¬ RamseyOf 8 3 4 :=
by
  sorry

lemma R44_gt_17 : ¬ RamseyOf 17 4 4 :=
by
  sorry
