import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic


local notation "|" x "|" => Finset.card x


/-
The main result in this project is the hypergraph version of Ramsey's theorem for 2-colours.

If X is a set and r ∈ ℕ we let X^(r) denote the set of subsets of X of size r.

If r,s,t : ℕ then there exists N : ℕ, such that in every 2-colouring of ℕ^(r)
every set of size N contains a set A such that |A| ≥  s and all the r-sets in A^(r) are red
or |A| ≥ t and all the r-sets in A^(r) are blue.


We use Fin 2 = {0,1} as our two colours - 0 as red and 1 as blue.
(We use this since we will later want to extend to more colours later.)

Note that if `a : Fin 2` then `a` is a pair `a = ⟨a.val,a.isLt⟩` where
`a.val : ℕ` and `a.isLt` is a proof that `a < 2`

We define colourings as maps from all finite subsets of ℕ to {0,1}
i.e.
 `col : Finset ℕ → Fin 2`

We only really care about the colour given to sets of size `r`.

If `A : Finset ℕ` then `A.powersetLen r` is the `Finset (Finset ℕ)` of all subsets of A
  of size `r`.
[We use the notation `A^(r)` for this in these comments and the pdf.]
-/

/-- A 2-colouring col is mono on A^(r) iff every r-set in A has the same colour c -/
def Finset.monoOnR (A : Finset ℕ) (r : ℕ) (col : Finset ℕ → Fin 2) (c : Fin 2) : Prop :=
  ∀ e ∈ A.powersetLen r, col e = c


/-
Since we previously proved similar results for r = 2 we put this project in a namespace
to avoid any confusion. Note we are proving everything from scratch and we won't use the
r = 2 case in our proof.
-/
namespace RGraph
open Finset Nat

/-- Given a 2-colouring and a vertex x we have the nbhd 2-colouring,
giving `e` the colour of `insert x e = e ∪ {x}`  -/
def nbhd (x : ℕ) (col : Finset ℕ → Fin 2) : Finset ℕ → Fin 2 := fun e => col (insert x e)


#check insert_erase

/-- the colour of an (r+1)-set e containing x is the same as the colour of the r-set with x removed
in the nbhd colouring -/
lemma nbhd_eq (x : ℕ) (col : Finset ℕ → Fin 2) :
    ∀ e : Finset ℕ, x ∈ e → col e = nbhd x col (e.erase x) :=
by
  sorry
/--
RamseyOf n r s t ↔ for any 2-colouring of the r-sets of ℕ every subset of size at least n contains
A such that either s ≤ |A| and A^(r) is red of t ≤ |A| and A^(r) is blue -/
def RamseyOf (N r s t : ℕ) : Prop :=
  ∀ col : Finset ℕ → Fin 2,
    ∀ V : Finset ℕ,
      N ≤ |V| →
        ∃ A : Finset ℕ, A ⊆ V ∧ (s ≤ |A| ∧ A.monoOnR r col 0 ∨ t ≤ |A| ∧ A.monoOnR r col 1)



#check card_eq_succ
#check subset_insert
#check mem_insert_self
/--
If n + 1 ≤ |V| then there exists  W ⊆ V with n ≤ |W| and ∃ x ∉ W , x ∈ V
-/
lemma succ_le_card {V : Finset ℕ} {n : ℕ} (hV : n + 1 ≤ |V|) :
    ∃ (x : ℕ), ∃ (W : Finset ℕ), W ⊆ V ∧ n ≤ |W| ∧ x ∉ W ∧ x ∈ V :=
by
  sorry

/-
The next lemma contains the crucial idea for the inductive step.

It says that if we have a vertex x and a set A not containing x
such that all the (r+1)-sets formed by adding x to a set in A^(r) have colour c
and A contains a set B such that s ≤ |B| and B^(r+1) is mono c then
(B ∪ {x})^(r+1)  is mono c and has size at least s + 1.
-/
#check card_insert_of_not_mem
#check powersetLen_succ_insert
#check mem_powersetLen
/--
Given a colouring that is mono c on A^(r) with s ≤ |A| and a vertex x such that the
nbhd colouring of x is mono c of the same colour we can extend to get a mono K_{s+1} -/
lemma nbhd_mono   {A V : Finset ℕ}  (h1 : A.monoOnR r (nbhd x col) c) (h2 : B ⊆ A) (h3 : s ≤ |B| ∧ B.monoOnR (r + 1) col c)
    (hx : x ∉ A ∧ x ∈ V) : (s + 1) ≤ |(insert x B)| ∧ (insert x B).monoOnR (r + 1) col c :=
by
  sorry


/-
See the pdf for a sketch of this next key lemma.
-/

/-- Key step to show 2-colour Ramsey numbers exist for all r-graphs -/
lemma Ramsey_step :
    RamseyOf n r a b → RamseyOf a (r + 1) s (t + 1) →
       RamseyOf b (r + 1) (s + 1) t → RamseyOf (n + 1) (r + 1) (s + 1) (t + 1) :=
by
  sorry

/-- RamseyOf n r s t is monotone in n -/
lemma Ramsey_mono  (hm : n ≤ m) (h : RamseyOf n r s t) : RamseyOf m r s t :=
by
  sorry

/-- RamseyOf n r s t is monotone in s and t -/
lemma Ramsey_mono_sizes  (ha : a ≤ s) (hb : b ≤ t) (h : RamseyOf n r s t) : RamseyOf n r a b :=
by
  sorry

#check exists_smaller_set
#check  powersetLen_empty

/-- If s < r then RamseyOf s r s t holds for any t -/
lemma Ramsey_triv  (hr : s < r) : RamseyOf s r s t :=
by
  sorry

#check Fin.val_eq_val

/--Useful for flipping colours in a 2-colouring -/
lemma  Fin_two_not (a : Fin 2) : ¬ a = 0 ↔ a = 1 :=
by
  sorry

/-- In the case that s = r (so if anything is coloured red we are happy)
we have the trivial bound -/
lemma Ramsey_edge  : RamseyOf t r r t :=
by
  sorry

/--
0-graphs : colourings of the empty set.
-/
lemma Ramsey_zero_graphs (s : ℕ) : RamseyOf s 0 s s :=
by
  sorry

/- `notC` is the opposite colour to colour  `c` -/
def notC (c : Fin 2) : Fin 2 := if (c = 0) then 1 else 0

/-- flip all the colours in a 2-colouring -/
def notCol (col : Finset ℕ → Fin 2) : Finset ℕ → Fin 2 :=  notC ∘ col

/-- notC (notC c) = c  -/
lemma not_notC (c : Fin 2) : notC (notC c) = c:=
by
  sorry


/-- col is mono on A iff it flipped version is  -/
lemma monoOnR_iff_notCol {A : Finset ℕ}: A.monoOnR r col c ↔ A.monoOnR r (notCol col) (notC c) :=
by
  sorry

lemma Ramsey_symm : RamseyOf n r s t → RamseyOf n r t s :=
by
  sorry

/-- r-graph 2-colour Ramsey numbers are finite -/
theorem Ramsey_rgraphs (r s t : ℕ) : ∃ n : ℕ, RamseyOf n r s t :=
by
  sorry

end RGraph


/-!
Possible extension: prove the same result for k colours.
-/

/-- A col is KmonoOnR A iff every set in A^(r) receives the same colour c  -/
def Finset.KmonoOnR (A : Finset ℕ) (r:ℕ)  (col : Finset ℕ → Fin k) (c : Fin k) : Prop :=
  ∀ e : Finset ℕ, e ∈ A.powersetLen r  → col e = c

namespace RGraph
open RGraph Finset Nat

/-- n is KRamseyOf r s, if for every k-colouring and every n-set V; there exists
a colour c and a subset A, such that s_c ≤ |A| and A^(r) is mono c -/
def KRamseyOf (n r : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ col : Finset ℕ → Fin k,
    ∀ {V : Finset ℕ},
      n ≤ |V| → ∃ A : Finset ℕ, ∃ c : Fin k, A ⊆ V ∧ s c ≤ |A| ∧  A.KmonoOnR r col c

/-- if n is RamseyOf for s,t and n ≤ m then m is also RamseyOf -/
lemma mono_KRamseyOf {s : Fin k → ℕ} (h : KRamseyOf n r s) (hm : n ≤ m) : KRamseyOf m r s :=
by
  sorry

/-- the first k sizes of cliques -/
def kSizes (s : Fin (k+1) → ℕ) : Fin k → ℕ := fun c => s c

/--
the 2-colouring associated to a (k+1)-col given by
i ↦ 0 for all i < k and  k ↦ 1  -/
def kto2 (col : Finset ℕ → Fin (k+1)) : Finset ℕ → Fin 2 :=
  fun e => if col e < Fin.last k then 0 else 1

/-- Definitional lemma for kto2 -/
@[simp]
lemma kto2' (col : Finset ℕ → Fin (k+1)) (e : Finset ℕ) : kto2 col e = if (col e < Fin.last k) then 0 else 1 :=
by
  sorry

#check Fin.last_le_iff

/-- If `kto2 col e = 0` then `col e` is one of the first k colours -/
@[simp]
lemma kto2_zero {col : Finset ℕ → Fin (k+1)} {e : Finset ℕ} (h0 : kto2 col e = 0) : col e < Fin.last k:=
by
  sorry


#check Fin.eq_last_of_not_lt
#check Fin.cast_nat_eq_last


/-- If `kto2 col e = 1` then `col e` is colour k -/
@[simp]
lemma kto2_one {col : Finset ℕ → Fin (k+1)} {e : Finset ℕ} (h0 : kto2 col e = 1) : col e = k :=
by
  sorry

section with_kNeZero

variable {k : ℕ} [NeZero k]

/-- the k-colouring formed from a (k+1)-colouring that
    only uses colours 0,..,k-1 on pairs in A -/
def kcol {col : Finset ℕ → Fin (k+1)} (hm : monoOnR A r (kto2 col) 0)  :
    Finset ℕ → Fin k :=
by
  intro e
  by_cases he : e ∈ A.powersetLen r
  · have hcol := hm e he
    use col e
    apply kto2_zero hcol
  · exact 0


/-- Definitional lemma for kcol-/
@[simp]
lemma kcol' {col : Finset ℕ → Fin (k+1)} (hm : monoOnR A r (kto2 col) 0)
     : ∀ e ∈ A.powersetLen r, (kcol hm e : ℕ) = col e :=
by
  sorry

section withA

variable {A : Finset ℕ}

#check powersetLen_mono
/-- If the kto2 colouring is red on A^(r) and  a ≤ |A| where `kRamseyOf a r (kSizes s)`
then A contains a set B such that  B^(r) is colour c and |B|≥  s_c, for some colour c   -/
lemma kmono_kto2_zero  {col : Finset ℕ → Fin (k+1)}  {s : Fin (k+1) → ℕ}
    (hm : A.monoOnR r  (kto2 col) 0) (kra : KRamseyOf a r (kSizes s)) (hA : a ≤ |A|) :
    ∃ c : Fin k, ∃ B : Finset ℕ, B ⊆ A ∧ B.KmonoOnR r  col c ∧ s c ≤ |B| :=
by
  sorry


/-- If the kto2 colouring is blue on A^(r) then the original (k+1)-colouring was k  -/
lemma kmono_kto2_one {col : Finset ℕ → Fin (k+1)} (hm : A.monoOnR r (kto2 col) 1) :
    A.KmonoOnR  r col k :=
by
  sorry


end withA

/-- The inductive step for (k+1)-colours see pdf of KColourRamsey project for sketch of proof -/
lemma kRamsey_step  (s : Fin (k+1) → ℕ) :
    KRamseyOf a r (kSizes s) → RamseyOf b r a (s k) → KRamseyOf b r s :=
by
  sorry


/-- 0 colours -/
lemma kRamsey_zero  (s : Fin 0 → ℕ) :  KRamseyOf 0 r s :=
by
  sorry

/- 1 colour -/
lemma kRamsey_one (s : Fin 1 → ℕ) : KRamseyOf (s 0) r s :=
by
  sorry

/-- For any number of colours k and any uniformity r and any s : Fin k → ℕ
 there is an n that will work..-/
theorem kcolour_rgraph_Ramsey (r : ℕ) (s : Fin k → ℕ) : ∃ n, KRamseyOf n r s :=
by
  sorry
