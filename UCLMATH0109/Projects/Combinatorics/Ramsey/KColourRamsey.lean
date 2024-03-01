import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Powerset
import UCLMATH0109.Projects.Combinatorics.Ramsey.Graph2Col

open Finset Nat

local notation "|" x "|" => Finset.card x

/-
We prove the k-colour version of Ramsey's theorem: `kcolour_Ramsey`,
assuming the 2-colour version.

Given a set A ⊆ ℕ we will refer to A^(2) (the set of all unordered pairs from A) as a `clique`.

A (k+1)-colouring is `col : Finset ℕ → Fin (k+1)`

Note that `Fin (k+1)` is the type of natural numbers less than k + 1.
If `a : Fin (k+1)` then `a` is a pair `a.val : ℕ` and `a.isLt : a.val < k + 1`

-/

/-
We need the following definitions and results from
Projects.Combinatorics.Ramsey.Graph2Col: -/
#check monoOn
#check RamseyCol
#check RamseyOf
#check Ramsey_symm
#check mono_RamseyOf
#check Ramsey_zero
#check Erdos_Szekeres_Ramsey


section kColour

/-- A k-colouring `col : Finset ℕ  → Fin k` is Kmono on a set A iff
every pair in A^(2) receives the same colour c -/
def Finset.KmonoOn (A : Finset ℕ) (col : Finset ℕ → Fin k) (c : Fin k) : Prop :=
  ∀ e, e ∈ A.powersetLen 2 → col e = c

/--
A k-colouring col is kRamseyCol for n s iff for every set of size at least n
there is a subset A and a colour
c such that s(c) ≤ |A| and every pair in A^(2) is coloured with colour c -/
def kRamseyCol (col : Finset ℕ → Fin k) (n : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ {V : Finset ℕ}, n ≤ |V| → ∃ A, ∃ c, A ⊆ V ∧ A.KmonoOn col c ∧ s c ≤ |A|

/-- Given `s : Fin k → ℕ`, N is kRamseyOf s if every k-colouring of ℕ is a
kRamseyCol for N and s -/
def kRamseyOf (N : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ (col : Finset ℕ → Fin k), kRamseyCol col N s

/-

We need to introduce three definitions for the proof (see pdf for details):

If `s : Fin (k + 1) → ℕ` describes the sizes of the k + 1 possible cliques we
define `kSizes s` as is its restriction to the first k sizes.

If `col : Finset ℕ  → Fin (k+1)` is a (k+1)-colouring then we define an associated
 2-colouring `kto2`. This is given by recolouring everything that received colour k with
 colour 1 and everything else with colour 0.

We will also need to convert a (k+1)-colouring which only uses colour 0,...,k-1 on
A^(2) into a k-colouring. We call this `kcol` below.
-/

/-- the first k sizes of cliques -/
def kSizes (s : Fin (k+1) → ℕ) : Fin k → ℕ := fun c => s c


/-
Note that `Fin.last k` is the largest element of `Fin (k + 1)` i.e. `k` as
a term of type `Fin (k + 1)`
-/

/--
the 2-colouring associated to a (k+1)-col given by
c ↦ 0 for all c < k and  k ↦ 1  -/
def kto2 (col : Finset ℕ → Fin (k+1)) : Finset ℕ → Fin 2 :=
  fun e => if col e < Fin.last k then 0 else 1

/-- Definitional lemma for kto2 -/
@[simp]
lemma kto2' (col : Finset ℕ → Fin (k+1)) (e : Finset ℕ) :
  kto2 col e = if (col e < Fin.last k) then 0 else 1 :=
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

/-
In order to define `kcol` below we need to know that `Fin k` is nonempty,
which is equivalent to `k ≠ 0`.
-/
variable {k : ℕ} [NeZero k]

/-- the k-colouring formed from a (k+1)-colouring that
    only uses colours 0,..,k-1 on pairs in A -/
def kcol {col : Finset ℕ → Fin (k+1)} (hm : monoOn A (kto2 col) 0)  :
  Finset ℕ → Fin k :=
by
  intro e
  by_cases he : e ∈ A.powersetLen 2
  · have hcol := hm e he
    use col e
    apply kto2_zero hcol
  · exact 0


/-- Definitional lemma for kcol-/
@[simp]
lemma kcol' {col : Finset ℕ → Fin (k+1)} (hm : monoOn A (kto2 col) 0):
 ∀ e ∈ A.powersetLen 2, (kcol hm e : ℕ) = col e :=
by
  sorry


/-- if n is Ramsey for s, t and n ≤ m then m is also Ramsey -/
lemma mono_kRamseyOf  {s : Fin k → ℕ} (h : kRamseyOf n s) (hm : n ≤ m) :
    kRamseyOf m s :=
by
  sorry


#check powersetLen_mono
#check Fin.cast_val_eq_self
/-- If the kto2 colouring is red on A^(2) and  a ≤ |A| where `kRamseyOf a (kSizes s)`
then A contains an c-coloured clique of size s_c for   -/
lemma kmono_kto2_zero {col : Finset ℕ → Fin (k+1)} {s : Fin (k+1) → ℕ}
    (hm : monoOn A (kto2 col) 0) (kra : kRamseyOf a (kSizes s)) (hA : a ≤ |A|)  :
    ∃ c, ∃ B, B ⊆ A ∧ B.KmonoOn  col c ∧ s c ≤ |B| :=
by
  sorry

/-- If the kto2 colouring is blue on A^(2) then the original (k+1)-colouring was k  -/
lemma kmono_kto2_one {col : Finset ℕ → Fin (k+1)} {A: Finset ℕ} (hm : A.monoOn (kto2 col) 1) :
    A.KmonoOn col k :=
by
  sorry

/-- The inductive step for (k+1)-colours see pdf for sketch of proof -/
lemma kRamsey_step (s : Fin (k+1) → ℕ)  :
    kRamseyOf a (kSizes s) → RamseyOf b a (s k) → kRamseyOf b s :=
by
  sorry

end with_kNeZero

/-
We already have the 2-colour version of the Ramsey's theorem but we
can also prove it directly and easily for 0 or 1 colours.
-/

#check Fin.elim0 -- Given an element of Fin 0 you can prove anything!

/-- 0-colour Ramsey number -/
lemma kRamseyOf_zero (s : Fin 0 → ℕ) : kRamseyOf 0 s :=
by
  sorry

/- Fin 1 consists of one colour 0 -/
#check eq_iff_true_of_subsingleton

/-- 1-colour Ramsey number -/
lemma kRamseyOf_one (s : Fin 1 → ℕ) : kRamseyOf (s 0) s :=
by
  sorry

/--
Ramsey's theorem for k-colours -/
theorem kcolour_Ramsey (s : Fin k → ℕ) : ∃ n, kRamseyOf n s :=
by
  sorry

end kColour

/-!
Possible extension: prove some constructive lower bounds for k = 3.
(See end of Ramsey/Graph2Col  for inspiration.)
-/
