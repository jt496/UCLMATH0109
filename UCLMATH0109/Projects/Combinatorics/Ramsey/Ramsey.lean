import Mathlib

open Finset Nat
local notation "|" x "|" => Finset.card x

/-
# This file contains 3 separate related projects in Ramsey theory. Please see the
# projects pdf for details of each project and the mathematics involved.
-/

/-
---------------------------------------------------------------------------------
  # Project 1: Ramsey's Theorem for two colours
---------------------------------------------------------------------------------

The main result in this project is the Erdos-Szekeres upper bound for the 2-colour
Ramsey number (we state it this way to avoid the need for ℕ subtraction which can
be painful in Lean). `Erdos_Szekeres_Ramsey`

    R(s + 1, t + 1) ≤ (s + t).choose s

The key lemma  is `Ramsey_step`:
On the way we prove R(s + 1,t + 1) ≤ R(s,t + 1) + R(s + 1,t).

We use Fin 2 = {0,1} as our two colours - 0 as red and 1 as blue.
(We use this rather than the more obvious Bool = {true,false} since we
want to extend to more colours later.)

Note that if `a : Fin 2` then `a` is a pair `a = ⟨a.val,a.isLt⟩` where
`a.val : ℕ` and `a.isLt` is a proof that `a < 2`

We define 2-colourings as maps from all finite subsets of ℕ to {0,1}
i.e.
 `col : Finset ℕ → Fin 2`

We only really care (at the moment) about the colour given to pairs {x,y} where x ≠ y

If `A : Finset ℕ` then `A.powersetCard 2` is the `Finset (Finset ℕ)` of all subsets of A
  of size 2. [We use the notation `A^(2)` for this in these comments.]
-/
section Mathlib_examples

variable {A : Finset ℕ} {a n : ℕ}
#check A.powersetCard 2 -- the collection of subsets of size 2 from A
#eval ({0,2,4,6,7} : Finset ℕ).powersetCard 2
#check insert n A -- The Finset formed by inserting n into A (i.e. A ∪ {n})
#check insert n ({a} : Finset ℕ) -- this is Lean's definition of {n, a} as a Finset ℕ
#eval ({0,1,4} : Finset ℕ).erase 4 -- erase will remove an element from a Finset

end Mathlib_examples

section twocolours


/-- A 2-colouring `col` is `monoOn` a set `A` iff every pair in the set receives the same colour `c`  -/
@[reducible]
def Finset.monoOn (A : Finset ℕ) (col : Finset ℕ → Fin 2) (c : Fin 2) :  Prop:=
∀ (e : Finset ℕ), e ∈ A.powersetCard 2 → col e = c


/-- A 2-colouring `col` satisfies `RamseyCol col N s t` if every set of size at least `N`
 contains an `s`-set with all pairs red or a `t`-set with all pairs blue -/
def RamseyCol (col : Finset ℕ → Fin 2) (N s t : ℕ) : Prop := ∀ {V : Finset ℕ}, N ≤ |V| →
  ∃ (A : Finset ℕ), A ⊆ V ∧ ((A.monoOn col 0 ∧ s ≤ |A|) ∨ (A.monoOn col 1 ∧ t ≤ |A|))

/-- `RamseyOf N s t` holds if every 2-colouring is a `RamseyCol` for `N, s, t` -/
def RamseyOf (N s t : ℕ): Prop:= ∀ (col : Finset ℕ → Fin 2), RamseyCol col N s t

/-
Take a moment to properly understand the definitions above.
In particular, `RamseyOf` is slightly different to what you might expect,
but allows us to avoid some tricky issues in Lean.
-/

/-- given a 2-colouring col, a colour `c : Fin2 , V : Finset ℕ`  and `n : ℕ`
the `nbhd col c V n` is `{ w ∈ V | col {w, n} = c}` as a `Finset ℕ` -/
def nbhd  (col : Finset ℕ → Fin 2) (c : Fin 2) (V : Finset ℕ) (n : ℕ) :
  Finset ℕ := V.filter (fun w => col (insert w {n}) = c)

-- The next definition may be useful when you try to prove `symmetry` for `RamseyOf`
/- `notC` is the opposite colour to colour  `c` -/
def notC (c : Fin 2) : Fin 2 := if (c = 0) then 1 else 0

/-- flip all the colours in a 2-colouring -/
def notCol (col : Finset ℕ → Fin 2) : Finset ℕ → Fin 2 :=  notC ∘ col


/-- if N is Ramsey for s,t and N ≤ M then M is also Ramsey for s,t -/
lemma mono_RamseyOf  (h : RamseyOf N s t) (hm: N ≤ M) : RamseyOf M s t :=by
  sorry

/-
The next lemma is very easy, but can also be seen as the version of
Ramsey's theorem for singletons (rather than pairs) and may be useful later.

If you colour {1,...,c + d} red/blue and a + b - 1 ≤ c + d then you
either coloured at least a elements red or at least b elements blue.
-/
#check add_lt_add_of_le_of_lt
#check le_pred_of_lt
/-- The inequality we require for the inductive step in Ramsey's theorem -/
lemma nbhd_cases :  a + b - 1 ≤ c + d  → a ≤ c ∨ b ≤ d:=by
  sorry

/-
The next result is the key step in the proof of Ramseys theorem that
 R (s+1, t+1) ≤ R(s,t+1) + R(s+1,t) but phrased in terms of `RamseyOf`
-/

/-- Key step R (s+1,t+1) ≤ R(s,t+1) + R(s+1,t) -/
lemma Ramsey_step (hab : 1 ≤ a + b):
    RamseyOf a s (t + 1) → RamseyOf b (s + 1) t → RamseyOf (a + b) (s + 1) (t + 1):=by
  sorry

/-- Symmetry in (s,t) -/
lemma Ramsey_symm {n s t : ℕ} : RamseyOf n s t → RamseyOf n t s:=by
  sorry


/-- R(0,t) ≤ 0 -/
lemma Ramsey_zero (t : ℕ): RamseyOf 0 0 t:=by
  sorry



/-- R(1,t) ≤ 1 -/
lemma Ramsey_one (t : ℕ): RamseyOf 1 1 t:=by
  sorry


/-
For the main theorem you will need to use facts about Nat.choose
-/

/-- The Erdos--Szekeres version of Ramsey's theorem -/
theorem Erdos_Szekeres_Ramsey (s t : ℕ)  : RamseyOf ((s + t).choose s) (s + 1) (t + 1) :=by
  induction s generalizing t with
  | zero =>
    sorry
  | succ s hs =>
    induction t generalizing s with
    | zero =>
      sorry
    | succ t ht =>
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
(∀ V ∈ (range n).powersetCard s,¬V.monoOn col 0) ∧ (∀ V ∈ (range n).powersetCard t,¬V.monoOn col 1)

#check card_range

theorem not_RamseyOf_exists (hcolbad: ∃ (col : Finset ℕ → Fin 2), not_RamseyOf_col n s t col):
 ¬ RamseyOf n s t:= by
  sorry

lemma R34_gt_8 : ¬ RamseyOf 8 3 4 :=by
  sorry

lemma R44_gt_17 : ¬ RamseyOf 17 4 4 :=by
  sorry


end twocolours



section kcolours

/-
---------------------------------------------------------------------------------
  # Project 2: Ramsey's Theorem for k-colours
---------------------------------------------------------------------------------

We prove the k-colour version of Ramsey's theorem: `kcolour_Ramsey`,
assuming the 2-colour version.

Given a set A ⊆ ℕ we will refer to A^(2) (the set of all pairs from A) as a `clique`.

A (k + 1)-colouring is `col : Finset ℕ → Fin (k + 1)`

Note that `Fin (k + 1)` is the type of natural numbers less than k + 1.
So `a : Fin (k+1)` then `a` is a pair `a.val : ℕ` and `a.isLt : a.val < k + 1`

-/

section Mathlib_examples

variable {A : Finset ℕ} {a n : ℕ}
#check A.powersetCard 2 -- the collection of subsets of size 2 from A
#eval ({0,2,4,6,7} : Finset ℕ).powersetCard 2
#check insert n A -- The Finset formed by inserting n into A (i.e. A ∪ {n})
#check insert n ({a} : Finset ℕ) -- this is Lean's definition of {n, a} as a Finset ℕ
#eval ({0,1,4} : Finset ℕ).erase 4 -- erase will remove an element from a Finset

end Mathlib_examples

/-
We need the following definitions and results from the two colour Ramsey
project in the previous section of this file. (You don't need to prove these.)
-/

#check monoOn
#check RamseyCol
#check RamseyOf
#check Ramsey_symm
#check mono_RamseyOf
#check Ramsey_zero
#check Erdos_Szekeres_Ramsey



/-- A k-colouring `col : Finset ℕ  → Fin k` is Kmono on a set A iff
every pair in A^(2) receives the same colour c -/
def Finset.KmonoOn (A : Finset ℕ) (col : Finset ℕ → Fin k) (c : Fin k) : Prop :=
  ∀ e, e ∈ A.powersetCard 2 → col e = c

/--
A k-colouring col is kRamseyCol for n s iff for every set of size at least n
there is a subset A and a colour c such that s(c) ≤ |A| and every pair
in A^(2) is coloured with colour c -/
def kRamseyCol (col : Finset ℕ → Fin k) (n : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ {V : Finset ℕ}, n ≤ |V| → ∃ A, ∃ c, A ⊆ V ∧ A.KmonoOn col c ∧ s c ≤ |A|

/-- Given `s : Fin k → ℕ`, N is kRamseyOf s if every k-colouring of ℕ is a
kRamseyCol for N and s -/
def kRamseyOf (N : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ (col : Finset ℕ → Fin k), kRamseyCol col N s

/-

We need to introduce three definitions for the proof (see pdf for details):

If `s : Fin (k + 1) → ℕ` describes the sizes of the k + 1 possible cliques we would
like to find then `kSizes s` is its restriction to the first k sizes.

If `col : Finset ℕ  → Fin (k+1)` is a (k+1)-colouring then we define an associated
 2-colouring `kto2`. This is given by recolouring everything that received colour k with
 colour 1 and everything else with colour 0. (This is the color-blindness argument.)

We will also need to convert a (k+1)-colouring which only uses colour 0,...,k-1 on
A^(2) into a k-colouring. We call this `kcol` below.
-/

/-- the first k sizes of cliques -/
def kSizes (s : Fin (k+1) → ℕ) : Fin k → ℕ := fun c => s c


/-
Note that `Fin.last k` is the largest element of `Fin (k + 1)` i.e. `k` as
a term of type `Fin (k + 1)`
-/

#check Fin.last_le_iff
#check Fin.eq_last_of_not_lt
#check Fin.cast_nat_eq_last

/--
the 2-colouring associated to a (k+1)-col given by
c ↦ 0 for all c < k and  k ↦ 1  -/
def kto2 (col : Finset ℕ → Fin (k+1)) : Finset ℕ → Fin 2 :=
  fun e => if col e < Fin.last k then 0 else 1


/-- If `kto2 col e = 0` then `col e` is one of the first k colours -/
@[simp]
lemma kto2_zero {col : Finset ℕ → Fin (k+1)} {e : Finset ℕ} (h0 : kto2 col e = 0) : col e < Fin.last k:=by
  sorry


section with_kNeZero
variable {k : ℕ} [NeZero k]-- we need k ≠ 0 for the next definition to make sense (Fin 0 is empty)

/-- the k-colouring formed from a (k+1)-colouring that
    only uses colours 0,..,k-1 on pairs in A -/
def kcol {col : Finset ℕ → Fin (k+1)} (hm : monoOn A (kto2 col) 0)  :
  Finset ℕ → Fin k :=by
  intro e
  by_cases he : e ∈ A.powersetCard 2
  · have hcol := hm e he
    use col e
    apply kto2_zero hcol
  · exact 0

#check powersetCard_mono
#check Fin.cast_val_eq_self


/-- The inductive step for (k+1)-colours see pdf for sketch of proof -/
lemma kRamsey_step (s : Fin (k + 1) → ℕ)  :
    kRamseyOf a (kSizes s) → RamseyOf b a (s k) → kRamseyOf b s :=by
    sorry

end with_kNeZero

/-
We already have the 2-colour version of the Ramsey's theorem but we
can also prove it directly and easily for 0 or 1 colours.
-/

#check Fin.elim0 -- Given an element of Fin 0 you can prove anything!

/-- 0-colour Ramsey number -/
lemma kRamseyOf_zero (s : Fin 0 → ℕ) : kRamseyOf 0 s :=by
  sorry

/- Fin 1 consists of one colour 0 -/
#check eq_iff_true_of_subsingleton
/-- 1-colour Ramsey number -/
lemma kRamseyOf_one (s : Fin 1 → ℕ) : kRamseyOf (s 0) s :=by
  sorry

/--
Ramsey's theorem for k-colours -/
theorem kcolour_Ramsey (s : Fin k → ℕ) : ∃ n, kRamseyOf n s :=by
  sorry

end kcolours

/-!
Possible extension: prove some constructive lower bounds for k = 3.
Alternatively use your result to prove Schur's theorem below.
-/




section schur



/-
---------------------------------------------------------------------------------
  # Project 3: Schur's Theorem
---------------------------------------------------------------------------------

In this project we prove Schur's theorem: `Schur`
For any k : ℕ, there exists N : ℕ such that in any k-colouring of {1,2,...,N},
 there is a solution of x + y = z where x,y,z receive the same colour.

We will assume Ramsey's theorem for  k-colours.
-/
#check kcolour_Ramsey

/-- `Schur n k` holds iff in any k-colouring of ℕ, there exist 0 < x,y
and a colour c such that x,y,(x+y) are all colour c and x + y < n -/
def SchurOf (n k : ℕ) : Prop := ∀ (Ncol : ℕ → Fin k),
      ∃ x y : ℕ, ∃ c : Fin k, Ncol x = c ∧ Ncol y = c ∧ Ncol (x + y) = c ∧ 0 < x ∧ 0 < y ∧ x + y < n

/--
Given a (k + 1)-colouring `Ncol` of ℕ we can define a colouring `Fcol` of Finsets ℕ
by the colour of (max A - min A) or 0 if A = ∅ -/
def Fcol (Ncol : ℕ → Fin (k + 1)) : Finset ℕ → Fin (k + 1) := fun A =>
  if hne : A.Nonempty then Ncol (max' A hne - min' A hne) else 0


section Mathlib_examples

variable {A : Finset ℕ} {a n : ℕ}
#check A.powersetCard 2 -- the collection of subsets of size 2 from A
#eval ({0,2,4,6,7} : Finset ℕ).powersetCard 2
#check insert n A -- The Finset formed by inserting n into A (i.e. A ∪ {n})
#check insert n ({a} : Finset ℕ) -- this is Lean's definition of {n, a} as a Finset ℕ
#eval ({0,1,4} : Finset ℕ).erase 4 -- erase will remove an element from a Finset

end Mathlib_examples

/-- Any set of 3 natural numbers can be ordered and the pairs are edges of the triangle on B -/
lemma card_three_to_pairs {B : Finset ℕ} (h : |B| = 3) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ {a, b} ∈ B.powersetCard 2 ∧ {a, c} ∈ B.powersetCard 2 ∧ {b, c} ∈ B.powersetCard 2 :=by
    sorry

/-- Schur's theorem  -/
theorem Schur (k : ℕ) : ∃ n : ℕ, SchurOf n k :=by
  sorry



end schur


/-!
Possible extension:
1. prove some constructive lower bounds for small values of k.
2. Extend to other equations.
3. Prove that for any n ≥ 1 there exists pₙ such that for any prime p ≥ pₙ
there exist non-trivial solutions to `xⁿ + yⁿ = zⁿ mod p`.
-/
