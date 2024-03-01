import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Powerset
import UCLMATH0109.Projects.Combinatorics.Ramsey.KColourRamsey

open Finset Nat

local notation "|" x "|" => Finset.card x

/-
In this project we prove Schur's theorem: `Schur`
For any k : ℕ, there exists N : ℕ such that in any (k+1)-colouring of {1,2,...,N},
 there is a solution of x + y = z where x,y,z receive the same colour.

We will assume Ramsey's theorem for  k-colours.
-/
#check kcolour_Ramsey

/-
See the pdf for details including a sketch of the key idea converting between colourings of ℕ
and colourings of Finset ℕ.
-/

section Schur


/-- Schur n k holds iff in any k-colouring of ℕ, there exist 0 < x,y
and a colour c such that x,y,(x+y) are have colour c and x + y < n -/
def SchurOf (n k : ℕ) : Prop := ∀ (Ncol : ℕ → Fin k),
      ∃ x y : ℕ, ∃ c : Fin k, Ncol x = c ∧ Ncol y = c ∧ Ncol (x + y) = c ∧ 0 < x ∧ 0 < y ∧ x + y < n

/--
Given a (k+1)-colouring `Ncol` of ℕ we can define a colouring `Fcol` of Finsets ℕ
by the colour of (max A - min A) or 0 if A = ∅ -/
def Fcol (Ncol : ℕ → Fin (k + 1)) : Finset ℕ → Fin (k+1) := fun A =>
  if hne : A.Nonempty then Ncol (max' A hne - min' A hne) else 0

#check mem_insert
#check mem_singleton_self
#check max'_le
#check le_min'

/-- For pairs the Fcol of {a,b} where a < b is the  Ncol of b - a -/
lemma Fcol_pair  (h : a < b) (Ncol : ℕ → Fin (k+1)) : Fcol Ncol {a, b} = Ncol (b - a) :=
by
  sorry

#check card_eq_three

/-- Any set B of 3 natural numbers can be ordered so that the pairs are edges of the triangle on B -/
lemma card_three_to_pairs {B : Finset ℕ} (h : |B| = 3) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ {a, b} ∈ B.powersetLen 2 ∧ {a, c} ∈ B.powersetLen 2 ∧ {b, c} ∈ B.powersetLen 2 :=
by
  sorry


/-- Schur's theorem  -/
theorem Schur (k : ℕ) : ∃ n : ℕ, SchurOf n k :=
by
  sorry


end Schur


/-!
Possible extension:
1. Prove some constructive lower bounds for small values of k.
2. Extend the result to solutions of other equations.
-/
