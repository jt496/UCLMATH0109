import Mathlib

open Nat hiding pow_succ ne_of_lt
open Function Finset

open scoped BigOperators

/-
# In this project we will explore ternary (base 3) expansions and the Cantor set.
# Read the project pdf for details. See below for useful results from Mathlib.
-/

------------------------------------------------------------------------------


/-   # Cantor sequences
A `Cantor sequence` is `f : ℕ → {0, 2}`, however we will want to consider them as a special case
of `ternary sequences` i.e. `g : ℕ → {0, 1, 2}`

In Lean `Fin 3` is the Type `{0, 1, 2}`.

We will need to endow ternary sequences with a natural order: the lexicographic (dictionary) order.

If `f g : ℕ → {0, 1, 2}` then we say that `f < g` (in the Lex order) iff the first time f and g differ
f is smaller: i.e. `∃ N, ∀ i, i < N → f i = g i ∧ f N < g N`

We can write `Lex (ℕ → Fin 3)` to mean the type of ternary sequences with lexicographic ordering
and then define a ternary sequence to be `Cantor` as follows.
-/

/-- A ternary sequence (with Lex ordering) is `Cantor` iff it only uses 0 and 2 -/
def Cantor (f : Lex (ℕ → Fin 3)) : Prop :=
  ∀ n, f n = 0 ∨ f n = 2

namespace Cantor


-- Results about Fin
#check Fin.le_last -- Will prove `if i : Fin 3 then i ≤ 2`
#check Fin.val_two


-- Results about infinite and finite sums
#check tsum_le_tsum
#check Summable
#check summable_geometric_of_lt_one

/-- if f ≠ g are Cantor sequences and f < g then they equal 0 , 2 at the first difference-/
theorem lt_Cantor (h : f < g) (hcf : Cantor f) (hcg : Cantor g) :
    ∃ N, (∀ n < N, f n = g n) ∧ f N = 0 ∧ g N = 2 :=by
--The next line comes from the definition of `<` using the Lex ordering
  obtain ⟨N, heq , hlt⟩ := h


  sorry

/-- the nth term of a real ternary expansion is 0, 1 / 3 ^ (n + 1) or 2 / 3 ^ (n + 1) -/
noncomputable
def texpn (f : Lex (ℕ → Fin 3)) (n : ℕ) : ℝ :=(f n) * (3 : ℝ)⁻¹ ^ n.succ

/-
We will use `tsum` from Mathlib, to define the infinite sum of a ternary expansion.

The notation for `tsum` is ∑'

Note that this sum will always converge (but we will need to prove this).

In Mathlib a real sequence `c : ℕ → ℝ` is `Summable` iff the sum ∑'n,(c n) converges

The sums we will consider are all closely related to geometric series. -/

/-- the infinite sum associated to a ternary sequence i.e. the real ternary expansion -/
noncomputable
def texp (f : Lex (ℕ → Fin 3)) : ℝ :=
  ∑' k, texpn f k



/-
Given the first n terms of a ternary expansion we can place bounds on the size of its valueby considering the completions of the expansion with all 0s or all 2s.

eg, `0112210` could be extended as `01122100000000000..` or `011221022222222222...`

We will call these two sequences `tmin f n` and `tmax f n` and you could prove the obvious facts that
      `texp (tmin f n) ≤ texp f ≤ texp (tmax f n)`
                                    -/
/--
tmax f n is the ternary sequence that agrees with f up to and including n and then equals 2 forever-/
def tmax (f : Lex (ℕ → Fin 3)) (n : ℕ) : Lex (ℕ → Fin 3) := fun k => ite (k ≤ n) (f k) 2


/-- tmin is the ternary sequence that agrees with f up to and including n and then is 0 forever-/
def tmin (f : Lex (ℕ → Fin 3)) (n : ℕ) : Lex (ℕ → Fin 3) := fun k => ite (k ≤ n) (f k) 0


/-
You will need some definitional lemmas about `tmin` and `tmax`.
`split_ifs` is a useful tactic for dealing with `ite` statements.
-/

/-- if f < g as Cantor sequences then texp f < texp g -/
theorem lt_texp_of_lt_Cantor (hle : f < g) (hcf : Cantor f) (hcg : Cantor g) : texp f < texp g :=by
  sorry

open Set

/-- `texp` restricted to Cantor sequences is injective. -/
theorem Cantor_to_Real_inj : InjOn texp {f | Cantor f} :=by
  sorry

/-
Any map from ℕ to the Subtype of Cantor sequences is not surjective.

To prove this you need to give an example of a Cantor sequence that has no preimage under F

Hint: Cantor's diagonal argument.
-/


/-- Any map from ℕ to the subtype of Cantor sequences is not surjective. -/
theorem Nat_to_Cantor_not_surjective (F : ℕ → {f // Cantor f}) : ¬Surjective F  :=by
  sorry

/-
We will need the fact that there exists a Cantor sequence
to deduce that if there exists an injection from {f // Cantor f} to ℕ
then there is a surjection from ℕ to {f // Cantor f} (which we just
proved can't exist.)
-/
instance : Nonempty {f // Cantor f} :=by
  sorry

section card
open Cardinal
/-
If A and B are types then `# A ≤ # B` iff there exists an embedding from A to B.
-/
#check le_def
#check # ℕ
#check mk_image_eq_of_injOn
#check mk_set_le
#check invFun_surjective

/-
The proof of the next result should use `Nat_to_Cantor_not_surjective`
and `Cantor_to_Real_inj` rather than find the theorem in Mathlib.
-/
/-- The cardinality of ℕ is less than the cardinality of ℝ-/
theorem card_ℕ_lt_card_ℝ : # ℕ < # ℝ :=by
  sorry

end card

/-
Possible extension: state and prove a theorem characterizing when two
distinct ternary sequences have expansions that sum to the same value.
I.e. characterize those `f g : ℕ → Fin 3` satisfying `f < g` and  `texp f = texp g`
-/

end Cantor
