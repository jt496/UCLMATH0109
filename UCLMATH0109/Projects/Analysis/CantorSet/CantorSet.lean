import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Pi.Lex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

open Nat hiding pow_succ ne_of_lt
open Function Finset

open scoped BigOperators

/-
In this project we will explore ternary (base 3) expansions and the Cantor set.

Given an infinite ternary sequence f = t₀t₁t₂t₃...  we define the associated real
ternary expansion: `texp f = t₀/3 + t₁/3² + t₂/3³ +...`

We say that a ternary sequence is `Cantor` if it contains only 0s and 2s.

Our main results are :

1) If f and g are both Cantor sequences, and the first time f n and g n differ
we have f n < g n, then texp f < texp g : `lt_texp_of_lt_Cantor`

2) The function `texp` is injective from C to ℝ (so |C| ≤ |ℝ|): `Cantor_to_Real_inj`

3) There are no surjections from ℕ to C, so |ℕ| < |C| : `Nat_to_Cantor_not_surjective`

4) The reals are uncountable: `card_ℕ_lt_card_ℝ`
 -/

------------------------------------------------------------------------------

namespace Cantor
/-
Some useful numerical facts.
-/
theorem third_pos : 0 < (3 : ℝ)⁻¹ :=
by
  sorry

theorem third_lt_one : (3 : ℝ)⁻¹ < 1 :=
by
  sorry

theorem third_nonneg : 0 ≤ (3 : ℝ)⁻¹ :=
by
  sorry

theorem third_pow_pos (n : ℕ) : 0 < (3 : ℝ)⁻¹ ^ n.succ :=
by
  sorry

theorem two_third_pow_pos {n : ℕ}: 0 < 2 * (3 : ℝ)⁻¹ ^ n.succ :=
by
  sorry

theorem third_pow_lt_two_third {n : ℕ} : (3 : ℝ)⁻¹ ^ n.succ < 2 * (3 : ℝ)⁻¹ ^ n.succ :=
by
  sorry


/-   # Cantor sequences
A `Cantor sequence` is `f : ℕ → {0,2}`, however we will want to consider them as a special case
of `ternary sequences` i.e. `g : ℕ → {0,1,2}`

In Lean `Fin 3` is the Type `{0,1,2}`.

We will need to endow ternary sequences with a sensible order: the lexicographic (dictionary) order.

If `f g : ℕ → {0,1,2}` then we say that `f < g` (in the Lex order) iff the first time f and g differ
f is smaller: i.e. `∃ N, ∀ i, i < N → f i = g i ∧ f N < g N`

We can write `Lex (ℕ → Fin 3)` to mean the type of ternary sequences with lexicographic ordering
and then define a ternary sequence to be `Cantor` as follows.
-/

/-- A ternary sequence (with Lex ordering) is `Cantor` iff it only uses 0 and 2 -/
def Cantor (f : Lex (ℕ → Fin 3)) : Prop :=
  ∀ n, f n = 0 ∨ f n = 2


#check Fin.le_last -- Will prove `if i : Fin 3 then i ≤ 2`

/-- if f ≠ g are Cantor sequences and f < g then they equal 0 , 2 at the first difference-/
theorem lt_Cantor (h : f < g) (hcf : Cantor f) (hcg : Cantor g) :
    ∃ N, (∀ n < N, f n = g n) ∧ f N = 0 ∧ g N = 2 :=
by
  sorry

/-   # Ternary expansions

Given a ternary sequence eg 0,1,2,1,2,0,... we would like to interpret it as a real ternary
expansion.

We do this in the obvious way, associating the sequence x₀,x₁,x₂,x₃,... with the expansion
    x₀/3 + x₁/3² + x₂/3² + ...

First we introduce the real sequence whose infinite sum will be the ternary expansion. -/
/-- the nth term of a real ternary expansion is 0, 1/3^(n+1) or 2/3^(n+1) -/
noncomputable
def texpn (f : Lex (ℕ → Fin 3)) (n : ℕ) : ℝ :=(f n)*(3 : ℝ)⁻¹ ^ n.succ

/-- the nth term of the ternary expansion is .. -/
@[simp]
theorem texpn' : texpn f n = (f n)*(3 : ℝ)⁻¹ ^ n.succ:= rfl

/-- if the ternary sequences f and g agree at n then so do the ternary expansions -/
theorem texpn_eq (h : f n = g n) : texpn f n = texpn g n :=
by
  sorry


/-- every term of a ternary expansion is non-negative-/
theorem texpn_nonneg (f : ℕ → Fin 3) (n : ℕ) : 0 ≤ texpn f n :=
by
  sorry

/-- the nth term of a ternary expansion is at most 2/3^{n+1} -/
theorem texpn_bdd (f : ℕ → Fin 3) (n : ℕ) : texpn f n ≤ 2 * (3 : ℝ)⁻¹ ^ n.succ :=
by
  sorry

/-- if f n ≤ g n then the corresponding real terms are also ≤ -/
theorem texpn_le (h : f n ≤ g n) : texpn f n ≤ texpn g n :=
by
  sorry



/-- if f n < g n then the corresponding real terms are also < -/
theorem texpn_lt (h : f n < g n) : texpn f n < texpn g n :=
by
  sorry


/-
We will use `tsum` from Mathlib, to define the infinite sum of a ternary expansion.

The notation for tsum is ∑'

Note that this sum will always converge (but we will need to prove this).

In Mathlib a real sequence `c : ℕ → ℝ` is `Summable` iff the sum ∑'n,(c n) converges

The sums we will consider are all closely related to geometric series. -/
/-- the infinite sum associated to a ternary sequence i.e. the real ternary expansion -/
noncomputable
def texp (f : Lex (ℕ → Fin 3)) : ℝ :=
  ∑' k, texpn f k

#check summable_geometric_of_lt_1

/-- ∑ 1/3^n is summable-/
theorem summable_thirds : Summable (fun n : ℕ => (3 : ℝ)⁻¹ ^ n) :=
by
  sorry

#check tsum_geometric_of_lt_1

/-- ∑ 1/3ⁿ  = 3/2 -/
theorem tsum_thirds : (∑' (n : ℕ), (3 : ℝ)⁻¹ ^ n )= 3 * 2⁻¹ :=
by
  sorry

#check tsum_mul_left

/-- the tsum of the shifted sequence is 3/(2*3ᵏ)-/
theorem tsum_thirds_shift (k : ℕ) : (∑' n, (3 : ℝ)⁻¹ ^ (k + n)) = (3 : ℝ)⁻¹ ^ k * 3 * 2⁻¹ :=
by
  sorry

#check Summable.mul_left

/-- ∑ 2/3ⁿ is summable-/
theorem summable_two_thirds : Summable fun n : ℕ => 2 * (3 : ℝ)⁻¹ ^ n :=
by
  sorry

/-- ∑ 2/3ⁿ  = 3 -/
theorem tsum_two_thirds : (∑' n : ℕ, 2 * (3 : ℝ)⁻¹ ^ n) = 3 :=
by
  sorry

/-- ∑ 2/3^(n+k)  = 3^(-k+1) -/
theorem tsum_two_thirds_shift (k : ℕ) : (∑' n, 2 * (3 : ℝ)⁻¹ ^ (k.succ + n)) = (3 : ℝ)⁻¹ ^ k :=
by
  sorry

/-- ∑ 2/3^{n+1} is summable-/
theorem summable_two_thirds_succ : Summable fun n : ℕ => 2 * (3 : ℝ)⁻¹ ^ n.succ :=
by
  sorry

-- For our next result we need to use the comparison test for convergence
#check summable_of_nonneg_of_le

/-- Any ternary expansion is summable -/
theorem summable_texp (f : ℕ → Fin 3) : Summable (texpn f) :=
by
  sorry

/-
Given the first n terms of a ternary expansion we can place bounds on the size of its value
by considering the completions of the expansion with all 0s or all 2s.

eg, `0112210` could be extended as `0112210`0000000000.. or `0112210`22222222222...

We will call these two sequences `tmin f n` and `tmax f n` and prove the obvious fact that
      `texp (tmin f n) ≤ texp f ≤ texp (tmax f n)` in all cases.                              -/
/--
tmax f n is the ternary sequence that agrees with f upto and including n and then equals 2 forever-/
def tmax (f : Lex (ℕ → Fin 3)) (n : ℕ) : Lex (ℕ → Fin 3) := fun k => ite (k ≤ n) (f k) 2

/-- f k ≤ tmax k for all k-/
theorem le_tmax (k : ℕ):  f k ≤ tmax f n k :=
by
  sorry

/-- every term of the expansion of f is ≤ the expansion of tmax f n-/
theorem texpn_le_tmax (f : ℕ → Fin 3) (n k : ℕ) : texpn f k ≤ texpn (tmax f n) k :=
by
  sorry

#check tsum_le_tsum

/-- the infinite sum  of f is ≤ the sum of tmax f n-/
theorem texp_le_tmax (f : ℕ → Fin 3) (n : ℕ) : texp f ≤ texp (tmax f n) :=
by
  sorry

/-- The ternary sequence `tmax f n` agrees with `f` up to and including nth term -/
theorem tmax_eq (hk : k ≤ n) :  tmax f n k = f k := by rw [tmax];  split_ifs; rfl

/-- The real expansion `texpn (tmax f n)` agrees with `texpn f` up to and including the nth term -/
theorem texpn_tmax_eq (f : ℕ → Fin 3) (hk : k ≤ n) :  texpn (tmax f n) k = texpn f k :=
by
  sorry

/-- every term after n is two in tmax f n -/
theorem tmax_two (f : ℕ → Fin 3) (hk : n < k) : tmax f n k = 2 :=
by
  sorry


/-- if f ≠ tmax f n then f < tmax f n -/
theorem lt_of_ne_tmax (hne : f ≠ tmax f n) : f < tmax f n :=
by
  sorry

/-- every term in the expansion of tmax f n after n is 2/3^k.succ -/
theorem texpn_tmax_two (f : ℕ → Fin 3) (n k : ℕ) (hk  : n < k) :
   texpn (tmax f n) k = 2 * (3 : ℝ)⁻¹ ^ k.succ :=
by
  sorry

/-- tmin is the ternary sequence that agrees with f up to and including n and then is 0 forever-/
def tmin (f : Lex (ℕ → Fin 3)) (n : ℕ) : Lex (ℕ → Fin 3) := fun k => ite (k ≤ n) (f k) 0

/-- tmin f n k ≤ f k for all k-/
theorem tmin_le (k : ℕ): tmin f n k ≤ f k :=
by
  sorry

/-- tmin agrees with f up to n -/
theorem tmin_eq (hk : k ≤ n):  tmin f n k = f k :=
by
  sorry

/-- tmin is zero after nth term -/
theorem tmin_zer (f : ℕ → Fin 3) (hk : n < k) :  tmin f n k = 0 :=
by
  sorry

/-- if tmin f n ≠ f then it is smaller (as a ternary sequence)-/
theorem tmin_lt_of_ne (hne : tmin f n ≠ f) : tmin f n < f :=
by
  sorry

/-- every term of the expansion of tmin f n is zer after the nth -/
theorem texpn_tmin_zer (f : ℕ → Fin 3) (hk : n < k) : texpn (tmin f n) k = 0 :=
by
  sorry

/-- f and tmin expansions agree upto the nth term -/
theorem texpn_tmin_eq (f : ℕ → Fin 3) (hk  : k ≤ n) : texpn (tmin f n) k = texpn f k :=
by
  sorry

/-- texpn (tmin f n) k ≤   texpn f k for all k -/
theorem tmin_le_texpn (f : ℕ → Fin 3) (n k : ℕ) :  texpn (tmin f n) k ≤ texpn f k :=
by
  sorry

/-- texp (cmnin f n) ≤ texp f -/
theorem tmin_le_texp (f : ℕ → Fin 3) (n : ℕ) : texp (tmin f n) ≤ texp f :=
by
  sorry

#check sum_congr
#check mem_range_succ_iff

/-- sum of tmin and tmax agree up to N ie as finite sums -/
theorem texpn_min_eq_max_range (f : ℕ → Fin 3) (N : ℕ) :
    ∑ k in range N.succ, texpn (tmin f N) k = ∑ k in range N.succ, texpn (tmax f N) k :=
by
  sorry

#check tsum_zero
#check tsum_congr

/-- the tail of tmin expansion is zero -/
theorem texp_tmin_tail_eq_zero (f : ℕ → Fin 3) (N : ℕ) : (∑' k, texpn (tmin f N) (k + N.succ)) = 0 :=
by
  sorry

/-- the tail of the tmax expansion is 1/3^N.succ (geometric sum)-/
theorem texp_tmax_tail_eq_geo (f : ℕ → Fin 3) (N : ℕ) :
    (∑' k, texpn (tmax f N) (k + N.succ)) = (3 : ℝ)⁻¹ ^ N.succ :=
by
  sorry

-- `sum_add_tsum_nat_add` allows us to split an infinite sum into sum over first k terms + the rest
#check sum_add_tsum_nat_add

/-- tmax and tmin expansions differ by exactly 1/3^N.succ -/
theorem texp_tmax_eq_tmin_add (f : ℕ → Fin 3) (N : ℕ) :
    texp (tmax f N) = texp (tmin f N) + (3 : ℝ)⁻¹ ^ N.succ :=
by
  sorry

/-- if f and g agree on n < N then tmax f N and tmax g N agree everywhere except N -/
theorem fgmax_eq (heq : ∀ n < N, f n = g n) (hn : n ≠ N): tmax f N n = tmax g N n :=
by
  sorry

/-- if f and g agree before the Nth term then `texp tmax f N` and `texp tmax g N` only differ by
the difference of their Nth terms -/
theorem texp_fgmax_eq (heq : ∀ n < N, f n = g n) :
    texp (tmax f N) = texp (tmax g N) - texpn g N + texpn f N :=
by
  sorry

/-- If f and g agree before the Nth term then texp f and texp g can only differ by at most
the difference at their Nth terms + 1/3^(N+1) -/
theorem texp_diff_le (heq : ∀ n < N, f n = g n) :
    texp f ≤ texp g + (3 : ℝ)⁻¹ ^ N.succ - texpn g N + texpn f N :=
by
  sorry

/-- if f < g as Cantor sequences then texp f < texp g -/
theorem lt_texp_of_lt_Cantor (hle : f < g) (hcf : Cantor f) (hcg : Cantor g) : texp f < texp g :=
by
  sorry

open Set

/-- `texp` restricted to Cantor sequences is injective. -/
theorem Cantor_to_Real_inj : InjOn texp {f | Cantor f} :=
by
  sorry

/-
Any map from ℕ to the subtype of Cantor sequences is not surjective.

To prove this you need to give an example of a Cantor sequence that has no preimage under F

Hint: Cantor's diagonal argument.
-/

#check funext_iff

/-- Any map from ℕ to the subtype of Cantor sequences is not surjective. -/
theorem Nat_to_Cantor_not_surjective (F : ℕ → {f // Cantor f}) : ¬Surjective F  :=
by
  sorry

/-
We will need the fact that there exists a Cantor sequence
to deduce that if there exists an injection from {f // Cantor f} to ℕ
then there is a surjection from ℕ to {f // Cantor f} (which we just
proved can't exist.)
-/
instance : Nonempty {f // Cantor f} :=
by
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
theorem card_ℕ_lt_card_ℝ : # ℕ < # ℝ :=
by
  sorry

end card


/-
Possible extension: characterise exactly when two different ternary sequences
have the same sum.
  [You may want to add some extra lemmas before proving this.]
-/
theorem lt_of_texp_eq (hlt : f < g) (he : texp f = texp g) :
    ∃ N, ∀ n < N, f n = g n ∧
       (f N = 0 ∧ g N = 1 ∨ f N = 1 ∧ g N = 2) ∧ tmax f N = f ∧ tmin g N = g :=
by
  sorry

end Cantor
