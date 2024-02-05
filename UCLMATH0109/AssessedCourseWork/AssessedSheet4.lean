import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import UCLMATH0109.Course._3_analysis_playground.E2_let
/-
  # Assessed Sheet 4
   Covering material from sheet3D,E,F
  `calc` `Finsets` `let` `norm_cast` `push_cast`
-/

open NNReal -- ℝ≥0 the type of nonnegative real numbers \nnr
/-
ℝ≥0 is a Subtype which means that if `x : ℝ≥0`
then x consists of real number together with a proof that it is nonnegative.
-/

variable (x : ℝ≥0)
#check x          -- x : ℝ≥0
#check x.val      -- ↑x : ℝ
#check x.prop     -- Subtype.prop x : 0 ≤ ↑x


/-

Tactics that will be useful include :
`norm_num`, `push_cast`, `norm_cast`, `rel`, `linarith`, `ring`,
 `field_simp`, `apply?`

-/

/--
Bernouilli's inequality: `1 + n*a ≤ (1 + a) ^ n`
-/
-- 01
lemma bernouilli₁ (n : ℕ) (a : ℝ≥0) : 1 + n * a ≤ (1 + a)^n:=
by
  induction n with
  | zero => sorry
  | succ n ih =>
    calc
    _   =   1 + n*a + a           := by sorry
    _   ≤   1 + n*a + a  + n*a^2  := by sorry
    _   =   (1 + n*a) * (1 + a)   := by sorry
    _   ≤   (1 + a)^n * (1 + a)   := by sorry
    _   =   (1 + a)^(n + 1)       := by sorry

/-
Recall the binomial coefficient `n.choose k`, where `k,n ∈ ℕ, usually
we would define this as `n.choose k = n! / (k! (n - k)!)`.

In Lean it has the following (equivalent) definition that is easier to work with:

def choose : ℕ → ℕ → ℕ
  | _, 0 => 1                                     -- n.choose 0 = 1
  | 0, _ + 1 => 0                                 -- 0.choose (k + 1) = 0
  | n + 1, k + 1 => choose n k + choose n (k + 1) -- Pascal's identity
-/

-- We list some results that you *may* wish to use later in this sheet

#check Nat.choose_succ_succ -- `(n + 1).choose (k + 1) = n.choose k + n.choose (k + 1)`

#check Nat.choose_one_right -- `n.choose 1 = n`

#check add_le_add_right

#check mul_le_mul_left'

/-
In our next example both `n = 0` and `n = 1` are special cases so we do `induction n`,
followed by `cases n`. You will probably need to use `bernouilli₁` at some point.
-/

-- 02
lemma bernouilli₂ (n : ℕ) (a : ℝ≥0): (n.choose 2) * a^2 ≤ (1 + a)^n :=
by
  induction n with
  | zero => sorry
  | succ n ih =>
    cases n with
    | zero => sorry
    | succ n =>
      have : (n + 1) * a ^ 2 ≤ a * (1 + a) ^ (n + 1)
      · calc
          _ = a* ((n + 1)*a)      := by sorry
          _ ≤ a*( 1 + (n + 1)*a)  := by sorry
          _ ≤ _                   := by sorry
-- Work out the proof on paper and add extra lines to this `calc` block as required
      calc
        _ = ((n+1).choose 1 + (n+1).choose 2)*a^2 := by sorry
        _ ≤ _                                     := by sorry



open Finset BigOperators


-- We introduce the notation `|S|` for the cardinality of a Finset S

local notation "|" x "|" => Finset.card x

variable {α : Type} [DecidableEq α]

#check card_le_of_subset

#check mem_union

-- 03
example  (S T U : Finset α) (hst : Disjoint S T) (hsu : S ⊆ U) (htu : T ⊆ U): |S| + |T| ≤ |U| :=
by
  sorry

/-
Useful examples of Finsets for indexing sums/products etc include:
For `a b n : ℕ`
  `range (n + 1) = {0,1,..,n}`
  `Ico a (b + 1) := {a,a+1,..,b}` (defaults to ∅ if b ≤ a)
-/
#eval range 4 -- {0,1,2,3}
#eval range 0 -- ∅
#eval Ico  3 6 -- {3,4,5}
#eval Ico  6 6 -- ∅


#check sum_range_add_sum_Ico

-- 04 x_0 + x_1 + ... + x_{2n-1} = (x_0 + ... + x_{n-1}) + {x_n + ... x_{2n-1}}
lemma sum_ico_twice (n : ℕ) (x : ℕ → ℝ) : ∑ i in Ico n (2*n), x i  = ∑ i in range (2*n), x i - ∑ i in range n, x i :=
by
  sorry


#check abs_add -- |a + b| ≤ |a| + |b| the triangle inequality

#check abs_sub_comm -- |a - b| = |b - a|

/-
A new tactic we use below is `positivity` this can prove goals
such as `0 < x` or `x ≠ 0`
-/


-- 05
/--
If `∑ xₙ` converges then `x_n + ... x_{2n-1} → 0` as `n → ∞` -/
lemma cauchy_like {x : ℕ → ℝ} (hs : limₙ (fun n => ∑ i in range n, x i) l) :
limₙ (fun n => ∑ i in Ico n (2*n), x i) 0 :=
by
  intro ε hε
  obtain ⟨N,hN⟩ := hs (ε/2) (by positivity)
  use N
  norm_num
  intro n hn
  let A := ∑ i in range n, x i
  let B := ∑ i in range (2*n), x i
-- Work out the proof on paper and add extra lines to this `calc` block as required
-- `sum_ico_twice` could be useful
  calc
    _ = |B - l + (l - A)|:= by sorry
    _ < _ := by sorry


#check card_eq_sum_ones

#check mul_sum

#check sum_le_sum


-- 06
lemma lb_mul_card_le_sum {S : Finset ℕ} {f : ℕ → ℝ} (lb : ∀ i, i ∈ S → c ≤ f i) : c * |S| ≤ ∑ i in S, f i :=
by
  sorry

/-
In the next example `field_simp` may be useful.
-/

#check mem_Ico

#check inv_le_inv_of_le

-- 07
lemma sum_inv_nat_Ico (k : ℕ): (1/2) ≤ ∑ i in Ico (2^k) (2*2^k), (i : ℝ)⁻¹ :=
by
  have lb : ∀ i ∈ Ico (2^k) (2*2^k), (2*2^k : ℝ)⁻¹ ≤ (i : ℝ)⁻¹
  · sorry
  convert lb_mul_card_le_sum lb using 1
  sorry

/-- The harmonic series diverges (use `cauchy_like` and `sum_inv_nat_Ico`)-/
-- 08
theorem harmonic : ¬ ∃ l , limₙ (fun n => ∑ i in range n, i⁻¹) l :=
by
  intro ⟨l,hl⟩
  sorry
