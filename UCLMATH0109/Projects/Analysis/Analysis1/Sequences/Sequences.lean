import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.BigOperators.Basic
namespace UCL
open  Finset

/-
  We define convergence of a sequence in the usual way

  (We call this `sLim` for `sequential limit` to distinguish it from `flim` which will
  be our name for the limit of a function at a point.)

  The main results in this file are

  (I) algebra of limits: eg

  `sLim_add` if xₙ  →  a and yₙ → b then xₙ + yₙ → a + b
  `sLim_mul` if xₙ  →  a and yₙ → b then xₙyₙ → ab

  (II) various versions of the `sandwich` lemma: eg

 `sLim_sandwich` if xₙ → a and zₙ → a and xₙ ≤ yₙ ≤ zₙ for all n then yₙ → a.
 `sLim_tail_sandwich` if xₙ → a and zₙ → a and xₙ ≤ yₙ ≤ zₙ for all n ≥ k then yₙ → a.

 (III) Congruent sequences:

 `sLim_congr` if xₙ = yₙ for all n and xₙ → a then yₙ → a

(IV) Uniqueness : `sLim_unique` if xₙ  → a and xₙ  → b then a = b

 (V) Various results about the `tail` of a sequence:

  `sLim_of_tail_sLim` if xₙ₊ₘ → a for some m, then xₙ → a
  `sLim_congr_tail`  if xₙ → a and xₙ = yₙ for all n ≥ k then yₙ → a

 (VI) Results about convergent sequences such as:
  `sLim_imp_bd` any convergent sequence is bounded
   `sLim_Icc` if xₙ → c and for all n xₙ ∈ [a,b] then c ∈ [a,b]

  -/

/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

open Finset

/--
Any convergent sequence `xₙ → a` is bounded by the maximum of {|x 0|,|x 1|, ... ,|x N|}
and |a| + 1, where N is given by setting ε = 1 in the definition of `xₙ → a`
-/
lemma sLim_imp_bd' (hx : limₙ x a) : ∃ B,∀ n, |x n| ≤ B :=
by
  sorry

/-- Version of limₙ with |xₙ - a| ≤ ε (sometimes useful) -/
def sLim' (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| ≤ ε

notation "limₙ' " => sLim'

/-- The two definitions sLim and sLim' agree-/
lemma sLim_iff_sLim' : limₙ x a ↔ limₙ' x a :=
by
  sorry

/-- The sequence `1/(n+1) → 0` -/
lemma one_over_nat : limₙ (fun n => (n + 1)⁻¹) 0 :=
by
  sorry

/-- A sequence with the same terms as one that converges also converges to the same limit -/
lemma sLim_congr (hx : limₙ x a) (heq1 : ∀ n, y n = x n) (heq2 : b = a) : limₙ y b :=
by
  sorry

/-- If a sequence has a limit it is unique -/
lemma sLim_unique (ha : limₙ x a) (hb : limₙ x b) : a = b :=
by
  sorry

/-- if two sequences both converge and have the same terms then the two limits are equal -/
lemma sLim_unique_congr (ha : limₙ x a) (hb : limₙ y b) (heq1 : ∀ n, y n = x n) : a = b :=
by
  sorry

/-- A constant sequence converges to its constant value-/
lemma sLim_const (a : ℝ) : limₙ (fun _ => a) a :=
by
  sorry

/-- If there is m such that `xₙ₊ₘ → a` then `xₙ → a`  -/
lemma sLim_of_tail_sLim (m : ℕ) (hxt : limₙ (fun n => x (n + m)) a) : limₙ x a :=
by
  sorry

/-- If `xₙ → a` then `xₙ₊ₘ → a` for all m -/
lemma tail_sLim_of_sLim (m : ℕ) (hx : limₙ x a) : limₙ (fun n => x (n + m)) a :=
by
  sorry

/--
A sequence with the same terms from some point on as one that converges to a
limit also converges to the same limit -/
lemma sLim_congr_tail (k : ℕ) (hx : limₙ x a) (heq1 : ∀ n, k ≤ n → y n = x n) (heq2 : b = a) :
    limₙ y b :=
by
  sorry

/--
The sLim_sandwich lemma: if  `xₙ  → a` and `zₙ → a` and for all n ∈ ℕ ,
 `xₙ ≤ yₙ ≤ zₙ`  then `yₙ → a` -/
lemma sLim_sandwich (hx : limₙ x a) (hz : limₙ z a) (hb : ∀ n, x n ≤ y n ∧ y n ≤ z n) :
    limₙ y a :=
by
  sorry

/-- If  `xₙ → a` and `zₙ → a` and for all n ≥ k , `xₙ ≤ yₙ ≤ zₙ`  then `yₙ → a`  -/
lemma sLim_tail_sandwich (k : ℕ) (hx : limₙ x a) (hz : limₙ z a)
    (hb : ∀ n, k ≤ n → x n ≤ y n ∧ y n ≤ z n) : limₙ y a :=
by
  sorry

/-- if `xₙ → a` and `yₙ → b` then `xₙ + yₙ  → a + b`  -/
lemma sLim_add (hx : limₙ x a) (hy : limₙ y b) : limₙ (x + y) (a + b) :=
by
  sorry

/-- if `xₙ → a` then `xₙ * b  → a * b`  -/
lemma sLim_mul_const (hx : limₙ x a) (b : ℝ) : limₙ (fun n => x n * b) (a * b) :=
by
  sorry

/-- if `xₙ → a` then `b * xₙ  → b * a`  -/
lemma sLim_const_mul (hx : limₙ x a) (b : ℝ) : limₙ (fun n => b * x n ) (b * a) :=
by
  sorry

/-- if `xₙ → a` then `-xₙ → -a` -/
lemma sLim_neg (hx : limₙ x a) : limₙ (fun n => -x n) (-a) :=
by
  sorry

/-- `xₙ → a` iff `-xₙ → -a` -/
lemma sLim_neg_iff : limₙ x a ↔ limₙ (fun n => -x n) (-a) :=
by
  sorry

/-- if `xₙ → a` and `yₙ → b` then `xₙ - yₙ  → a - b`  -/
lemma sLim_sub (hx : limₙ x a) (hy : limₙ y b) : limₙ (fun n => x n - y n) (a - b) :=
by
  sorry

/-- If `xₙ → a` and `zₙ → 0` and `∀ n, |x n - y n | ≤ z n` then `yₙ → a`  -/
lemma sLim_sandwich_abs (y : ℕ → ℝ) (hx : limₙ x a) (hz : limₙ z 0)
    (hab : ∀ n, |x n - y n| ≤ z n) : limₙ y a :=
by
  sorry

/-- If `xₙ → a` then `|xₙ| → |a|` -/
lemma sLim_abs (hx : limₙ x a) : limₙ (fun n => |x n|) (|a|) :=
by
  sorry

/-- If |xₙ| → a and 0 ≤ xₙ then xₙ → a   -/
lemma sLim_abs_of_nonneg (hx : limₙ (fun n => |x n|) a) (hn : ∀ n, 0 ≤ x n) : limₙ x a :=
by
  sorry

/-- If xₙ → a and 0 ≤ xₙ then 0 ≤ a -/
lemma sLim_nonneg (hx : limₙ x a) (hn : ∀ n, 0 ≤ x n) : 0 ≤ a :=
by
  sorry

/-- If |xₙ| → 0 then xₙ → 0 -/
lemma sLim_zero_abs (hx : limₙ (fun n => |x n|) 0) : limₙ x 0 :=
by
  sorry

/-- Any convergent sequence is bounded above by some B > 0  -/
lemma sLim_imp_bd (hx : limₙ x a) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
by
  sorry


/-- if `xₙ → a` and `yₙ → 0` then `xₙ * yₙ → 0` -/
lemma sLim_mul_zero (hx : limₙ x a) (hy : limₙ y 0) : limₙ (fun n => x n * y n) 0 :=
by
  sorry

/-- if `xₙ → a` and `yₙ → b` then `xₙ* yₙ → a * b` -/
lemma sLim_mul (hx : limₙ x a) (hy : limₙ y b) : limₙ (x * y) (a * b) :=
by
  sorry

/-- If `xₙ → a` and `k ∈ ℕ` then  `xₙ^k → a^k` -/
lemma sLim_pow (k : ℕ) (hx : limₙ x a) : limₙ (fun n => x n ^ k) (a ^ k) :=
by
  sorry

/-- If xₙ → 1 and k ∈ ℕ then xₙ^k → 1 -/
lemma sLim_pow_one (k : ℕ)  (hx : limₙ x 1) : limₙ (fun n => x n ^ k) 1 :=
by
  sorry

/-- if `xₙ → a` and `0 < a` then `1 / xₙ → 1 / a` -/
lemma sLim_inv_pos (hx : limₙ x a) (hnn : 0 < a) : limₙ (fun n => (x n)⁻¹) a⁻¹ :=
by
  sorry

/-- if `xₙ → a` and `a ≠ 0` then `1 / xₙ → 1 / a` -/
lemma sLim_inv (hx : limₙ x a) (hnn : a ≠ 0) : limₙ (fun n => (x n)⁻¹) a⁻¹ :=
by
  sorry

/-- if `xₙ → a` and `yₙ → b` and `b ≠ 0` then `xₙ / yₙ → a / b ` -/
lemma sLim_div (hx : limₙ x a) (hy : limₙ y b) (hnn : b ≠ 0) :
    limₙ (fun n => x n / y n) (a / b) :=
by
  sorry

/-- If two sequences are equal and non-zero then the sLim of their quotient is 1 -/
lemma sLim_of_eq_ne_zero {x y : ℕ → ℝ} (heq : ∀ n, x n = y n) (hnz : ∀ n, y n ≠ 0) :
    limₙ (fun n => x n / y n) 1 :=
by
  sorry

/-- a/(n+b) → 0 as n → ∞  for any a, b constant -/
lemma sLim_zero (a b : ℝ) : limₙ (fun n => a / (n + b)) 0 :=
by
  sorry


/-- (n+a)/(n+b) → 1 as n → ∞ any a,b constant -/
lemma sLim_one (a b : ℝ) : limₙ (fun n => (n + a) / (n + b)) 1 :=
by
  sorry

/-- (n + a / n + b)ᵏ → 1 for any a b ∈ ℝ and k ∈ ℕ -/
lemma sLim_one_pow (a b : ℝ) (k : ℕ) : limₙ (fun n => ((n + a) / (n + b))^k) 1 :=
by
  sorry

/--
If sₙ ≤ xₙ ≤ tₙ and uₙ ≤  yₙ ≤ vₙ and sₙ/vₙ → l and tₙ/uₙ → l and 0 ≤ sₙ and 0 < uₙ then xₙ/yₙ → l -/
lemma sLim_sandwich_div {x y s t u v : ℕ → ℝ}  (hx : ∀ n, s n ≤ x n ∧ x n ≤ t n) (hy : ∀ n, u n ≤ y n ∧ y n ≤ v n)
    (hl1 : limₙ (fun n => s n / v n) l) (hl2 : limₙ (fun n => t n / u n) l)
    (hp : ∀ n, 0 ≤ s n ∧ 0 < u n) : limₙ (fun n => x n / y n) l :=
by
  sorry


open Nat
/- The next result will be useful for differentiating power-series-/
#check ascFactorial
/-- (n+1)(n+2)...(n+k+1)/(n(n+1)...(n+k)) → 1 -/
lemma sLim_div_asc_fact (k : ℕ) :
    limₙ (fun n => (n + 1).ascFactorial k / n.ascFactorial k) 1 :=
by
  sorry

/-- If xₙ → a and, for all n, xₙ ≤ b then a ≤ b-/
lemma sLim_le (hx : limₙ x a) (hle : ∀ n, x n ≤ b) : a ≤ b :=
by
  sorry

/-- If xₙ → a and, for all n, b ≤ xₙ then b ≤ a-/
lemma sLim_ge (hx : limₙ x a) (hle : ∀ n, b ≤ x n) : b ≤ a :=
by
  sorry

open Set

/-- If xₙ → c and for all n, xₙ ∈ [a,b] then c ∈ [a,b] -/
lemma sLim_Icc (hx : limₙ x c) (hicc : ∀ n, x n ∈ Set.Icc a b) : c ∈ Icc a b :=
by
  sorry

/-- If xₙ → a and xₙ is monotone increasing then xₙ ≤ a for all n  -/
lemma le_sLim_mono (hx : limₙ x a) (hm : Monotone x) {n : ℕ} : x n ≤ a :=
by
  sorry

/-- If xₙ → a and xₙ is monotone decreasing then a ≤ xₙ for all n  -/
lemma sLim_le_anti (hx : limₙ x a) (hm : Antitone x) {n : ℕ} : a ≤ x n :=
by
  sorry






open scoped NNReal

lemma bernouilli1 (n : ℕ) (a : ℝ≥0): 1 + n*a ≤ (1 + a)^n:=
by
  induction n with
  | zero => norm_num;
  | succ n ih =>
    rw [pow_succ (1+a),Nat.succ_eq_add_one]
    push_cast
    rw [add_mul,add_mul,one_mul ((1+a)^n),← add_assoc]
    apply _root_.add_le_add ih
    rw [mul_comm]
    apply mul_le_mul le_rfl (le_of_add_le_left ih) zero_le_one zero_le'

lemma bernouilli2 (n : ℕ) (a : ℝ≥0): (n.choose 2)*a^2 ≤ (1 + a)^n :=
by
  induction n with
  | zero => norm_num;
  | succ n ih =>
    cases n with
    | zero => norm_num;
    | succ n =>
      rw [pow_succ (1+a)]
      rw [Nat.succ_eq_add_one] at *
      rw [Nat.choose,add_mul,Nat.choose_one_right]
      push_cast at *
      simp_rw [add_mul _ _ (a^2)] at *
      rw [add_comm,one_mul]
      apply _root_.add_le_add
      · rw [one_mul]; exact ih
      · rw [pow_two,← mul_assoc,←add_mul,mul_comm]
        apply mul_le_mul le_rfl _ zero_le' zero_le'
        apply le_trans _ (bernouilli1 (n+1) a)
        push_cast
        rw [add_mul,one_mul]
        exact le_add_self

lemma choose_div_succ (i : ℕ) : limₙ (fun n => (n.choose i)/(n.choose (i+1))) 0 :=
by
  apply sLim_congr_tail (i+1) (sLim_zero (i+1) (-i)) _ rfl
  intro n hn;
  rw [div_eq_iff,mul_comm,←mul_div_assoc,eq_div_iff]
  have :=(choose_succ_right_eq n i).symm
  · rw [← sub_eq_add_neg,← Nat.cast_sub ((Nat.le_succ i).trans hn)]
    norm_cast
  · intro hf; rw [add_neg_eq_zero] at hf
    norm_cast at hf
    exact lt_irrefl i (hf ▸ hn)
  · norm_cast;
    exact Nat.pos_iff_ne_zero.1 (choose_pos hn)


lemma choose_div_add (i j : ℕ)  : limₙ (fun n => (n.choose i)/(n.choose (i + j + 1))) 0 :=
by
  induction j with
  | zero =>  exact choose_div_succ _;
  | succ j ih =>
    apply sLim_congr_tail (i+j +1) (sLim_mul  ih (choose_div_succ (i+j+1))) _ (by norm_num)
    intro n hn;
    simp only [Pi.mul_apply];
    rw [ div_mul_div_cancel]
    · rfl;
    · norm_cast;
      intro hf; apply pos_iff_ne_zero.1 (choose_pos hn) hf



lemma sLim_succ_root_zero (x : ℕ → ℝ) (k : ℕ) (h : limₙ (x^(k+1)) 0) : limₙ x 0 :=
by
  intro ε hε
  obtain ⟨N,hN⟩:=h (ε^(k+1)) (by positivity)
  simp only [Pi.pow_apply, sub_zero, abs_pow] at *
  use N
  intro n hn
  apply lt_of_pow_lt_pow (k+1) hε.le (hN n hn)



lemma sLim_sandwich_zero_div {x y z : ℕ → ℝ} {k : ℕ} (h0 : ∀n, 0 ≤ y n) (h02: ∀n, k ≤ n → 0 < x n) (h1 : ∀n, (x n)*(y n)≤ z n) (hl: limₙ (z/x) 0) : limₙ y 0 :=
 sLim_tail_sandwich k (sLim_const 0) hl (fun n hn => ⟨h0 n,(le_div_iff' (h02 n hn)).2 (h1 n)⟩)
/--
Defining the `nth`-root on ℝ≥0 is tricky, so instead we prove that any sequence
`1 + xₙ` such that `0 ≤ xₙ` and `(1 + xₙ)ⁿ ≤ n` tends to 0
-/
lemma nth_root_n (x : ℕ → ℝ) (h1: ∀n, 0 ≤ x n) (hnp : ∀ n ,(1 + x n) ^ n ≤ n) : limₙ x 0 :=
by
  apply sLim_succ_root_zero _ 1;
  rw [one_add_one_eq_two]
  have h0 : ∀ n, 0 ≤ (x n)^2 := fun n => sq_nonneg _
  have h02 : ∀ n, 2 ≤ n →  (0:ℝ) < Nat.choose n 2
  · exact_mod_cast (fun n hn => Nat.choose_pos hn)
  have h1 : ∀ n, (n.choose 2)*(x n)^2 ≤ n.choose 1
  · intro n;
    rw [Nat.choose_one_right]
    apply le_trans _ (hnp n)
    exact_mod_cast (bernouilli2 n ⟨(x n),h1 n⟩)
  apply sLim_sandwich_zero_div h0 h02 h1 (choose_div_succ 1)

/-
We have deliberately developed the basic theory of convergence of real sequences avoiding Mathlib's
definitions of filters and topology, however if we need to use a result from Mathlib then the following conversion
may be useful
-/
open Filter Topology

/-- limₙ xₙ = a ↔ Tendsto x atTop (𝓝 a) -/
lemma sLim_iff_tendsto : limₙ x a ↔ Tendsto x atTop (𝓝 a):=
by
  simp only [Metric.tendsto_atTop, Real.dist_eq]
  rfl
