import Mathlib.Tactic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace UCL
open  Finset

/-
We start with some results from 1st Year analysis on limits of sequences.

We do this in ℝ but most of it would carry over almost unchanged to a metric space

  A `real sequence` is simply a function from `ℕ → ℝ`, mapping n ↦ xₙ

  Recall that to define a function in Lean we can use `λ`-notation.

  For example we can write `f : ℕ → ℝ := λ n, 2*n` to define a function
   `f` from `ℕ` to `ℝ` mapping `n ↦ 2*n`

  We define convergence of a sequence in the usual way

  (We call this `sLim` for `sequential limit` to distinguish it from `flim` which will
  be our name for the limit of a function at a point.)

  The main results in this file are

  (I) algebra of limits: eg

  `sLim_add` if xₙ  →  a and yₙ → b then xₙ + yₙ → a + b
  `sLim_mul` if xₙ  →  a and yₙ → b then xₙyₙ → ab

  (II) various versions of the `sandwich` theorem: eg

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

/-- The sequence `1/(n+1) → 0` -/
theorem one_over_nat : limₙ (fun n => (n + 1)⁻¹) 0 :=
  by
  intro ε hε
  --  We need to use the Archimedean property of ℝ, ie for any r ∈ ℝ there
  --  exists N ∈ ℕ such that r < N
  obtain ⟨N, hN⟩ := exists_nat_gt ε⁻¹
  use N; intro n hn; rw [sub_zero]
  -- Very useful to know that 0 < 1/(n+1).
  have hsp : 0 < (n + 1 : ℝ)⁻¹ := Nat.inv_pos_of_nat
  rw [abs_of_pos hsp]
  apply inv_lt_of_inv_lt hε; apply hN.trans
  exact_mod_cast lt_of_le_of_lt hn <| Nat.lt_succ_self _

-- Something obvious but useful --
/-- A sequence with the same terms as one that converges also converges to the same limit -/
theorem sLim_congr (hx : limₙ x a) (heq1 : ∀ n, y n = x n) (heq2 : b = a) : limₙ y b :=
by
  convert hx;
  ext; apply heq1

/-- If a sequence has a limit it is unique -/
theorem sLim_unique (ha : limₙ x a) (hb : limₙ x b) : a = b :=
by
  --- If a ≠ b then we can set ε = |a-b| > 0 and obtain a contradiction
  cases (abs_nonneg (a - b)).lt_or_eq with
  | inl hp =>
    exfalso
    obtain ⟨Na, hA⟩ := ha (|a - b| / 2) <| half_pos hp
    obtain ⟨Nb, hB⟩ := hb (|a - b| / 2) <| half_pos hp
    let N := max Na Nb
    specialize hA N (le_max_left _ _)
    specialize hB N (le_max_right _ _)
    apply lt_irrefl (|a - b|)
    calc
       |a - b| = |a - x N + (x N - b)|     := by ring
        _      ≤ |a - x N| + |x N - b|     := by exact abs_add _ _
        _      = |x N - a| + |x N - b|     := by rw [abs_sub_comm a]
        _      < (|a - b|/2) + (|a - b|/2) := by rel [hA, hB]
        _      = |a - b|                   := by linarith
  | inr hz =>
    exact eq_of_abs_sub_eq_zero hz.symm

/-- if two sequence both converge and have the same terms then the two limits are equal -/
theorem sLim_unique_congr (ha : limₙ x a) (hb : limₙ y b) (heq1 : ∀ n, y n = x n) : a = b :=
  sLim_unique ha (sLim_congr hb (fun n => (heq1 n).symm) rfl)

/-- A constant sequence converges to its constant value-/
theorem sLim_const (a : ℝ) : limₙ (fun _ => a) a :=
by
  intro ε hε; use 0; intro n _
  rwa [sub_self, abs_zero]

/-- If there is m such that `xₙ₊ₘ → a` then `xₙ → a`  -/
theorem sLim_of_tail_sLim (m : ℕ) (hxt : limₙ (fun n => x (n + m)) a) : limₙ x a :=
by
  intro ε hε
  obtain ⟨N, hN⟩ := hxt ε hε
  refine ⟨N + m, fun n hn => ?_⟩
  specialize hN (n - m) (le_tsub_of_add_le_right hn); dsimp at hN
  rwa [tsub_add_cancel_of_le] at hN ; apply le_of_add_le_right hn

/-- If `xₙ → a` then `xₙ₊ₘ → a` for all m -/
theorem tail_sLim_of_sLim (m : ℕ) (hx : limₙ x a) : limₙ (fun n => x (n + m)) a :=
by
  intro ε hε; obtain ⟨N, hN⟩ := hx ε hε
  use N; intro n hn
  apply hN (n + m) <| hn.trans <| Nat.le_add_right _ _

/--
A sequence with the same terms from some point on as one that converges to a limit also converges to the same limit -/
theorem sLim_congr_tail (k : ℕ) (hx : limₙ x a) (heq1 : ∀ n, k ≤ n → y n = x n) (heq2 : b = a) :
    limₙ y b := by
  apply sLim_of_tail_sLim k
  apply sLim_congr (tail_sLim_of_sLim k hx) _ heq2
  intro n; apply heq1 (n + k) (Nat.le_add_left _ _)

/--
The sLim_sandwich theorem: if  `xₙ  → a` and `zₙ → a` and for all n ∈ ℕ , `xₙ ≤ yₙ ≤ zₙ`  then `yₙ → a`  -/
theorem sLim_sandwich (hx : limₙ x a) (hz : limₙ z a) (hb : ∀ n, x n ≤ y n ∧ y n ≤ z n) :
    limₙ y a :=
by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx ε hε
  obtain ⟨Nz, hNz⟩ := hz ε hε
  use max Nx Nz
  intro n hn
  specialize hNx n ((le_max_left Nx Nz).trans hn)
  specialize hNz n ((le_max_right Nx Nz).trans hn)
  rw [abs_lt] at *
  constructor
  · apply lt_of_lt_of_le hNx.1 <| sub_le_sub_right (hb n).1 _
  · apply lt_of_le_of_lt (sub_le_sub_right (hb n).2 _) hNz.2

/-- If  `xₙ → a` and `zₙ → a` and for all n ≥ k , `xₙ ≤ yₙ ≤ zₙ`  then `yₙ → a`  -/
theorem sLim_tail_sandwich (k : ℕ) (hx : limₙ x a) (hz : limₙ z a)
    (hb : ∀ n, k ≤ n → x n ≤ y n ∧ y n ≤ z n) : limₙ y a :=
by
  apply sLim_of_tail_sLim k
  apply sLim_sandwich (tail_sLim_of_sLim k hx) (tail_sLim_of_sLim k hz)
  intro n; exact ⟨(hb (n + k) (Nat.le_add_left _ _)).1, (hb (n + k) (Nat.le_add_left _ _)).2⟩

/-- if `xₙ → a` and `yₙ → b` then `xₙ + yₙ  → a + b`  -/
theorem sLim_add (hx : limₙ x a) (hy : limₙ y b) : limₙ (fun n => x n + y n) (a + b) :=
by
  intro ε hε; dsimp
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) (half_pos hε)
  use max Nx Ny; intro n hn
  specialize hNx n ((le_max_left Nx Ny).trans hn)
  specialize hNy n ((le_max_right Nx Ny).trans hn)
  calc
    |x n + y n - (a + b)| = |x n - a + (y n - b)| :=by rw [add_sub_add_comm]
        _                 ≤ |x n - a| + |y n - b| := abs_add _ _
        _                 < ε/2 + ε/2 := add_lt_add hNx hNy
        _                 = ε :=add_halves _

/-- if `xₙ → a` then `xₙ*b  → a*b`  -/
theorem sLim_mul_const (hx : limₙ x a) (b : ℝ) : limₙ (fun n => x n * b) (a * b) :=
by
  intro ε hε; dsimp
  by_cases hb : 0 ≤ b
  · by_cases hbp : 0 = b
    · use 0
      intro n _; rw [← hbp, mul_zero, mul_zero, sub_zero, abs_zero]
      exact hε
    · have hbpos := lt_of_le_of_ne hb hbp
      obtain ⟨N, hN⟩ := hx (ε / b) (div_pos hε hbpos)
      use N; intro n hn
      rw [← sub_mul, abs_mul, abs_of_pos hbpos]
      rw [← lt_div_iff hbpos]; exact hN n hn
  · have hbneg := lt_of_not_le hb
    have absb := abs_of_neg hbneg
    rw [← neg_pos] at hbneg
    obtain ⟨N, hN⟩ := hx (ε / -b) (div_pos hε hbneg)
    use N; intro n hn
    rw [← sub_mul, abs_mul, ← lt_div_iff _]
    simp only [← absb] at hN
    exact hN n hn; rwa [← absb] at hbneg

/-- if `xₙ → a` then `-xₙ → -a` -/
theorem sLim_neg (hx : limₙ x a) : limₙ (fun n => -x n) (-a) :=
by
  apply sLim_congr (sLim_mul_const hx (-1))
  intro n; dsimp; rw [mul_comm, neg_mul, one_mul]
  rw [mul_comm, neg_mul, one_mul]

/-- `xₙ → a` iff `-xₙ → -a` -/
theorem sLim_neg_iff : limₙ x a ↔ limₙ (fun n => -x n) (-a) :=
  ⟨fun h => sLim_neg h, fun h =>
    sLim_congr (sLim_neg h) (fun n => by rw [neg_neg]) (by rw [neg_neg])⟩

/-- if `xₙ → a` and `yₙ → b` then `xₙ - yₙ  → a - b`  -/
theorem sLim_sub (hx : limₙ x a) (hy : limₙ y b) : limₙ (fun n => x n - y n) (a - b) :=
by
  apply sLim_congr (sLim_add hx (sLim_neg hy))
  intro n; rfl; rfl

-- A variant of the sLim_sandwich theorem using absolute value and a null sequence
/-- If `xₙ → a` and `zₙ → 0` and `∀ n, |x n - y n | ≤ z n` then `yₙ → a`  -/
theorem sLim_sandwich_abs (y : ℕ → ℝ) (hx : limₙ x a) (hz : limₙ z 0)
    (hab : ∀ n, |x n - y n| ≤ z n) : limₙ y a :=
by
  have h1 := sLim_sub hx hz
  have h2 := sLim_add hx hz
  simp only [add_zero, sub_zero] at *
  apply sLim_sandwich h1 h2
  intro n
  specialize hab n;
  rw [abs_sub_le_iff] at hab
  exact ⟨sub_le_comm.2 hab.1, sub_le_iff_le_add'.1 hab.2⟩

/-- If `xₙ → a` then `|xₙ| → |a|` -/
theorem sLim_abs (hx : limₙ x a) : limₙ (fun n => |x n|) (|a|) :=
by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  use N; intro n hn
  apply lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) (hN n hn)

/-- If |xₙ| → a and 0 ≤ xₙ then xₙ → a   -/
theorem sLim_abs_of_nonneg (hx : limₙ (fun n => |x n|) a) (hn : ∀ n, 0 ≤ x n) : limₙ x a :=
  sLim_congr hx (fun n => (abs_of_nonneg (hn n)).symm) rfl

/-- If xₙ → a and 0 ≤ xₙ then 0 ≤ a -/
theorem sLim_nonneg (hx : limₙ x a) (hn : ∀ n, 0 ≤ x n) : 0 ≤ a :=
by
  rw [sLim_unique_congr hx (sLim_abs_of_nonneg (sLim_abs hx) hn) fun n => rfl]
  exact abs_nonneg _

/-- If |xₙ| → 0 then xₙ → 0 -/
theorem sLim_zero_abs (hx : limₙ (fun n => |x n|) 0) : limₙ x 0 :=
by
  intro ε he
  obtain ⟨N, hN⟩ := hx ε he
  use N; simp only [sub_zero, abs_abs] at *; exact hN

-- Any convergent sequence `xₙ → a` is bounded by the maximum of its first
-- N₁ terms and (a + 1) where N₁ is given by setting ε = 1 in the
-- definition of `xₙ  → a`
-- [It is convenient to take 0 < B in this bound so that we can divide by it in applications]
/-- Any convergent sequence is bounded  -/
theorem sLim_imp_bd (hx : limₙ x a) : ∃ B, 0 < B ∧ ∀ n, |x n| ≤ B :=
by
  obtain ⟨N, hN⟩ := (sLim_abs hx) 1 zero_lt_one
  let I : Finset ℕ := range N.succ
  have hne : I.Nonempty := ⟨0, mem_range_succ_iff.2 zero_le'⟩
  let J := I.image fun n => |x n|
  let B1 := J.max' (hne.image _)
  use max B1 (|a| + 1)
  constructor
  · apply lt_max_iff.2 (Or.inr _)
    apply lt_of_lt_of_le; exact zero_lt_one; apply le_add_of_nonneg_left; exact abs_nonneg _
  · intro n
    by_cases hn : n ≤ N
    · apply le_max_iff.2 (Or.inl _)
      apply le_max'; rw [mem_image]; use n; rw [mem_range_succ_iff]
      exact ⟨hn, rfl⟩
    · apply le_max_iff.2 (Or.inr _)
      have := hN n (lt_of_not_le hn).le; dsimp at this
      rw [abs_lt] at this
      apply le_add_of_sub_left_le this.2.le

/-- if `xₙ  → a` and `yₙ → 0` then `xₙyₙ → 0` -/
theorem sLim_mul_zero (hx : limₙ x a) (hy : limₙ y 0) : limₙ (fun n => x n * y n) 0 :=
by
  intro ε hε
  obtain ⟨B, hBp, hB⟩ := sLim_imp_bd hx
  obtain ⟨N, hN⟩ := hy (ε / B) (div_pos hε hBp)
  use N; intro n hn; dsimp; simp only [sub_zero] at *
  rw [abs_mul]
  specialize hN n hn
  specialize hB n
  convert mul_lt_mul' hB hN (abs_nonneg _) hBp
  symm
  apply mul_div_cancel' ε hBp.ne.symm

/-- if `xₙ → a` and `yₙ → b` then `xₙyₙ → ab` -/
theorem sLim_mul (hx : limₙ x a) (hy : limₙ y b) : limₙ (fun n => x n * y n) (a * b) :=
by
  have hyb := sLim_sub hy (sLim_const b)
  rw [sub_self] at hyb
  apply sLim_congr (sLim_add (sLim_mul_zero hx hyb) (sLim_mul_const hx b))
  intro n
  rw [mul_sub, sub_add_cancel]
  rw [zero_add]

--- WARNING!
-- If you import all of Mathlib then it interprets this as (xₙ^↑k) rather than `npow`
/-- If  `xₙ → a` and `k ∈ ℕ` then  `xₙ^k → a^k` and-/
theorem sLim_pow (k : ℕ) (hx : limₙ x a) : limₙ (fun n => x n ^ k) (a ^ k) :=
by
  induction k with
  | zero =>
    simp only [pow_zero];
    exact sLim_const 1
  | succ k hk =>
    apply sLim_congr (sLim_mul hk hx)
    · intro n ; rw [pow_succ']
    · rw [pow_succ']

theorem sLim_pow_one (k : ℕ)  (hx : limₙ x 1) : limₙ (fun n => x n ^ k) (1) :=
by
  convert sLim_pow k hx
  rw [one_pow]

/-- if `xₙ → a` and `0 < a` then `1/xₙ → 1/a` -/
theorem sLim_inv_pos (hx : limₙ x a) (hnn : 0 < a) : limₙ (fun n => (x n)⁻¹) a⁻¹ :=
by
  obtain ⟨N1, hN1⟩ := hx (a / 2) (half_pos hnn)
  intro ε hε
  obtain ⟨N2, hN2⟩ :=
    hx (a ^ 2 * ε / 2) (div_pos (mul_pos (sq_pos_of_pos hnn) hε) (zero_lt_two))
  use max N1 N2
  intro n hn
  specialize hN1 n ((le_max_left _ _).trans hn)
  specialize hN2 n ((le_max_right _ _).trans hn)
  obtain ⟨hN1,_⟩:= abs_lt.1 hN1
  nth_rw 2 [← add_halves a] at hN1
  rw [neg_lt_sub_iff_lt_add] at hN1
  replace hN1 := lt_of_add_lt_add_left hN1
  have xnp : 0 < x n := (half_pos hnn).trans hN1
  rw [inv_sub_inv (ne_of_gt xnp) (ne_of_gt hnn)]
  rw [abs_div, abs_sub_comm, abs_mul, abs_of_pos hnn, abs_of_pos xnp, div_lt_iff (mul_pos xnp hnn)]
  apply hN2.trans; rw [mul_comm (x n)]
  rw [← mul_assoc, pow_two, mul_assoc, mul_comm a ε, ← mul_assoc, mul_comm a ε, mul_div_assoc]
  apply mul_lt_mul' (le_refl _) hN1 (half_pos hnn).le (mul_pos hε hnn)

/-- if `xₙ → a` and `a ≠ 0` then `1/xₙ → 1/a` -/
theorem sLim_inv (hx : limₙ x a) (hnn : a ≠ 0) : limₙ (fun n => (x n)⁻¹) a⁻¹ :=
by
  cases lt_or_gt_of_ne hnn with
  | inl h =>
    rw [← neg_pos] at h
    rw [sLim_neg_iff] at *
    apply sLim_congr (sLim_inv_pos hx h)
    intro n; dsimp; rw [inv_neg]; rw [inv_neg]
  | inr h =>
    exact sLim_inv_pos hx h

/-- if `xₙ → a` and `yₙ → b` and `b ≠ 0` then `xₙ/yₙ → a / b ` -/
theorem sLim_div (hx : limₙ x a) (hy : limₙ y b) (hnn : b ≠ 0) :
    limₙ (fun n => x n / y n) (a / b) :=
by
  apply sLim_congr (sLim_mul hx (sLim_inv hy hnn))
  · intro n; dsimp; rw [div_eq_mul_inv];
  · rw [div_eq_mul_inv]

/-- If two sequences are equal and non-zero then the sLim of their quotient is 1 -/
theorem sLim_of_eq_ne_zero {x y : ℕ → ℝ} (heq : ∀ n, x n = y n) (hnz : ∀ n, y n ≠ 0) :
    limₙ (fun n => x n / y n) 1 :=
by
  apply sLim_congr (sLim_const 1)
  · intro n
    rw [heq n]; apply div_self (hnz n)
  · rfl

/-- a/(n+b) → 0 as n → ∞  for any a, b -/
theorem sLim_zero (a b : ℝ) : limₙ (fun n => a / (n + b)) 0 :=
by
  have hb : limₙ (fun n => 1 / (n + b)) 0
  · by_cases hb1 : b = 1
    · rw [hb1]; apply sLim_congr one_over_nat (fun n => by rw [inv_eq_one_div]) rfl
    · obtain ⟨k, _⟩ := exists_nat_gt (|b|)
      apply
        sLim_congr_tail k
        (sLim_div one_over_nat (sLim_add (sLim_const 1) (sLim_mul_const one_over_nat (b - 1))) _)
      · intro n _; dsimp; rw [inv_eq_one_div, div_div, mul_add, mul_one]
        rw [div_mul, mul_div_assoc', mul_one, div_div_cancel', add_add_sub_cancel]
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_ne_zero]; exact Nat.succ_ne_zero _
      · rw [zero_mul, add_zero, div_one]
      · rw [zero_mul, add_zero]
        exact one_ne_zero
  exact sLim_congr (sLim_mul (sLim_const a) hb) (fun n => by rw [mul_div, mul_one])
          (by rw [mul_zero])


/-- (n+a)/(n+b) → 1 as n → ∞ any a,b -/
theorem sLim_one (a b : ℝ) : limₙ (fun n => (n + a) / (n + b)) 1 :=
by
  rw [← zero_add a, ← sub_self b, sub_add]; simp only [← add_sub_assoc, sub_div]
  obtain ⟨k, hk⟩ := exists_nat_gt (|b|)
  apply sLim_congr_tail k (sLim_sub (sLim_const 1) (sLim_sub (sLim_zero b b) (sLim_zero a b)))
  · intro n hn; dsimp; congr; rw [div_self]
    intro hf;
    rw [← @Nat.cast_le ℝ, ← neg_le_neg_iff] at hn
    apply lt_irrefl (-n : ℝ); convert lt_of_le_of_lt hn (abs_lt.1 hk).1
    exact add_eq_zero_iff_neg_eq.1 hf;
  · rw [sub_zero, sub_zero]

/--
If sₙ ≤ xₙ ≤ tₙ and uₙ ≤  yₙ ≤ vₙ and sₙ/vₙ → l and tₙ/uₙ → l and 0 ≤ sₙ and 0 < uₙ then xₙ/yₙ → l -/
theorem sLim_sandwich_div {x y s t u v : ℕ → ℝ}  (hx : ∀ n, s n ≤ x n ∧ x n ≤ t n) (hy : ∀ n, u n ≤ y n ∧ y n ≤ v n)
    (hl1 : limₙ (fun n => s n / v n) l) (hl2 : limₙ (fun n => t n / u n) l)
    (hp : ∀ n, 0 ≤ s n ∧ 0 < u n) : limₙ (fun n => x n / y n) l :=
by
  apply sLim_sandwich hl1 hl2
  intro n
  exact
    ⟨div_le_div ((hp n).1.trans (hx n).1) (hx n).1 (lt_of_lt_of_le (hp n).2 (hy n).1) (hy n).2,
      div_le_div (((hp n).1.trans (hx n).1).trans (hx n).2) (hx n).2 (hp n).2 (hy n).1⟩



open Nat
-- The next result will be useful for differentiating power-series
/-- (n+1)(n+2)...(n+k+1)/(n(n+1)...(n+k)) → 1 -/
theorem sLim_div_asc_fact (k : ℕ) :
    limₙ (fun n => (n + 1).ascFactorial k / n.ascFactorial k) 1 :=
by
  have hx :
    ∀ n : ℕ, (n + 1 + 1) ^ k ≤ (n + 1).ascFactorial k ∧ (n + 1).ascFactorial k ≤ (n + 1 + k) ^ k
  · intro n; exact ⟨pow_succ_le_ascFactorial (n + 1) k, ascFactorial_le_pow_add (n + 1) k⟩
  have hy : ∀ n : ℕ, (n + 1) ^ k ≤ n.ascFactorial k ∧ n.ascFactorial k ≤ (n + k) ^ k
  · intro n;
    exact ⟨pow_succ_le_ascFactorial n k, ascFactorial_le_pow_add n k⟩
  simp only [← @cast_le ℝ] at hx hy
  apply sLim_sandwich_div hx hy
  · simp only [cast_pow, ← div_pow]
    apply sLim_pow_one k
    simp only [cast_add, add_assoc]
    apply sLim_one _ _
  · simp only [cast_pow, ← div_pow]
    apply sLim_pow_one k
    simp only [cast_add, add_assoc]
    apply sLim_one _ _
  · intro n
    simp only [cast_nonneg, cast_pos, pow_pos (succ_pos _)]

/-- If xₙ → a and, for all n, xₙ ≤ b then a ≤ b-/
theorem sLim_le (hx : limₙ x a) (hle : ∀ n, x n ≤ b) : a ≤ b :=
by
  by_contra hn
  replace hn := lt_of_not_le hn
  obtain ⟨N, hN⟩ := hx (a - b) (sub_pos_of_lt hn)
  simp only [abs_lt] at hN
  apply lt_irrefl b;
  obtain ⟨h1,h2⟩:= hN N (le_refl _)
  nth_rw 1 [← add_sub_cancel' a b]
  rw [lt_sub_iff_add_lt', neg_sub, add_sub] at h1
  apply lt_of_lt_of_le h1 (hle N)

/-- If xₙ → a and, for all n, b ≤ xₙ then b ≤ a-/
theorem sLim_ge (hx : limₙ x a) (hle : ∀ n, b ≤ x n) : b ≤ a :=
by
  replace hx := sLim_neg hx
  rw [← neg_le_neg_iff]; apply sLim_le hx fun n => neg_le_neg (hle n)

open Set

/-- If xₙ → c and for all n xₙ ∈ [a,b] then c ∈ [a,b] -/
theorem sLim_Icc (hx : limₙ x c) (hicc : ∀ n, x n ∈ Icc a b) : c ∈ Icc a b :=
by
  simp only [Set.mem_Icc] at *
  exact
    ⟨sLim_ge hx fun n => (Set.mem_Icc.1 (hicc n)).1, sLim_le hx fun n => (Set.mem_Icc.1 (hicc n)).2⟩

/-- If xₙ → a and xₙ is monotone then xₙ ≤ a for all n  -/
theorem le_sLim_mono (hx : limₙ x a) (hm : Monotone x) {n : ℕ} : x n ≤ a :=
by
  by_contra hf
  replace hf := lt_of_not_le hf
  let ε := x n - a
  have hε := sub_pos_of_lt hf
  obtain ⟨N, hN⟩ := hx ε hε
  specialize hN (max n N) (le_max_right n N)
  specialize hm (le_max_left n N)
  rw [abs_sub_lt_iff] at hN
  apply lt_irrefl (x n)
  apply lt_of_le_of_lt hm
  rw [sub_lt_iff_lt_add, sub_add_cancel] at hN
  exact hN.1
