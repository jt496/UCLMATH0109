import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
/-

  # Assessed Sheet 3
   Covering material from sheet3A,B,C,D
 `norm_num` `linarith` `ring` `apply?` `exact?`
  `refine` `convert` `congr` `have` `calc`
-/

/-
In the same way that `succ n` is Lean for `n + 1` so `pred n` is Lean for `n - 1`

Subtraction on ℕ is defined in terms of `pred`

def Nat.pred : ℕ → ℕ
  | 0      => 0         --          0 - 1 = 0
  | succ a => a         --    (a + 1) - 1 = a


def Nat.sub : ℕ → ℕ → ℕ
  | a, 0      => a              --            a - 0 = a
  | a, succ b => pred (a - b)   --      a - (b + 1) = (a - b) - 1

Warning: subtraction in ℕ is nasty, eg `4 - 6 = 0` etc..

In particular `ℕ` is not a ring so the `ring` tactic will struggle with
subtraction in ℕ (but is great at proving identities in ℤ, ℝ, ℚ etc).

One strategy that can work in `ℕ` is to first rewrite the identity you are trying to prove
so that subtraction does not appear. Once you've done this `ring` should finish it off.

-/

-- 01
example (a b : ℕ) : a + b - b = a :=
by
  exact Nat.add_sub_cancel a b -- found using apply?

-- 02
example : ∃ (a b : ℕ), a - b  + b ≠ a:=
by
  use 0,1
  decide

-- 03
example (a b : ℕ) (h : b ≤ a) : a - b + b = a :=
by
  exact Nat.sub_add_cancel h -- found using apply?

-- 04
example (a b : ℕ) : a + b - a = b :=
by
  exact Nat.add_sub_self_left a b -- found using apply?

-- 05 The previous example could be useful here
example (m n : ℕ) (h : m ≤ n) : n^2 - m^2 = (n-m)*(n+m):=
by
  have hk : ∃ k, n = m + k
  · exact Nat.exists_eq_add_of_le h -- found using apply?
  obtain ⟨k,hk⟩:=hk
  have : (m+k)^2 = m^2 + (2*m*k + k^2)
  · ring
  rw [hk,this, Nat.add_sub_self_left (m^2), Nat.add_sub_self_left]
  ring



/-
In the exercises below you can always introduce new `have` statements
to give new goals that help.
-/

-- 06
example (m : ℕ) (h : 0 < m) : (2 * m)^2 + (m^2 - 1)^2 = (m^2 + 1)^2:=
by
  have hs : ∃ n, m = n + 1
  · exact Nat.exists_eq_add_of_le' h -- found via apply?
  obtain ⟨n,hn⟩ := hs
  rw [hn]
  have hsub : (n + 1)^2 - 1 = n^2 + 2*n -- new `have` introduced
  · have : (n+1)^2 = n^2 + 2*n + 1 -- new `have` introduced
    · ring
    rw [this]
    rfl
  rw [hsub]
  ring


-- 07 this is very easy (notice we are in `ℤ` not `ℕ`)
example (m n : ℤ) : (n^2 - m^2)^2 + (2*m*n)^2 = (n^2 + m^2)^2 :=
by
  ring

namespace Sheet3sol
/-- xₙ → a if for any ε > 0 there is N ∈ ℕ such that for all n ≥ N we have |xₙ - a| < ε  -/
def sLim (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → |x n - a| < ε

notation "limₙ " => sLim

/-
In the next few examples we are working in `ℝ` so `norm_num`, `ring`,
and `linarith` (as well as `have / apply?`) may be useful.

You can also use `dsimp` or `dsimp at h` to simplify the goal or hypothesis
when needed.
-/


-- 08 the constant sequence `xₙ = b` tends to `b`
lemma sLim_const (b : ℝ) : limₙ (fun _ => b) b :=
by
  intro ε he
  use 0
  norm_num
  exact he

-- 09
/-- if `xₙ → a` and `0 ≤ b` then `xₙ*b  → a*b`  -/
theorem sLim_mul_const_nonneg (hx : limₙ x a) (b : ℝ) (hb : 0 ≤ b) : limₙ (fun n => x n * b) (a * b) :=
by
  by_cases hbp : b = 0
  · rw [hbp]
    convert sLim_const 0
    · norm_num
    · norm_num
  · have hbpos : 0 < b
    · exact Ne.lt_of_le' hbp hb -- found via apply?
    intro ε hε
    -- We will want to use the definition of `xₙ → a` with `ε` replaced by `ε/b`
    have hebp: 0 < ε / b
    · exact div_pos hε hbpos -- found via apply?
    obtain ⟨N, hN⟩ := hx (ε / b) hebp
    use N; intro n hn
    calc
      _ = |(x n - a)*b|   := by ring_nf
      _ = |x n - a| * |b| := abs_mul _ _ -- found by exact?
      _ = |x n - a| * b   := by congr!; exact abs_eq_self.mpr hb -- found by exact?
      _ < (ε/b) * b       := (mul_lt_mul_iff_of_pos_right hbpos).mpr (hN n hn) -- found by exact?
      _ = ε               := div_mul_cancel₀ ε hbp -- found by exact?
