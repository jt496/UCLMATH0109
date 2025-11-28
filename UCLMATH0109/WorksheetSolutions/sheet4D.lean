import Mathlib.Tactic
import Mathlib.Data.Finset.Card
-- the next line allows us to see exactly what `simp` does
set_option trace.Meta.Tactic.simp.rewrite true


/-
In this sheet we will try to prove some simple results in a variety
of areas of maths using `simp`.

Some of these will not be solved completely by `simp` but will get you close enough to
use `apply?` or some higher level tactic such as `ring` or `linarith` etc.


Remember `simp` will not use any hypotheses you have unless you tell it to.
e.g. `simp? [h]` will try to simplify using simp lemmas *and* the hypothesis `h`.

Also if you want to use a lemma that is not marked `@[simp]` then you should add
it `simp? [lemma]


Using `simp` can be a good way of exploring an area of Mathlib, in particular
if simp suggests a choice of lemmas to prove one goal you may find
results nearby that will help prove similar goals.
-/

-- 01
example (n : ℕ) (x : ℝ) : (-x)^(2*n) = x ^(2*n)  :=by
  simp

-- 02
example (h : Even n ) (x : ℝ) : (-x)^(3*n) * x^(n + n)= x ^(5*n)  :=by
  simp only [h, Even.mul_left, Even.neg_pow]
  ring


-- If G is a Group with elements x,y then `Commute x y` means `x * y = y * x`
-- 03
example [Group G] (x y : G) (h : Commute x y)  : Commute (y^3*x) (y^2):=by
  simp [h]

-- 04
example [Group G] [Group H] (x y : G) (φ : G →* H) (h : φ x = φ y) : φ (y⁻¹*x) =1 :=by
  simp [h]
/-
If `z : ℤ` then `Int.natAbs z = |z|` is the absolute value of `z` as a
natural number.
-/
#check Int.natAbs -- ℤ → ℕ

-- 05
example (a b : ℤ) (h: a ≤ b) : Int.natAbs (b - a) = b - a:=by
  simp [h]

/-
If `x y : ℤ` then `x % y` is the remainder of `x` modulo `y`.

For `y ≠ 0` this is defined to be the smallest nonnegative integer
congruent to `x` mod `y`.

(For `y = 0` it is defined by `x % 0 := x`)

The actual function is called `Int.emod` so w

-/
#eval (7 : ℤ) % 3   -- 1
#eval (-12) % -5    -- 3
#eval (-7) % -12    -- 5
#eval (10 : ℤ) % 0  -- 10

-- 06
example (m k n : ℤ) (h : a = b) : (m % k + n ) % k + a = b +  (m + n % k) % k:=by
  simp only [Int.emod_add_emod, h, Int.add_emod_emod] -- found using `simp? [h]`
  exact Int.add_comm ((m + n) % k) b  -- found via apply?



/-
A `Metric Space X` is a type X with a distance function `dist`.
 Then `Metric.ball x r`, where `x ∈ X` and `r ∈ ℝ`, is the set of points
 `{y | dist x y < r}`
-/
-- 07 If x,y ∈ X then there exists `n ∈ ℕ` such that `x ∈ ball y n`
example [MetricSpace X] (x y : X): ∃ (n : ℕ), x ∈ Metric.ball y n :=by
  simp only [Metric.mem_ball] -- found using `simp?`
  exact exists_nat_gt (dist x y) -- found using `exact?`

/-
If X is a metric space then `Metric.sphere c r := {x : X | dist x c = r}`,

In our next example `simp` won't initially work, you first need to tell Lean
what to use for `c` and `r` and `intro`
-/
-- 08
example [MetricSpace X] (x y z : X) (hd : dist z x = dist x y) : ∃ c r, {y , z} ⊆ Metric.sphere c r:=by
  use x,(dist y x)
  intro a ha
  -- use `simp? at *` to find the next line
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, Metric.mem_sphere] at *
  cases ha with
  | inl h =>
    rw [h];
  | inr h =>
    rw [h,hd]; exact dist_comm x y

-- 09 Hint: use `by_cases`
example (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) : Finset.card {a,b,c} = 3 ∨ b = c :=by
  by_cases hbc : b = c
  · right; exact hbc
  · left;
    simp [hbc, hab, hac]

/-
If `S : Set X` then `S` is simply a predicate `S : X → Prop`.

If `T : Finset X` then `T` is a finite subset of terms of type `X` but it is also constructive in that
there is `List` that enumerates the elements of `T`.

This difference means that the simple proof of 10A below doesn't work for 10B.
-/
-- 10A
example (A B : Set ℕ) (hxA : x ∈ A) (hxB : x ∈ B) : (A ∩ B).Nonempty:=by
  use x
  exact ⟨hxA,hxB⟩

-- Using `simp` will typically allow us work around this issue.
-- 10B
example (A B : Finset ℕ) (hxA : x ∈ A) (hxB : x ∈ B) : (A ∩ B).Nonempty:=by
  use x
  simp only [Finset.mem_inter]
  exact ⟨hxA,hxB⟩

-- 11
example (A B C : Finset ℕ) (hab : x ∈ A ∩ B) (hac : x ∈ B ∩ C) : (A ∩ B ∩ C).Nonempty :=by
  use x
  -- use `simp? at *` to find the next line
  simp only [Finset.mem_inter, Finset.inter_assoc] at *
  use hab.1


-- 12
example (A B   : Finset ℕ) (hx : x ∈ A ∩ B) (hy : y ∈ B) (hne : x ≠ y) : 2 ≤ B.card :=by
  have  hc2: ({x ,y} : Finset ℕ).card = 2
  · simp only [Finset.mem_singleton, hne, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton]
  rw [← hc2]
  have hxy : {x,y} ⊆ B
  · intro a ha
    -- use `simp? at *` to find the next line
    simp only [Finset.mem_inter, ne_eq, Finset.mem_singleton, Finset.mem_insert] at *
    cases ha with
    | inl h => rw [h]; exact hx.2
    | inr h => rw [h]; exact hy
  exact Finset.card_le_card hxy -- found using `exact?`
