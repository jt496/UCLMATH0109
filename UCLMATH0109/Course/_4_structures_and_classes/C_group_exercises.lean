import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

--## WORK IN PROGRESS
/-
In the previous file, the notion of a group was defined from scratch.
Of course, groups are already defined in Mathlib, and many theorems
about groups are already there. We have imported some of these in the first
line of this file. From now on, we'll work with the Mathlib definition of
a group.
-/

/-Let `G` be a group.-/
variable (G : Type) [Group G]


open Group

-- first find the group axioms, using `exact?`
example (x y z : G) : (x*y)*z=x*(y*z) :=
by
  -- exact? 
  sorry

example (x : G) : 1*x = x :=
by
  sorry

example (x : G) : x*1 = x :=
by
  sorry


example (x : G) : x*x⁻¹ = 1 :=
by
  sorry


example (x : G): x⁻¹ * x = 1 :=
by
  sorry


-- a few simple consequences of the axioms can also be
-- found by library_search. For example:

example (x : G) : (x⁻¹)⁻¹ = x :=
by
  sorry


example (x : G) (h: x*y=1) : y = x⁻¹:=
by
  sorry





-- for the next example, you could use a "have" statement
-- to obtain the previous example as an intermediate step.
example (x y : G) (h : x*y=1) : y*x=1 :=
by
  sorry


--to prove a complicated equation which is true in any group
--(with no other hypotheses than the group axioms),
--you can use the high level tactic `group`. For example,
example (x y : G) : x*y*x⁻¹ *y^2*y⁻¹^2*x*y⁻¹*x^2 = x^3 :=
by
  sorry


-- note that `group` does not use hypotheses,
-- so it cannot solve the following. Instead,
-- you can use the `rw` tactic.
example (x y : G) (h: x=y) : x^2 = y^2 :=
by
  sorry


example (x : G) : (x^n)⁻¹ = x⁻¹ ^ n :=
by
  exact Eq.symm (inv_pow x n)

example (x : G) (n : ℤ) : x^(-n) = x⁻¹^n :=
by
  exact Eq.symm (inv_zpow' x n)


-- Have a think about this one. 
-- Of course you could prove it by a very
-- long sequence of rewrites. However it is easier to
-- prove a more general statement by induction.
example (x y : G) (h : x*y=y*x) : x^45*y^4 = y^4* x^45 :=
by
  sorry



-- here is a classic group theory exercise.
-- Suppose G is a group in which x^2=1 for every element x. 
-- Prove that G is abelian.
example (x y : G) (h: ∀ z:G , z^2=1) : x*y=y*x :=
by
  -- first prove that `z⁻¹ = z` for all elements `z` in the group.
  -- then use this formula in the case `z = y*x`, we get `(y*x)⁻¹ - y*x`.
  -- then simplify the left hand side.
  sorry

example (x y : G) (h : x * y = y^2 * x) (n : ℕ) : x^n * y = y ^ (2^n) * x^n :=
by
  induction n with
  | zero => 
    --simp
    rw [pow_zero, pow_zero, pow_one, one_mul, mul_one]
  | succ n ih =>
    rw [pow_succ, mul_assoc, ih, ←mul_assoc, ←mul_assoc]
    congr 1
    clear ih
    induction n with
    | zero =>
      simp [h]
    | succ n ih2 =>
      rw [pow_succ, mul_comm, pow_mul, pow_two,
        ←mul_assoc, ih2, mul_assoc,ih2, ←mul_assoc,
        pow_succ, pow_succ, ←pow_add, pow_succ]
      congr
      ring



example (x y : G) (h : x * y = y⁻¹ * x) : x ^ (2 * n) * y = y * x^(2 * n) := by
  sorry

example (x y : G) (h : x * y = y⁻¹ * x) : x ^ n * y = y^((-1:ℤ)^n) * x ^ n := by
  sorry
