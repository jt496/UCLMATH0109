import Mathlib.Tactic

/-
This file demonstrates the use of the tactic `simp`.
Much more information on this subject can be found in the following page:
https://leanprover-community.github.io/extras/simp.html.

`simp` is a high level tactic, which repeatedly searches for ways to `rw` a goal
in order to make it "simpler". It doesn't search through the whole of Mathlib,
but only the `lemma`s and `theorem`s marked with the attribute `@[simp]` just
before their statement. Such `lemma`s are always equations or iff statements,
in which the RHS is in some sense simpler than the LHS.

Often, `simp` closes the goal completely.
-/
example : 1 * y * 1 * 1 * x = y * 1 * 1 * x :=
by
  sorry

/-
Changing `simp` to `simp?` will give us a list of the `lemma`s used, and we can see the `@[simp]`
in their statements in Mathlib.

We can also tell `simp` to try using extra `lemma`s (i.e. not just those `lemma`s with
the attribute @[simp]). This is done using the syntax `simp [h1, h2, ...]`.
-/
example (x : ℝ) (h : x = -1) : (x^2 * x^2)^100 = 1 :=
by
  sorry
/-
If you already know exactly which `simp` lemmas you want to use, then you can type
`simp only [lemma₁, lemma₂, ...]`. If `simp` does not completely close the current goal,
then you should always replace it by `simp only ...`. If you do not do this, then
your code could crash after a Mathlib update (because new `simp` lemmas might be added which
change the state at the end of your simp command).

If we type `simp?` instead of `simp`, then lean will tell us which lemmas it has used,
and offer to replace your `simp` by an equivalent `simp only ...`. This should always
be done if `simp` is not completely closing a goal.
-/
example : ((-1) ^ n) ^ 2 = 1 :=
by
  sorry

/-
We may train `simp` by adding the attribute `@[simp]` to some of our own lemmas.
In the following example we let

`ω = (1 + √-3) / 2`, and prove some standard facts about powers of `ω`.
-/

/--define the notation `√3` for the positive real square root of `3`.-/
notation "√3" => Real.sqrt 3

@[simp]
lemma rt3_sq : √3^2 = 3 :=
by
  norm_num

/--The 6th root of unity `(1+I*√3)/2`.-/
@[simps]
noncomputable def ω : ℂ := ⟨1/2, √3 / 2⟩

-- @[simp]
-- lemma ω_re : ω.re = 1/2 := by rfl

-- @[simp]
-- lemma ω_im : ω.im = Real.sqrt 3 / 2 := by rfl

@[simp]
lemma omega_sq : ω ^ 2 = ω - 1 :=
by
  ext
  · simp
    calc
      _ = 4⁻¹ - √3^2 / 4         := by sorry
      _ = 4⁻¹ - 3 / 4            := by sorry
      _ = _                      := by sorry
  · simp
    sorry

@[simp]
lemma omega_pow_three : ω^3 = -1 :=
by
  calc
  ω^3 = ω * ω^2         := by ring
  _   = ω * (ω-1)       := by simp
  _   = ω^2 - ω         := by ring
  _   = (ω-1) - ω       := by simp
  _   = -1              := by ring

@[simp]
lemma omega_pow_six : ω^6 = 1 :=
by
  calc
  _ = ω^3 * ω^3       := by ring
  _ = (-1) * (-1)     := by simp
  _ = 1               := by ring

example : ω ^ (6 * n + 13) = ω :=
by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, mul_zero, zero_add]
    calc
      ω^13 = ω^6 * ω^6 * ω := by ring
      _    = ω             := by simp
  | succ n ih =>
    calc
      _ = ω ^ (6 * n + 13) * ω ^ 6  := by rw [Nat.succ_eq_add_one]; ring
      _ = ω                         := by simp [ih]
