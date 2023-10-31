import Mathlib.Tactic

/-
This file demonstrates the use of the tactics `simp` and `simp?`.

`simp` searches for ways to `rw` a goal in order to make it "simpler".
It doesn't search through the whole of Mathlib, but onlt the lemmas and theorems
with the attribute `@[simp]` just before their statement. Such lemmas are
always equtions or iff statements, in which the RHS is in some sense simpler than the LHS.
Often, `simp` closes the goal completely.
-/

example : (-1 : ℝ)^4 = 1 :=
by
  simp -- of course, `ring` would also work here.

/-
We can also tell `simp` to try using extra lemmas (i.e. not just those lemmas with
the attribute @[simp]. This is dome using the syntax `simp [lemma₁, lemma₂, ...]`.
-/

example (x : ℝ) (h : x = -1) : (x^2 * x^2)^100 = 1 :=
by
  simp [h]

/-
If you know examply which `simp` lemma you want to use, then you can type
`simp only [lemma₁, lemma₂, ...]`. If `simp` does not completely close the current goal,
then you should always replace it by `simp only ...`. If you do not do this, then
your code could crash after a Mathlib update (because new `simp` lemmas might be added which
change the state at the end of your simp command).

If we type `simp?` instead of `simp`, then lean will tell us which lemmas it has used,
and offer to replace your `simp` by an equivalent `simp only ...`. This should always
be done if `simp` is not completely closing a goal.
-/

example (x : ℝ) (h : x = -1) : x^(2 * n + 2) = 1 :=
by
  simp only [h]
  rw [neg_one_pow_eq_one_iff_even, Nat.even_add]
  simp?
  norm_num


/-
We may train `simp` by adding the attribute `@[simp]` to some of our own lemmas.
In thw following example we let

`ω = (1 + √-3) / 2`, and prove some standard facts about powers of `ω`.
-/

open Complex

notation "√3" => Real.sqrt 3

@[simp]
lemma rt3_sq : √3^2 = 3 :=
by
  apply Real.sq_sqrt
  norm_num

noncomputable def ω : ℂ := ⟨1/2, √3 / 2⟩

@[simp]
lemma omega_re : ω.re = 1/2 := by rfl

@[simp]
lemma omega_im : ω.im = Real.sqrt 3 / 2 := by rfl

@[simp]
lemma omega_sq : ω ^ 2 = ω - 1 :=
by
  ext
  · simp only [pow_two, mul_re, omega_re, one_div, omega_im, sub_re, one_re]
    calc
      _ = 4⁻¹ - √3^2 / 4         := by ring
      _ = 4⁻¹ - 3 / 4            := by simp
      _ = _                      := by ring
  · simp only [pow_two, mul_im, omega_re, one_div, omega_im, sub_im, one_im, sub_zero]
    ring

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
