import Mathlib.Tactic

/--
`Cts f a` means that `f` is continuous at `a` -/
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

/--
Fill in the proof of the `have` statament, to complete the proof that `|x|` is a
continuous function of `x`. -/
example (a : ℝ): Cts (fun x ↦ |x|) a :=
by
  intro ε hε
  use ε
  constructor
  · exact hε
  · intro x hx
    dsimp
    have : |(|x|-|a|)| ≤ |x-a|
    · sorry
    linarith


/-
Have a look at the following proof that `10*x` is a continuous function of `x`.
There are three `have` statements. Fill in the proof of each of these, using any tactics which you know.
-/
example (a : ℝ) : Cts (fun x ↦ 10*x) a :=
by
  intro ε hε
  let δ := ε / 10
  have : δ > 0
  · sorry
  use δ
  constructor
  · exact this
  · intro x hx
    dsimp
    rw [←mul_sub, abs_mul]
    have : |(10:ℝ)| = 10
    · sorry
    rw [this]
    have : ε = 10 * δ
    · sorry
    rw [this]
    rel [hx]
