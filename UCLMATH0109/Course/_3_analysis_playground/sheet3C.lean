import Mathlib.Tactic
-- # work in progress

/--
`continuous_at f a` means that `f` is continuous at `a`.
-/
def continuous_at (f : ℝ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε

/--
`continuous f` means that `f` is a continuous function.
-/
def continuous (f : ℝ → ℝ) := ∀ a, continuous_at f a


/--
Fill in the proof of the `have` statament, to complete the proof that `|x|` is a
continuous function of `x`.
-/
example : continuous (fun x ↦ |x|) :=
by
  intro a ε hε
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
example : continuous (fun x ↦ 10*x) :=
by
  intro a ε hε
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
