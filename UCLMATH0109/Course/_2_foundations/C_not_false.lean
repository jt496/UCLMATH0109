import Mathlib.Tactic

/-
# Not : ¬ P  (tactics: contradiction / intro / apply / exfalso / by_cases)
We would like `not P` to be the proposition that is true iff P is False

In particular if we have `P` and `¬P` in the local context then we have a `contradiction`
and from this we can prove any proposition Q
-/
example (P Q : Prop) (hp: P) (hnp: ¬ P) : Q :=
by
  contradiction



/-  To prove `¬ P` we need to show that assuming `P` we get a contradiction.

In Lean `¬ P` is formally defined as `P → False` so it is an implication.
We can start a proof of `¬ P` with `intro hp` and then we try to derive a contradiction.
-/

example (P : Prop) : ¬ (P ∧ ¬P):=
by
  intro h
  obtain ⟨hp,hnp⟩:= h
  contradiction



/-
Since **any** proposition `Q` follows from a contradiction we can always replace any goal
`⊢ Q` by `⊢ False` the Lean tactic for this is `exfalso`
-/
example (Q : Prop) (hf : False ) : Q :=
by
  -- Change the goal from `⊢ P` to `⊢ False`
  exfalso
-- Complete the proof using `hf : False`
  exact hf

-- In our next example we could start with `intro hp`, `intro hn`
-- but these two tactics can me merged into one.
example (P : Prop) : P → ¬¬P :=
by
  intro _ _
  contradiction

/-
In order to prove that `P` and `¬¬P` are equivalent we need to assume the
Law of the Excluded Middle, which says that for any proposition P we have:
 `P ∨ ¬ P`
The Lean tactic `by_cases hp : P` allows us to use this to construct a proof into
two goals where in the first we have `hp : P` and in the second we have `hp : ¬P`
-/
example (P : Prop) : ¬¬ P → P:=
by
  intro hnp
  by_cases hp : P
  · exact hp
-- We have `hp: ¬P` and `hnp: ¬¬P` in the context which is a contradiction
  · contradiction


/-
# True : (tactic : trivial)
`True` is the proposition that is trivially true, its proof is `trivial`
-/
example (P : Prop) : P → True :=
by
  intro -- we don't need to use a name for the `intro` since we won't use it
  trivial


/-
# Now do exercises and examples in sheet2C.lean
-/
