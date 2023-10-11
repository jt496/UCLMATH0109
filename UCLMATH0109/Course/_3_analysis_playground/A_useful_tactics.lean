import Mathlib.Tactic

/-
`refine` is like `exact` except that we can replace any explicit argument that we don't 
currently have in our local context by `?_` and Lean will add this as a new goal. 

`exact?` searchs Mathlib for a result that will close the goal.
`apply?` gives suggestions for a lemma to apply when `exact?` fails.

Many of the suggestions given by `apply?` will involve `refine`
-/

example (a b : ℝ) : |a - b| = |b - a| :=
by
  sorry

example (a b c : ℝ) : |a - b| ≤ |a - c| + |c - b| :=
by
  sorry

example (a b c : ℕ) (h : c < a)  : 0 < a + b - c := 
by
  sorry

example (n : ℕ) : n < (n + 1) + 1 :=
by
  sorry


/-
Congruence lemmas: if `f = g` and `a = b` then `f a = g b`. We can prove this easily using `rw`
but the tactic `congr!` will do it for us.
-/

example (f g : ℕ → ℕ) (a b : ℕ) (hac : a = b) (hfg : f = g): f a = g b :=
by 
  sorry

/-
Sometimes `congr!` is too aggressive and results in goals that are false. We can control this using 
`congr! n` where `n = 1,2,..`

-/
example (a b c : ℕ) : a + 2*b + 2*c = (2*b + a) + (c + c) :=
by
  sorry

/-
`convert` is similar to `refine` but it works when the goal is not exactly the same as the term we use.
 It introduces new goals for us to prove that the given term is in fact correct. 
 
 It uses the same strategies as `congr!` and can be controlled in a similar way using
 `convert h using n` where `n = 1, 2, ...`
-/

example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) (hm : Monotone f) : Monotone g :=
by
  sorry

example (f : ℕ → ℝ) (h : StrictMono (2 * f)) : StrictMono (f + f):=
by
  sorry

