import Mathlib.Tactic

/-
# Other useful tactics for structuring a proof

`refine` is like `exact` except that we can replace any explicit argument that we don't 
currently have in our local context by `?_` and Lean will add this as a new goal. 

`exact?` searchs Mathlib for a result that will close the goal.
`apply?` gives suggestions for a lemma to apply when `exact?` fails.

Many of the suggestions given by `apply?` will involve `refine`
-/

-- 01
example (a b : ℝ) : |a - b| = |b - a| :=
by
  sorry

-- 02
example (a b c : ℝ) : |a - b| ≤ |a - c| + |c - b| :=
by
  sorry

-- 03
example (a b c : ℕ) (h : c < a)  : 0 < a + b - c := 
by
  sorry

-- 04
example (n : ℕ) : n < (n + 1) + 1 :=
by
  sorry


/-
Congruence lemmas: if `f = g` and `a = b` then `f a = g b`. We can prove this easily using `rw`
but the tactic `congr!` will do it for us.
-/

-- 05
example (f g : ℕ → ℝ) (a b : ℕ) (hac : a = b) (hfg : f = g): f a = g b :=
by 
  sorry

/-
Sometimes `congr!` is too aggressive and results in goals that are false. We can control this using 
`congr! n` where `n = 1,2,..`
-/

-- 06
example (a b c : ℕ) : a + 2*b + 2*c = (2*b + a) + (c + c) :=
by
  sorry

/-
`convert` is similar to `refine` but it works when the goal is not exactly the same as the term we use.
 It introduces new goals for us to prove that the given term is in fact correct. 
 
 It uses the same strategies as `congr!` and can be controlled in a similar way using
 `convert h using n` where `n = 1, 2, ...`
-/

-- 07
example (f g : ℕ → ℕ) (h : ∀ n, g n = f n) (hm : Monotone f) : Monotone g :=
by
  sorry

-- 08
example (f : ℕ → ℝ) (h : StrictMono (f + f)) : StrictMono (2 * f):=
by
  sorry

/-
We already saw the `rfl` tactic that allows Lean to close any goal of the form `⊢ A ∼ A`, if 
`∼` is a reflexive relation. 

There are corresponding tactics for symmetric and transitive relations. 

If the goal is `⊢ A ∼ B` where `∼` is a symmetric relation then `symm` changes the goal to `⊢ B ∼ A`

If `h : A ∼ B` is in the local context then `h.symm` is `B ∼ A`

The most common use of this is with `=`
-/

-- 09 
example (a b : ℕ) (h : a = b) : b = a :=
by
  sorry

/-
If the goal is `⊢ A ∼ B` where `∼` is a transitive relation, then `trans C` converts this into two goals,
`⊢ A ∼ C` and `⊢ C ∼ B` 
-/  

-- 10  
example (a b c : ℕ) (h1 : a = b) (h2 : c = b) : a = c :=
by
  sorry

-- 11
example (s t u : Set ℕ) (h1: s ⊆ t) (h2 : t ⊆ u) : s ⊆ u:=
by
  sorry
