import Mathlib.Tactic

variable (A: Type) (P Q R: A → Prop)

-- 01
example : (∀x, ∃y, P y → P x) :=
by
  intro x
  use x
  intro hx
  exact hx

-- 02
example (h : ∃ x, ¬ P x) : ¬ ∀ a, P a:=
by
  push_neg
  exact h


/-
We used the tactic `push_neg` to push negations inside a goal.

We can also use it to simplify a negated hypothesis `h : ¬ P`
with `push_neg at h`
-/

-- 03
example (h : ¬ ∀ a, ¬P a)  : ∃ x, P x:=
by
  push_neg at h
  exact h

-- 04
example : (∀ x, P x → Q x) → (∀y, Q y → R y) → (∀z, R z → P z) → (∀a, R a ↔ P a):=
by
  intro hpq hqr hrp a
  specialize hpq a
  specialize hqr a
  specialize hrp a
  constructor
  · exact hrp
  · intro hpa
    apply hqr (hpq hpa)

/-
If our hypothesis is `h: ∃x, ∃y,...` then `obtain ⟨x, y, hxy⟩ := h` will give us `x` and `y`

If our goal is `⊢ ∃y, ∃x, ...` we can first tell Lean what to use for `y` and then the
goal will change to `⊢ ∃ x,...`  so we can then tell it what to use for `x`
-/
-- 05
example  (h : ∃x, ∃y, P x → P y) : (∃x, ∃y, P y → P x):=
by
  obtain ⟨x,y,hxy⟩:= h
  use y
  use x


-- 05'
example  (h : ∃x, ∃y, P x → P y) : (∃x, ∃y, P y → P x):=
by
  obtain ⟨x,y,hxy⟩:= h
  exact ⟨y,x,hxy⟩


-- 06
example : (∀ x, P x) → (∃x, ¬ Q x) → ∃ (a b : A), ¬ (P a → Q b):=
by
  intro hp ⟨x,hx⟩
  use x,x
  intro h
  apply hx
  apply h (hp x)


-- 07
example: (∃x, ¬Q x) → (∃ y, Q y) →
  ∃ a b, ∀ z, P z → Q a ∧ ¬(P z → Q b) :=
by
  intro ⟨x,hnq⟩ ⟨y,hq⟩
  use y,x
  intro z hpz
  constructor
  · exact hq
  · intro hpq
    apply hnq (hpq hpz)

-- 08
example : (∀x, ∃y, ¬(P x → P y)) → (∃u, P u) →   (∃v, ¬ P v) :=
by
  intro h1 ⟨u,_⟩
  obtain ⟨y,hy⟩ := h1 u
  use y
  intro hpy
  apply hy
  intro _
  exact hpy

-- 09
example : (¬∀a, (P a → Q a)) ↔ ∃x, (¬Q x ∧ P x):=
by
  push_neg
  constructor
  · intro ⟨a,hpa,hnqa⟩
    use a
  · intro ⟨a,hnqa,hpa⟩
    use a

-- In the last proof we didn't need the names of the hypotheses we introduced `hpa` and `hnqa`
-- so we we could use `_` instead

-- 09'
example : (¬∀a, (P a → Q a)) ↔ ∃x, (¬Q x ∧ P x):=
by
  push_neg
  constructor
  · intro ⟨a,_,_⟩
    use a
  · intro ⟨a,_,_⟩
    use a


-- Since the two parts of the last proof are now identical we can use `all_goals` to shorten the proof
-- 09''
example : (¬∀a, (P a → Q a)) ↔ ∃x, (¬Q x ∧ P x):=
by
  push_neg
  constructor ; all_goals -- this applies the next `·` block to all open goals
  · intro ⟨a,_,_⟩
    use a


variable (C : A → A → Prop)
-- 10 The no barber theorem
-- We can do this using `by_cases`
example : ¬∃ b, ∀ a, C b a ↔ ¬ C a a :=
by
  intro hb
  obtain ⟨b,hb1⟩:= hb
  specialize hb1 b
  by_cases hbb: C b b
  · obtain ⟨hbl,_⟩:= hb1
    apply hbl hbb hbb
  · obtain ⟨hbl,hbr⟩:= hb1
    apply hbl
    · apply hbr hbb
    · apply hbr hbb

-- 10' The no barber theorem
-- But we don't actually need `by_cases`
example : ¬∃ b, ∀ a, C b a ↔ ¬ C a a :=
by
  intro hb
  obtain ⟨b,hb⟩:=hb
  specialize hb b
  apply hb.1
  · apply hb.2
    intro h
    apply hb.1 h h
  · apply hb.2
    intro h
    apply hb.1 h h
