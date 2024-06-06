import Mathlib.Tactic.Basic




-- 01
example  (A B C : Type) (f : A → B) (g : B → C) (x : A) : C :=
by
  sorry

-- 02
example (α β γ : Type)  (g : γ → α) : (α → β) → (γ → β) :=
by
  sorry

-- 03
example (A B C D : Type) (f : A  → B) (g : B → C) (h : C → D) (a : A): D :=
by
  sorry

-- 04
example (A B C D E : Type)(f : A → B) (g : B → C) (h : D → E) (i : C → E) (x : A) : E :=
by
  sorry

-- 05
example (A B : Type) : ((A → B) → (A → A)) → ((A → A) → (B → A)) → ((B → A) → (B → A)) :=
by
  sorry
