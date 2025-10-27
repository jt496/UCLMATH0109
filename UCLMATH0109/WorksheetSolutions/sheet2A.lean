import Mathlib.Tactic

/--
# Worked solutions -- note we give a few different versions in some cases
-/


-- 01
example  (A B C : Type) (f : A → B) (g : B → C) (x : A) : C :=
by
  apply g
  apply f
  exact x


-- 01'
example  (A B C : Type) (f : A → B) (g : B → C) (x : A) : C :=
by
  apply g (f x)

-- 01''
example  (A B C : Type) (f : A → B) (g : B → C) (x : A) : C :=
by
  exact g (f x)


-- 02
example (α β γ : Type)  (g : γ → α) : (α → β) → (γ → β) :=
by
  intro f
  intro c
  apply f
  apply g
  exact c

-- 02'
example (α β γ : Type)  (g : γ → α) : (α → β) → (γ → β) :=
by
  intro f c
  apply f (g c)


-- 03
example (A B C D : Type) (f : A  → B) (g : B → C) (h : C → D) (a : A): D :=
by
  apply h
  apply g
  apply f
  exact a

-- 03'
example (A B C D : Type) (f : A  → B) (g : B → C) (h : C → D) (a : A): D :=
by
  apply h (g (f a))


-- 04
example (A B C D E : Type)(f : A → B) (g : B → C) (h : D → E) (i : C → E) (x : A) : E :=
by
  apply i
  apply g
  apply f
  exact x

-- 04'
example (A B C D E : Type)(f : A → B) (g : B → C) (h : D → E) (i : C → E) (x : A) : E :=
by
  apply i (g (f x))


-- 04''
example (A B C D E : Type)(f : A → B) (g : B → C) (h : D → E) (i : C → E) (x : A) : E :=
by
  apply i <| g <| f x


-- 05
example (A B : Type) : ((A → B) → (A → A)) → ((A → A) → (B → A)) → ((B → A) → (B → A)) :=
by
  intro _ _ h
  exact h
