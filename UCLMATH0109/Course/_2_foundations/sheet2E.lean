import Mathlib.Tactic


/-
# TODO write some simple questions using rfl, rw and rwa (but not using theorems from Mathlib)
-/

-- 01
example (a b : ℕ) (ha : a = 1) (hb: b = 2) : a+ 2*b +3 = 8 :=
by
  rw [ha,hb]

-- 02 
example (P Q : Prop) (hp: P ↔ Q) (hq : Q): P:=
by
  rwa [hp]

-- 03
example (α : Type) (P Q: α → Prop) (hP: ∀ x, P x ↔ Q x) (a : α) : P a ↔ Q a:=
by
  rw [hP]


/-
In our next example we have a type `α` for which multiplication on the left by ℕ is defined
(so if `n : ℕ` and `a : α` then `n * a : α` is well-defined.) 
-/
variable {α : Type} [HMul ℕ α α]
/-
This multiplication satisfies two hypotheses: 
`h2id: ∀ a, a = 2 * a` so 2 is a left-multiplicative identity 
`hmul_assoc : ∀ i j: ℕ,∀ a : α, i * (j * a) = (i * j ) * a`, so
left-multiplication by natural numbers is associative.
-/
-- 08
example (h2id: ∀ (a:α), a = 2 * a ) (hmul_assoc : ∀ i j: ℕ,∀ a : α, i * (j * a) = (i * j ) * a) (b : α): 
 b = 8 * b:=
by
  rw [h2id b, hmul_assoc, h2id (2*b), h2id (2*b), h2id (2*b), hmul_assoc,hmul_assoc,hmul_assoc]

