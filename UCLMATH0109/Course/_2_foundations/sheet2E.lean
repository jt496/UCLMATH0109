import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-
  All of these examples can be solved using only `rw`, `rwa` and `rfl`
-/

-- 01
example (ha : a = 1) (hb: b = 2*a) : a + 2 * b + 3 = 8 * a :=
by
-- When Lean sees a numeral it assumes this is of type ℕ (unless told otherwise),
-- so from the hypotheses it can deduce that a and b are also of type ℕ
  rw [hb, ha]

-- 02
example (h1: a = b) (h2 : c = d) (h3: d = b) : a = c:=
by
-- Notice that Lean can work out that a,b,c and d are all of the same type
-- even though we haven't told it what type this is.
  rw [h1,h2,h3]

-- 03
example (hp: P ↔ Q) (hq : Q): P:=
by
  rwa [hp]

-- 04
example (α : Type) (P Q R: α → Prop) (hP: ∀ x, P x ↔ Q x) (a : α) (hQR: Q = R): P a ↔ R a:=
by
  rw [hP, hQR]


/-
In our next few examples we have a type `α` for which multiplication on the left by ℕ is defined
(so if `n : ℕ` and `a : α` then `n * a : α` is well-defined.)
-/
variable {α : Type} [HMul ℕ α α]
-- This multiplication satisfies two axioms:

-- Left-multiplication by natural numbers is associative.
(hmul_assoc : ∀ i j : ℕ, ∀ a : α, i * (j * a) = (i * j ) * a)
-- 2 is a left-identity
(h2id: ∀ a : α, a = 2 * a)

-- Note that we know **nothing** else about this multiplication, even `b = 1 * b` needs a proof.

-- 08
example (b : α) :
 b = 1 * b :=
by
  rw [h2id b, hmul_assoc]

-- 09
example (b : α):
 b = 8 * b:=
by
  rw [h2id b, hmul_assoc, h2id (2*b), h2id (2*b), h2id (2*b), hmul_assoc,hmul_assoc,hmul_assoc]

-- 10
example (h34: ∀ a : α, 3 * a = 4 * a) (b : α): b = 3 * b:=
by
  rw [h34, h2id b, hmul_assoc, h2id (2*b), h2id (2*b), hmul_assoc, hmul_assoc]

-- 11
example (ho: ∀ n : ℕ, ∀ a : α, (2*n)* a = (2*n + 1)* a) (k : ℕ): a = k*a :=
by

  sorry

-- 12 Bonus question using induction
example (h2id: ∀ (a : α), a = 2 * a) (hmul_assoc : ∀ i j : ℕ, ∀ a : α, i * (j * a) = (i * j ) * a) (b : α) (n m: ℕ):
 b = 2^n * b:=
by
  rw [h2id b,hmul_assoc]
  induction n with
  | zero => rfl;
  | succ n ih =>
    rw [ih, ← hmul_assoc, h2id (2*b), hmul_assoc, hmul_assoc]
    rfl
