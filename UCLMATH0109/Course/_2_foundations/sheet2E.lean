import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-
  All of these examples can be solved using only `rw`, `rwa` and `rfl`
-/

-- 01
example (ha : a = 1) (hb : b = 2*a) : a + 2 * b + 3 = 8 * a :=
by
-- When Lean sees a numeral it assumes this is of type ℕ (unless told otherwise),
-- so from the hypotheses Lean deduces that a and b are also of type ℕ (see Infoview)
  rw [hb, ha]

-- 02
example (h1 : a = b) (h2 : c = d) (h3 : d = b) : a = c :=
by
-- Notice that Lean can work out that a,b,c and d must all have same type (how?)
-- even though we haven't told it what type this is.
  rw [h1,h2,h3]

-- 03
example (hp : P ↔ Q) (hq : Q): P:=
by
  rwa [hp]

-- 04
example (α : Type) (P Q R : α → Prop) (hP : ∀ x, P x ↔ Q x) (a : α) (hQR : Q = R): P a ↔ R a:=
by
  rw [hP, hQR]

-- 05
example  (h2 : R ↔ Q) (h3 : R ↔ P) (hp : P) : Q :=
by
  rw [← h3] at hp
  rwa [← h2]


/-
In our last few examples we introduce a type `α` for which multiplication on the left by ℕ is defined
(so if `n : ℕ` and `a : α` then `n * a` is well-defined and has type `α`.)
-/
variable {α : Type} [HMul ℕ α α]

-- This multiplication satisfies two axioms:

-- Left-multiplication by ℕ is associative.
(hmul_assoc : ∀ i j : ℕ, ∀ a : α, i * (j * a) = (i * j ) * a)

-- Two is a left-identity
(h2id: ∀ a : α, a = 2 * a)

-- Note that we know **nothing** else about this multiplication, even `b = 1 * b` needs a proof.

-- However Lean does know how to do arithmetic in ℕ so, for example, if `a : α` then
--  `(2 * 3) * a = 6 * a` is true by `rfl`

-- 06
example (b : α) : 12 * b = 3 * 4 * b :=
by
  rfl

-- 07 associativity does not hold by definition so rfl won't work here.
example (b : α) : 10 * b = 5 * (2 * b) :=
by
--  rfl fails
  rw [hmul_assoc]

-- 08
example (b : α) : b = 1 * b :=
by
  rw [h2id b, hmul_assoc]

-- 09
example (b : α) : b = 8 * b:=
by
  rw [h2id b, hmul_assoc, h2id (2*b), h2id (2*b), h2id (2*b), hmul_assoc,hmul_assoc,hmul_assoc]

-- 10
example (b : α) : 3 * b = 12 * b :=
by
  rw [h2id b, hmul_assoc 12, h2id (2*b), h2id (2*b), hmul_assoc, hmul_assoc, hmul_assoc]


-- 11 Bonus question using induction for those who know it
example (b : α) (n : ℕ):
 b = 2^n * b:=
by
  rw [h2id b,hmul_assoc]
  induction n with
  | zero => rfl;
  | succ n ih =>
    rw [ih, ← hmul_assoc, h2id (2*b), hmul_assoc, hmul_assoc]
    rfl
