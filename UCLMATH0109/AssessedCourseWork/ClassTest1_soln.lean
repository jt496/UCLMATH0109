import Mathlib.Tactic

/-

# In-class test : total 30 marks

-/

-- 01 (3 marks)
example (P Q : Prop) (hq : Q) : (P → Q → P) → (Q → P) → P:=
by
  intro _ hqp
  apply hqp hq


-- 02 (3 marks)
example  (A B : α → Prop) : (¬ ∃ x, A x ∧ B x) ↔ ∀ x, A x → ¬ B x :=
by
  push_neg
  rfl

-- 03 (3 marks)
example (P Q : Prop) : (P ∧ ¬Q) → (P ∨ Q) ∧ (¬ (P ∧ Q)):=
by
  intro ⟨hp,hnq⟩
  constructor
  · left; exact hp
  · push_neg
    intro _
    apply hnq

-- 04 (3 marks)
example (α : Type) (x y : α) (R S : α → α → Prop) (h : ∀ a b, R a b → S a b) (Rsymm : Symmetric R) :
R x y → S y x :=
by
  intro hr
  apply h _ _ (Rsymm hr)

def double : ℕ → ℕ := fun a => 2*a

-- 05 (1 mark)
lemma double_eq (a : ℕ) : double a = 2*a :=
by
  rfl

def redouble : ℕ → ℕ → ℕ
| a , 0       => a
| a , (n + 1) => redouble (double a) n

-- 06 (1 mark)
lemma redouble_zero (a : ℕ) : redouble a 0 = a :=
by
  rfl

-- 07 (1 mark)
lemma redouble_succ (a : ℕ) : redouble a (n + 1) = redouble (double a) n :=
by
  rfl

-- 08 (4 marks)
lemma redouble_eq (n : ℕ) : ∀ a, redouble a n = 2^n * a :=
by
  induction n with
  | zero =>
    intro a
    rw [redouble_zero,pow_zero,one_mul]
  | succ n ih =>
    intro a
    rw [redouble_succ, double_eq, ih, ←mul_assoc]
    rfl


-- 09 (3 marks)
lemma redouble_swap (a n : ℕ) : redouble (2^a) n = redouble (2^n) a :=
by
  -- # Hint: you don't need induction
  rw [redouble_eq,redouble_eq,mul_comm]


-- A function `f : ℝ → ℝ` is continuous at `a` iff
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop:= ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a|< δ → |f x - f a| < ε


-- 10 (4 marks) If `f` and `g` are continuous at `a` then so is `f + g`
example (hf : Cts f a) (hg : Cts g a):  Cts (f + g) a :=
by
  intro ε he
  dsimp
  obtain ⟨d₁, hd1p, hd1⟩:=hf (ε/2) (half_pos he)
  obtain ⟨d₂, hd2p, hd2⟩:=hg (ε/2) (half_pos he)
  use min d₁ d₂
  constructor
  · exact lt_min hd1p hd2p
  · intro x hx
    have hd1' : |x - a| < d₁
    · apply lt_of_lt_of_le hx
      exact min_le_left d₁ d₂
    have hd2' : |x - a| < d₂
    · apply lt_of_lt_of_le hx
      exact min_le_right d₁ d₂
    specialize hd1 x hd1'
    specialize hd2 x hd2'
    calc
    _ = |f x - f a + (g x - g a)|  := by ring
    _ ≤ |f x  - f a| + |g x - g a| := by exact abs_add (f x - f a) (g x - g a)
    _ < (ε/2) + (ε/2)              := by exact add_lt_add hd1 hd2
    _ = _                          := by exact add_halves ε



-- If `f` is cts at `g(a)` and `g` is cts at `a` then `f ∘ g` is cts at `a`
-- 11 (4 marks)
example (hf : Cts f (g a)) (hg : Cts g a) :  Cts (f ∘ g) a :=
by
  intro ε he
  obtain ⟨d₁, hd1p, hd1⟩:= hf _ he
  obtain ⟨d₂, hd2p, hd2⟩:= hg _ hd1p
  use d₂, hd2p
  intro x hx
  apply hd1 _ (hd2 _ hx)
