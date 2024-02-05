import Mathlib.Tactic

/-

# In-class test : total 30 marks

-/

-- 01 (3 marks)
example (P Q : Prop) (hq : Q) : (P → Q → P) → (Q → P) → P:=
by
  sorry


-- 02 (3 marks)
example  (A B : α → Prop) : (¬ ∃ x, A x ∧ B x) ↔ ∀ x, A x → ¬ B x :=
by
  sorry


-- 03 (3 marks)
example (P Q : Prop) : (P ∧ ¬Q) → (P ∨ Q) ∧ (¬ (P ∧ Q)):=
by
  sorry


-- 04 (3 marks)
example (α : Type) (x y : α) (R S : α → α → Prop) (h : ∀ a b, R a b → S a b)
(Rsymm : Symmetric R) : R x y → S y x :=
by
  sorry

def double : ℕ → ℕ := fun a => 2*a


-- 05 (1 mark)
lemma double_eq (a : ℕ) : double a = 2*a :=
by
  sorry


def redouble : ℕ → ℕ → ℕ
| a , 0       => a
| a , (n + 1) => redouble (double a) n


-- 06 (1 mark)
lemma redouble_zero (a : ℕ) : redouble a 0 = a :=
by
  sorry


-- 07 (1 mark)
lemma redouble_succ (a : ℕ) : redouble a (n + 1) = redouble (double a) n :=
by
  sorry


-- 08 (4 marks)
lemma redouble_eq (n : ℕ) : ∀ a, redouble a n = 2^n * a :=
by
  induction n with
  | zero => sorry
  | succ n ih => sorry




-- 09 (3 marks)
lemma redouble_swap (a n : ℕ) : redouble (2^a) n = redouble (2^n) a :=
by
  -- # Hint: you don't need induction
  sorry


-- A function `f : ℝ → ℝ` is continuous at `a` iff
def Cts (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0 , ∀ x, |x - a| < δ → |f x - f a| < ε


-- 10 (4 marks) If `f` and `g` are continuous at `a` then so is `f + g`
example (hf : Cts f a) (hg : Cts g a):  Cts (f + g) a :=
by
  intro ε he
  dsimp
  obtain ⟨d₁, hd1p, hd1⟩:=hf (ε/2) (half_pos he)
  obtain ⟨d₂, hd2p, hd2⟩:=hg (ε/2) (half_pos he)
  use min d₁ d₂
  constructor
  · sorry
  · intro x hx
    have hd1' : |x - a| < d₁
    · sorry
    have hd2' : |x - a| < d₂
    · sorry
    specialize hd1 x hd1'
    specialize hd2 x hd2'
    calc
    _ = |f x - f a + (g x - g a)|  := by sorry
    _ ≤ |f x  - f a| + |g x - g a| := by sorry
    _ < (ε/2) + (ε/2)              := by sorry
    _ = _                          := by sorry



-- If `f` is cts at `g(a)` and `g` is cts at `a` then `f ∘ g` is cts at `a`
-- 11 (4 marks)
example (hf : Cts f (g a)) (hg : Cts g a) :  Cts (f ∘ g) a :=
by
  sorry
