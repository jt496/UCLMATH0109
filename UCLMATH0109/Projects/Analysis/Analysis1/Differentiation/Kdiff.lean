import UCLMATH0109.Projects.Analysis.Analysis1.Differentiation.Ideriv


namespace UCL
open Nat Set
open scoped Classical

/-

We introduce notation for the kth derivative of f : Δ k f and develop enough basic theory to
prove Taylor's theorem (and a bit more)

-/

/-- kdash k f is the kth derivative of f if it exists-/
noncomputable def kdash : ℕ → (ℝ → ℝ) → ℝ → ℝ
| 0, f => f -- the 0th derivative of f is just f
-- the `(k + 1)-th` derivative of `f` at `a` is the derivative of the `k-th`
-- derivative of `f` at `a`, if this exists otherwise it is 0.
| k + 1, f => fun a => if h : ∃ d, ∂ (kdash k f) a d then h.choose else 0

notation "Δ" => kdash
#check Δ

/-- the zeroth derivative  of f is f -/
@[simp]
lemma kdash_zero (f : ℝ → ℝ) : Δ 0 f = f :=
by
  sorry

/-- f is `Ikdfble k a b` iff for every `j < k` the derivative of the jth derivative
exists on (a,b) i.e. it is `k-times` differentiable on (a,b) -/
def Ikdfble (k : ℕ) (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ d : ℕ → ℝ → ℝ, ∀ j < k, ∀ x ∈ Ioo a b, ∂ (Δ j f) x (d j x)

/-
Results required for Taylors lemma
-/
section forTaylor

/-- If  f is m-dfble on (a,b)  and k ≤ m then it is k-dfble  (a,b) -/
lemma Ikdfble_le (hle : k ≤ m) (hd : Ikdfble m f a b) : Ikdfble k f a b :=
by
  sorry

/-- f' exists on (a,b) iff the 1st derivative exists on (a,b)-/
lemma Ikdfble_one_iff : Ikdfble 1 f a b ↔ Idfble f a b :=
by
  sorry

/-- If f is k-dfble on (a,b) and `Δ k f` is dfble on (a,b) then f is (k+1)-dfble on (a,b) -/
lemma Ikdfble_succ (hdk : Ikdfble k f a b) (hd1 : Idfble (Δ k f) a b) :
    Ikdfble (k + 1) f a b :=
by
  sorry

/-- If f is (k+1)-dfble on (a,b) then  -/
lemma Ikdfble_imp_exists (h : Ikdfble (k + 1) f a b) : ∀ x ∈ Ioo a b, ∃ d, ∂ (Δ k f) x d :=
by
  sorry

/-- If f is (k+1)-differentiable on (a,b) then the derivative of `Δ k f` on
(a,b) is `Δ (k+1) f`-/
lemma Ideriv_kdash (hd : Ikdfble (k + 1) f a b) : Ideriv (Δ k f) (Δ (k + 1) f) a b :=
by
  sorry

/-- If f is (k+1)-dfble then Δ (k+1) f is the derivative of Δ k f -/
lemma kdash_rw (d : ℝ → ℝ) (h : Ikdfble (k + 1) f a b) :
    ∀ x ∈ Ioo a b, Δ (k + 1) f x = d x ↔ ∂ (Δ k f) x (d x) :=
by
  sorry

/-- Given the derivative of the kth derivative we have the (k+1)th derivative -/
lemma kdash_eq_ideriv (h : Ideriv (Δ k f) d a b) : ∀ x ∈ Ioo a b, Δ (k + 1) f x = d x :=
by
  sorry

/-- If f is (k+1)-dfble then its kth derivative is dfble  -/
lemma Ikdfble_succ_imp (hdk : Ikdfble (k + 1) f a b) : Idfble (Δ k f) a b :=
by
  sorry

/-- The first derivative -/
lemma kdash_one (h : Ideriv f d a b) : ∀ x ∈ Ioo a b, Δ 1 f x = d x :=
by
  sorry

/-- rewrite between Ideriv and Δ 1 -/
lemma kdash_one_rw (hd : Idfble f a b) : Ideriv f d a b ↔ ∀ x ∈ Ioo a b, Δ 1 f x = d x :=
by
  sorry

/-- If f is Idfble then ∂ f  = Δ 1 f on (a,b) ... -/
lemma kdash_one' (hd : Idfble f a b) : Ideriv f (Δ 1 f) a b :=
by
  sorry

end forTaylor
