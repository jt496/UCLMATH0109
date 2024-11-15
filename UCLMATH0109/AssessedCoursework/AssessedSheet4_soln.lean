import Mathlib.Tactic

/-

A `Dedekind cut` is a partition of the rationals `(A , Aᶜ)` such that both A and Aᶜ are
nonempty with the following properties:

1)  A is a down-set: if x < y and y ∈ A then x ∈ A;

2)  A has no maximum element: if x ∈ A there exists y ∈ A with x < y.

One way of constructing the real numbers from ℚ is as Dedekind cuts.

We identify a real number `r` with the cut `(A, Aᶜ)` where `A = {x ∈ ℚ | x < r}`

-/
/--
Dedekind cut
-/
@[ext] -- two Dedekind cuts D = E iff D.A = E.A
structure Dedekind where
  A         : Set ℚ
  nonempty  : A.Nonempty
  nonempty' : Aᶜ.Nonempty
  down      : ∀ ⦃x y⦄, x < y → y ∈ A → x ∈ A
  no_max    : ∀ ⦃x⦄, x ∈ A → ∃ y ∈ A, x < y

-- the @[ext] label produces the following two results for free:
#check Dedekind.ext
#check Dedekind.ext_iff

namespace Dedekind
notation "𝔻" => Dedekind

/- All our results will now be in the Dedekind namespace -/
/-
We open a named section to explain what we are trying to prove (we will prove
some basic results in this section hence the name).
-/
section basics
variable {D : 𝔻}
variable {x y : ℚ}
/-
The use of a section allows us to introduce variables into the local context
 that will vanish once the section ends.
-/
-- 2 marks
/-- If `D = (A , Aᶜ)` is a Dedekind cut with `x ∈ A` and `y ∈ Aᶜ` then `x < y`-/
lemma lt_of_cut (hx : x ∈ D.A) (hy : y ∈ D.Aᶜ) : x < y :=by
  by_contra! h
  cases h.lt_or_eq with
  | inl h =>  exact hy <| D.down h hx
  | inr h =>  exact hy (h ▸ hx)



#check D.A         -- D.A : Set ℚ
#check D.nonempty  -- D.nonempty : Set.Nonempty D.A
#check D.nonempty' -- D.nonempty' : Set.Nonempty D.Aᶜ
#check D.down      -- D.down : ∀ ⦃x y : ℚ⦄, x < y → y ∈ D.A → x ∈ D.A
#check D.no_max    -- D.no_max : ∀ ⦃x : ℚ⦄, x ∈ D.A → ∃ y, y ∈ D.A ∧ x < y


/-- We can order Dedekind cuts with `D ≤ E` iff `D.A ⊆ E.A` -/
instance : LE 𝔻 where
  le := fun D E => D.A ⊆ E.A

lemma le' : D ≤ E ↔ D.A ⊆ E.A :=by rfl

/-- We can define `<` on Dedekind cuts by `D < E` iff `D ≤ E` and `D ≠ E`-/
instance : LT 𝔻 where
  lt := fun D E => D ≤ E ∧ ¬ E ≤ D

-- 1 mark
/-- `D < E` iff `D.A` is a proper-subset of `E.A` -/
lemma lt' : D < E ↔ D.A ⊂ E.A :=by rfl

-- 2 marks
/-- D < E iff ∃ x ∈ E.A \ D.A -/
lemma lt_iff_exists : D < E ↔ ∃ x, x ∈ E.A \ D.A:=by
  rw [lt']
  constructor
  · intro hde
    exact Set.exists_of_ssubset hde
  · intro ⟨x,hx⟩
    constructor
    · intro y hy
      apply E.down (D.lt_of_cut hy hx.2) hx.1
    · intro hf
      apply hx.2 <| hf hx.1

end basics

/-
We now establish that Dedekind cuts form a `Preorder`.

class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

-/
-- 2 marks
instance : Preorder 𝔻 where
  le_refl :=by
    intro D; rw [le'];
  le_trans :=by
    intro D E F hde hef
    rw [le'] at *
    apply hde.trans hef

/--
𝔻 contains a copy of the rational numbers given by the embedding `rat`
-/
-- 4 marks
def rat (q : ℚ) : 𝔻 :=by
  use {x : ℚ | x < q}
  · use q - 1
    simp only [Set.mem_setOf_eq, sub_lt_self_iff, zero_lt_one]
  · use q; apply lt_irrefl q
  · intro x y hxy hyx
    apply hxy.trans  hyx
  · intro x hx
    use (q + x) / 2
    simp only [Set.mem_setOf_eq] at *
    constructor <;> linarith

@[simp]
lemma rat' (q : ℚ) : (rat q).A = {x : ℚ | x < q} := rfl
-- 2 marks
/-- The map `rat` is an order embedding: i.e. it is injective and `rat p ≤ rat q ↔ p ≤ q`-/
def Rat : ℚ ↪o 𝔻 where
  toFun := rat
  inj' :=by
    intro p q hpq
    rw [Dedekind.ext_iff] at hpq
    simp only [rat'] at *
    cases lt_trichotomy p q with
    | inl h =>
      have hq : p ∉ {x | x < p} := lt_irrefl p
      rw [hpq] at hq
      contradiction
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h =>
        have hp : q ∉ {x | x < q} := lt_irrefl q
        rw [← hpq] at hp
        contradiction
  map_rel_iff' :=by
    intro p q
    -- At this point the goal looks rather unreadable so we try `dsimp`
    dsimp
    -- You could now use constructor followed by ext to finish the proof but
    -- the following result from Mathlib is easier.
    exact forall_lt_iff_le

instance : Zero 𝔻 where
zero := rat 0

/--
There is a Dedekind cut corresponding to √2
-/
-- 4 marks
def root_two : 𝔻 :=by
  use { x : ℚ | x^2 < 2 ∨ x < 0}
      -- In this solution we almost only use high level tactics:
      -- `simp?` (using the `simp only` suggestion)
      -- `exact?, ring, nlinarith` and `field_simp`
      -- This is to show you a strategy for solving problems such as this using only these tactics.
      -- It is possible to instead use lemmas from Mathlib (but this requires you to know
      -- the right lemmas to use or be able to find them).
  · use 0; left; norm_num
  · use 2; norm_num
  · intro x y hlt hy
    simp only [Set.mem_setOf_eq] at *
    by_cases hx : x < 0
    · right; exact hx
    · cases hy with
      |inl h1 => left; push_neg at hx; nlinarith
      |inr h2 => right; nlinarith;
  · intro x hx
    simp only [Set.mem_setOf_eq] at *
    by_cases hxneg : x < 0
    · exact  ⟨0,Or.inl (by norm_num),hxneg⟩
    · cases hx with
      | inl hsq =>
      -- The next line makes our proof easier to read, but we will need to use `dsimp [e]`
      -- at various points to make sure Lean understands how `e` is defined.
        let e := 1 - (x ^ 2 / 2)
        use x + (e / (2 * x + 1))
        push_neg at hxneg
        have h2x0 : 0 < 2 * x + 1 := by nlinarith
        have he0 : 0 < e :=by dsimp [e]; nlinarith
        have h2x1 : e ≤ 2 * x + 1 := by dsimp [e]; nlinarith
        have hposdiv : 0 < e / (2 * x + 1) := by exact div_pos he0 h2x0 -- exact?
        have hdivle1 : e / (2 * x + 1) ≤ 1:= by exact (div_le_one h2x0).mpr h2x1 -- exact?
        have hsqle : (e / (2 * x + 1)) ^ 2 ≤ e / (2 * x + 1) := by nlinarith
        constructor
        · left
          calc
            _ = x ^ 2 + 2 * x * e / (2 * x + 1) + (e / (2 * x + 1)) ^ 2 := by ring -- expand the brackets
            _ ≤ x ^ 2 + 2 * x * e / (2 * x + 1) + e / (2 * x + 1)       := by nlinarith -- uses hsqle
            _ = x ^ 2 + e / (2 * x + 1) * (2 * x + 1)                   := by ring -- factorise
            _ = x ^ 2 + e                                               := by field_simp -- clear the denominator using h2x0
            _ < _                                                       := by dsimp [e]; nlinarith
        · nlinarith
      | inr hneg => contradiction

/-
If `S : Set 𝔻` is nonempty and bounded above then it has a supremum defined
by taking the union of cuts in S.
-/
-- 3 marks
noncomputable
instance : SupSet 𝔻 where
  sSup :=by
    intro S
    by_cases h : S.Nonempty ∧ BddAbove S
    · use  ⋃ d ∈ S, d.A
      · -- the union is nonempty because S is nonempty and each cut in S is nonempty
        obtain ⟨d,hd⟩:= h.1
        obtain ⟨x,hx⟩ := d.nonempty
        use x
        simp only [Set.mem_iUnion, exists_prop]
        use d,hd,hx
      · -- the complement is nonempty uses the fact that there is an upper bound
        -- u for S and the complement of u is nonempty
        obtain ⟨u,hu⟩ := h.2
        obtain ⟨x,hx⟩ := u.nonempty'
        use x
        intro hf
        apply hx
        simp only [Set.mem_iUnion, exists_prop] at hf
        obtain ⟨i,hi1,hi2⟩:= hf
        exact (hu hi1) hi2
      · -- if x < y and y is in the union then y is in one of the cuts from S and x is
        -- in the same cut
        intro x y hxy hy
        simp only [Set.mem_iUnion, exists_prop] at *
        obtain ⟨i,hi1,hi2⟩:= hy
        use i,hi1
        apply i.down hxy hi2
      · -- if x is in the union then it is in one of the cuts from S and this cut contains
        -- a larger element which also belongs to the union
        intro x hx
        simp only [Set.mem_iUnion, exists_prop] at *
        obtain ⟨i,hi,hix⟩:= hx
        obtain ⟨y,hy⟩ := i.no_max hix
        use y, ⟨i,hi,hy.1⟩, hy.2
-- If S is ∅ or not bounded above we still need to return something sensible
    · exact 0

#check dif_pos -- These can be used to simplify a function defined using `by_cases` or `if then else`
#check dif_neg
-- 1 mark
lemma sSup' (S : Set 𝔻) (h1 : S.Nonempty) (h2: BddAbove S) : (sSup S).A = (⋃ d ∈ S, d.A) :=by
  dsimp [sSup]
  rw [dif_pos ⟨h1,h2⟩]

#check IsLeast
#check upperBounds
#check IsLUB

/--
`𝔻` is complete: any nonempty set of Dedekinds cuts that is bounded above
  has a least upper bound-/
-- 3 marks
theorem complete_lub (S : Set 𝔻) (hne: S.Nonempty) (hupb: BddAbove S) :
  IsLUB S (sSup S) :=by
  constructor <;> (intro d hd; rw [le',sSup' S hne hupb])
  · exact Set.subset_biUnion_of_mem hd
  · exact Set.iUnion₂_subset_iff.mpr hd
