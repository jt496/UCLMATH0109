import Mathlib


namespace SimpleGraph
variable {V : Type u} [DecidableEq V]


/-
# This project is on the Mycielskian of a graph and its basic properties.
# See the project pdf for details.
-/
-- You will need to use the `SimpleGraph` part of Mathlib.
#check SimpleGraph V -- this is the type of simple graphs with vertex set V
#print SimpleGraph  --
/-
structure SimpleGraph (V : Type u) where
Adj : V → V → Prop
symm : Symmetric Adj := by aesop_graph
loopless : Irreflexive Adj := by aesop_graph

So if `G : SimpleGraph V` then `G.Adj` is the adjaceny relation on the vertex set V
i.e. `G.Adj x y` is true iff `xy` is an edge of G.

The `symm` part of the definition ensures that edges are undirected
in the sense that `xy` is an edge iff `yx` is an edge

The `loopless` part ensures that edges are not loops i.e. `xx` is never an edge.
-/

/-
We also need to use `Sum` types and `Option` types.

If A and B are types then `Sum A B` is the disjoint union of A and B
and can be written as `A ⊕ B`.
So if `x : A ⊕ B` then
-/
#check Sum
/-
inductive Sum (α : Type u) (β : Type v) where
| inl (val : α) : Sum α β
| inr (val : β) : Sum α β

If `x : A ⊕ B` you should think of this as an `or` statement:
`x` is either of type A of B and we can do `cases` just like an `or`

cases x with
| inl x => sorry -- (x : A)
| inr x => sorry -- (x : B)

If A is a type then `Option A` is `A` with a new extra element called `none`
-/
#check Option
/-
inductive Option (α : Type u) where
| none : Option α
| some (val : α) : Option α

If `x : Option A` then we can again think of this as an `or` statement
and we can use `cases`

cases x with
| none   => sorry -- Here `x` will vanish and be replace by `none` in the local context
| some x => sorry -- (x : A)

-/
/-

If `G : SimpleGraph V` then the natural type to use for the Mycielskian
is `V ⊕ (Option V)`.
We can think of this as the new vertex set consisting
of a copy of the original vertex set V and a new vertex set that is a copy of the
original vertex set with a new special vertex `none`.

The definition of the Mycielskian is given below with some of the details
of the proofs omitted.
-/


@[reducible]
def Mycielskian (G : SimpleGraph V) : SimpleGraph (V ⊕ Option V) where
  Adj := fun x y => match x, y with
    | Sum.inl v, Sum.inl w => G.Adj v w
    | Sum.inl v, Sum.inr (some w) => G.Adj v w
    | Sum.inr (some v), Sum.inl w => G.Adj v w
    | Sum.inr (some _), Sum.inr none => True
    | Sum.inr none, Sum.inr (some _) => True
    | _, _ => False
  symm := by
    intro x y hxy
    cases x with
    | inl v =>
      cases y with
      | inl w => simp only at *; exact hxy.symm
      | inr w =>
        cases w with
        | some w => simp only at *; exact hxy.symm
        | none => simp only at *;
    | inr v => sorry
  loopless := by sorry

namespace Mycielskian

/- An example of the kind of definitional lemma you may want to start with.-/
@[simp]
lemma adj_l_l (G : SimpleGraph V) (v w : V) : (Mycielskian G).Adj (Sum.inl v) (Sum.inl w) = G.Adj v w := rfl




#check Finset.card_eq_three
#check CliqueFree
#check is3Clique_triple_iff

variable {G : SimpleGraph V}
/-- If G is K₃-free then so is its Mycielskian -/
lemma K3_free (h : G.CliqueFree 3) : G.Mycielskian.CliqueFree 3 := by
  sorry

/-
We now move on to the chromatic number of the Mycielskian, this involve graph
colorings.
A `G.Coloring β` is a valid coloring of the vertices of `G` with colors from the
type `β`.
We say `G` is `k`-colorable if there is a coloring of `G` with `k` colors.
In Lean this is `G.Colorable k`
-/
#check Coloring
#check Colorable
/-
To construct a `β` coloring we need to define a pair `⟨col, valid⟩` where
`col` is a map from `V → β` and `valid` is a proof that if two vertices are adjacent
they receive different colors.
-/
-- Useful facts about `Fin`
#check Fin.last
#check Fin.val_lt_last
#check Fin.eq_of_val_eq
#check Fin.castSucc_inj
#check Fin.coe_eq_castSucc
/-- Given any (k + 1)-coloring of the Mycielskian get the equivalent coloring with the new
special vertex `Sum.inr none` colored with the last color in Fin (k + 1) -/
abbrev succ_col (c : G.Mycielskian.Coloring (Fin (k + 1))) : G.Mycielskian.Coloring (Fin (k + 1)) :=
  G.Mycielskian.recolorOfEquiv (Equiv.swap (Fin.last k) (c (Sum.inr none))) c

/-- Given a (k + 1) - coloring of the Mycielskian produce a k-coloring of G -/
def coloring_of_self  (c : G.Mycielskian.Coloring (Fin (k + 1))) : G.Coloring (Fin k) :=by
  sorry

/-- Given a k - coloring of G get a (k + 1) -coloring of the Mycielskian -/
def coloring_of_mycielskian  (c : G.Coloring (Fin k)) : G.Mycielskian.Coloring (Fin (k + 1)) :=by
  sorry

/--
G is k-colorable iff the Mycielskian of G is k + 1 colorable.
(This is equivalent to saying the chromatic number of the Mycielskian equals the chromatic
number of G plus 1.)
-/
theorem colorable_iff (k : ℕ): G.Colorable k ↔ G.Mycielskian.Colorable (k + 1):= by
  sorry

/-
We now move on to the iterated Mycielskian, starting from K₂.

We first define its vertex set which we will call `W n`
-/

/-- The vertex set for the iterated Mycielskian graph starting with K₂ -/
abbrev W : ℕ → Type
| 0 => Fin 2  -- {0, 1}
| n + 1 => (W n) ⊕ Option (W n)


/-- The nth iterated Mycielskian Mₙ -/
abbrev M : (n : ℕ) → SimpleGraph (W n)
| 0 => ⊤ -- M 0 is the complete graph on {0, 1} i.e. a single edge
| n + 1 => (M n).Mycielskian -- the Mycielskian of M n



/-- The vertex set of the nth iterated Mycielskian has Decidable equality -/
instance (n : ℕ) : DecidableEq (W n) :=by
  induction n with
  | zero => infer_instance
  | succ _ _ => infer_instance


/-- The vertex set of the nth iterated Mycielskian is finite-/
instance instFintypeWn (n : ℕ) : Fintype (W n) :=by
  induction n with
  | zero => infer_instance
  | succ _ _ => infer_instance

/-- The vertex set of the (n + 1)-th iterated Mycielskian is Nonempty -/
instance (n : ℕ) : Nonempty (W n) :=by
  induction n with
  | zero => infer_instance
  | succ _ _ => infer_instance



/-- The vertex set of the nth iterated Mycielskian has cardinalty 3 * 2ⁿ - 1 -/
@[simp]
lemma card_W (n : ℕ) : Fintype.card (W n) = 3 * 2 ^ n - 1 := by
  sorry


/-- The nth iterated Mycielskian is K₃-free, has chromatic number n + 2 and order 3 * 2ⁿ -1 -/
theorem K3_free_chromatic_eq_order (n : ℕ) :
    (M n).CliqueFree 3 ∧ (M n).chromaticNumber = n + 2 ∧ Fintype.card (W n) = 3 * 2 ^ n - 1 :=by
      sorry


instance (G : SimpleGraph V) [DecidableRel G.Adj]: DecidableRel (Mycielskian G).Adj := by
  sorry

instance  : ∀ n, DecidableRel (M n).Adj := by
  sorry

instance instFintypeEdgeMn  : ∀ n,  Fintype (M n).edgeSet := by
  sorry


set_option maxRecDepth 200000 -- This will help if your computer is slow. Alternatively try using Codespaces
lemma chromaticNumber_seven_K₃_free : ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (_ : Fintype H.edgeSet),
 H.CliqueFree 3 ∧ H.chromaticNumber = 7 ∧ Fintype.card W = 95 ∧ Fintype.card H.edgeSet = (by sorry) :=by
  sorry

end Mycielskian
end SimpleGraph
