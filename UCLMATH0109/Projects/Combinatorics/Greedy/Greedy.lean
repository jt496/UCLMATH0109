import Mathlib

/-
Any finite graph with maximum degree at most Δ has a Δ + 1 coloring.

We will take our graphs to have vertex set Fin (n + 1) which is {0,1,..,n}
-/
open Finset Fin
namespace SimpleGraph
section greedy
-- We work with a graph G on vertex set {0, 1, ..., n} and maximum degree Δ
variable {n Δ : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hmax: G.maxDegree ≤ Δ )


@[ext]
structure PartialColoring (i : Fin (n + 1)) (β : Type*)  where
col : Fin (n + 1) → β
valid : ∀ ⦃v w⦄, v ≤ i → w ≤ i → G.Adj v w → col v ≠ col w

namespace PartialColoring

/-- Convert a Partial coloring up to n into a proper coloring  -/
def toColoring (c : G.PartialColoring (last n) β) : G.Coloring β :=
  sorry

/-- Given a partial colouring up to i and a colour b not used in the nbhd of i + 1
extend the coloring up to i + 1 -/
def extend  (c : G.PartialColoring i β)  (hvb : ∀ ⦃x⦄, x ≤ i → G.Adj (i + 1) x → c.col x ≠ b) :
    G.PartialColoring (i + 1) β := by
  sorry

end PartialColoring

/-- A greedy Δ + 1 partial coloring given max degree ≤ Δ -/
def greedy' : (i : Fin (n + 1)) → G.PartialColoring i (Fin (Δ + 1)):= by
  apply induction
  · sorry
  · sorry

/-- A greedy Δ + 1 coloring given max degree ≤ Δ -/
def greedy : G.Coloring (Fin (Δ + 1)):=
  sorry
theorem chromaticNumber_le_maxDegree_add_one : G.chromaticNumber ≤ Δ + 1 := by
  sorry

end greedy

/-
Extension (1): consider a graph `G : SimpleGraph ℕ` and define `G.degLT n` to be the number of neighbours of
`n` in `G` that precede `n` (in the order on ℕ).  Prove that if `∀ n, G.degLT n ≤ Δ` then `G` is `Δ + 1` colorable.

-/



section DeBruijnErdos
/-
Extension (2):
Any graph H is k-colorable iff all its finite induced subgraphs are k-colorable
-/
open Classical
variable {α : Type u} (H : SimpleGraph α)

@[reducible]
def valid (A : Set α) (k : ℕ) : Set (α → Fin k):=
  { f | ∀ ⦃a b⦄, a ∈ A → b ∈ A → H.Adj a b → f a ≠ f b}

theorem DeBruijnErdos (k : ℕ) :
    H.Colorable k ↔ ∀ A : Finset α, (H.induce A).Colorable k := by
  sorry


-- We can now put this together to get a (Δ + 1)-coloring of any graph with all
-- degrees at most Δ (you can't use maxDegree here since the vertex set may not be
-- finite so maxDegree is not defined in this case.)
#check equivFin
variable  [∀ a: α, Fintype (H.neighborSet a)]

theorem colorable_of_for_all_degree_le (hdeg: ∀ a : α, H.degree a ≤ Δ) : H.Colorable (Δ + 1):=by
  sorry

end DeBruijnErdos
end SimpleGraph
