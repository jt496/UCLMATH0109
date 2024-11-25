import Mathlib

/-
# This project is on coloring graphs with the greedy algorithm
# See the pdf for details.
-/
section greedy
namespace SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin (n + 1))}

/-
Any finite graph with maximum degree at most Δ has a Δ + 1 coloring.

We will take our graphs to have vertex set Fin (n + 1) which is essentially {0,1,..,n}

You will need to use SimpleGraph ,Finset and Fin results.
-/
-- Facts about `SimpleGraph` and colorings
#check Colorable
#check Coloring
#check maxDegree
#check neighborFinset
#check mem_neighborFinset
#check card_neighborFinset_eq_degree
#check degree_le_maxDegree
#check Colorable.chromaticNumber_le

-- Facts about `Finset`
#check Finset.card_image_le
#check Finset.mem_compl
#check Finset.min'_mem
#check Finset.mem_image
#check Finset.card_compl_lt_iff_nonempty

-- Facts about `Fin`
#check Fintype.card_fin
#check Fin.le_last
#check Fin.castSucc
#check Fin.val_succ
#check Fin.coe_castSucc
#check Fin.coe_eq_castSucc
#check Fin.coeSucc_eq_succ


@[ext]
structure PartialColoring (i : Fin (n + 1)) (β : Type*)  where
col : Fin (n + 1) → β
valid : ∀ ⦃v w⦄, v ≤ i → w ≤ i → G.Adj v w → col v ≠ col w

namespace PartialColoring

def copy {i j : Fin (n + 1)} (c: G.PartialColoring i β) (hij : i = j)  : G.PartialColoring j β :=
  hij ▸ c

/-- Convert a Partial coloring up to n into a proper coloring  -/
def toColoring (c : G.PartialColoring (Fin.last n) β ) : G.Coloring β := by
  sorry

/-- Given a partial colouring up to i and a colour b not used in the nbhd of i.succ
extend the coloring up to i.succ -/
def extend  (c : G.PartialColoring i β)  (hvb : ∀ ⦃x⦄, x ≤ i → G.Adj i.succ x → c.col x ≠ b) :
G.PartialColoring i.succ β := by
  sorry




end PartialColoring
open PartialColoring

/-- A constructive greedy Δ + 1 coloring given max degree ≤ Δ -/
def greedy (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hmax: G.maxDegree ≤ Δ ) : G.Coloring (Fin (Δ + 1)):= by
  let c : ∀ i, (G.PartialColoring i (Fin (Δ + 1))) :=by
    apply Fin.induction
    · sorry
    · sorry
  sorry


theorem chromaticNumber_le_maxDegree_add_one (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hmax: G.maxDegree ≤ Δ ) :
G.chromaticNumber ≤ Δ + 1 := by
  sorry



/-
Extension (1): define K₅,₅ with a matching removed.
If vertices are ordered `0,1,2,3,..,9` the greedy coloring uses 2 colors
If ordered `0,5,1,6,2,7,3,8,4,9` then it uses 5 colors (which is the worst possible
since this graph has maximum degree 4).
-/
-- You can use the following line to help construct your graph
#check SimpleGraph.fromRel
-- If you want to describe a permutation of Fin 10 then you can use cycle notation
-- as follows
#check (c[1,2,5]*c[6,7] : Fin 10 ≃ Fin 10)
-- Given a `G : SimpleGraph (Fin 10)` and  `e : Fin 10 ≃ Fin 10` you can define the
-- graph given by permuting the vertices as `G.map e.toEmbedding`
-- Once you have defined everything you can use `#eval` to see the greedy coloring
-- used for any given graph.
end SimpleGraph
end greedy

section DeBruijnErdos
/-
Extension (2): Prove the De Bruijn-Erdos theorm.
Any graph H is k-colorable iff all its finite induced subgraphs are k-colorable
This follows by a compactness argument (i.e. Tychonoff's theorem) see pdf for details.
-/
namespace SimpleGraph
open Classical

variable {α : Type u} (H : SimpleGraph α) {f : α → Fin k}

-- The following instance is not required since it would be produced automatically.
-- It shows that Lean knows that the space `α → Fin k` is compact.
instance : CompactSpace (α → Fin k) :=inferInstance

/--
The set of k-colorings of α that are valid k-colorings of `H.induce A` -/
abbrev valid (A : Set α) (k : ℕ) : Set (α → Fin k):=
  { f | ∀ ⦃a b⦄, a ∈ A → b ∈ A → H.Adj a b → f a ≠ f b}

/--
There is a (k+1)-coloring of H that is valid on A iff `H.induce A` is
(k+1)-colorable -/
lemma valid_nonempty_iff (A : Set α) :
(H.valid A (k + 1)).Nonempty  ↔ (H.induce A).Colorable (k + 1):=by
  sorry


lemma valid_FIP (ℱ : Finset (Finset α)) (hf : ∀ (A : Finset α), (H.valid A k).Nonempty) :
 (⋂ A ∈ ℱ, (H.valid A k)).Nonempty := by
  sorry

#check isOpen_compl_iff
#check isOpen_pi_iff

lemma valid_finset_isClosed (k : ℕ) (A : Finset α):  IsClosed (H.valid A k):=by
  sorry

#check IsCompact.inter_iInter_nonempty

theorem DeBruijnErdos (k : ℕ) :
    H.Colorable k ↔ ∀ A : Finset α, (H.induce A).Colorable k := by
  sorry


/-
We can now put this together with the greedy coloring to get a (Δ + 1)-coloring of
any graph with all degrees at most Δ (you can't use maxDegree here since
the vertex set may not be finite so maxDegree may not be defined)
-/

variable  [∀ a : α, Fintype (H.neighborSet a)]

theorem infinite_greedy_bound (hdeg: ∀ a : α, H.degree a ≤ Δ) : H.Colorable (Δ + 1):=by
  sorry


end SimpleGraph
end DeBruijnErdos
