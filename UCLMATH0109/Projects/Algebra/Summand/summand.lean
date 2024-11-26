import Mathlib

/--
`Summand G H` means that `G` is a direct summand of `H`,
i.e. there exists a group `G'` and an isomorphism `G × G' ≃* H`.
-/
inductive Summand (G H : Type) [Group G] [Group H] : Prop where
  | of (G' : Type) [Group G'] (_ : G × G' ≃* H) : Summand G H

/--
`G ∣⊕ H` means that `G` is a direct summand of `H`.
-/
infix:50  " ∣⊕ " => Summand

variable (G H H' K : Type) [Group G] [Group H] [Group H'] [Group K]

lemma summand_defn : G ∣⊕ H ↔ ∃ G' : Type, ∃ _ : Group G', Nonempty (G × G' ≃* H) :=
by
  sorry

lemma unit_summand : Unit ∣⊕ G :=
by
  sorry

lemma summand_unit_iff : G ∣⊕ Unit ↔ Nonempty (G ≃* Unit) :=
by
  sorry

lemma summand_refl [Group G] : G ∣⊕ G :=
by
  sorry

lemma Summans_trans [Group G] [Group H] [Group K] (h : G ∣⊕ H) (h' : H ∣⊕ K) : G ∣⊕ K :=
by
  sorry

lemma Summand_of_equiv [Group G] [Group H] [Group G'] [Group H'] (φG : G ≃* G') (φH : H ≃ H') :
    G ∣⊕ H ↔ G' ∣⊕ H' :=
by
  sorry

lemma card_dvd_of_summand (h : G ∣⊕ H) : Nat.card G ∣ Nat.card H := by
  sorry

lemma summmand_antisymm_of_finite [Group G] [Group H] [Finite G] [Finite H] (h : G ∣⊕ H) (h' : H ∣⊕ G) : Nonempty (G ≃* H) :=
by
  sorry

lemma summand_iff : G ∣⊕ H ↔ ∃ φ : G →* H, ∃ ψ : H →* G, ψ.comp φ = MonoidHom.id G ∧ φ.range.Normal :=
by
  sorry

lemma summand_prod_of_finite_of_simple [Group G] [Group H] [Group H'] [Finite G] [IsSimpleGroup G] (h : G ∣⊕ (H × H')) :
    G ∣⊕ H ∨ G ∣⊕ H' :=
by
  sorry
