import LeapsInBounds.Statements.Ramsey

/-!
# R(3, 3) = 6

Sample certificates for both bounds on `R(3, 3)`.
-/

namespace LeapsInBounds.Proofs.Ramsey33

open SimpleGraph

/-- The 5-cycle, which has no triangle and whose complement (another 5-cycle)
has no triangle. -/
def pentagon : SimpleGraph (Fin 5) where
  Adj i j := (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> omega⟩

instance : DecidableRel pentagon.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem lower : Ramsey.LowerBound 3 3 6 :=
  ⟨pentagon, by unfold CliqueFree; decide, by unfold CliqueFree; decide⟩

/-- A vertex with three neighbors gives a triangle in `G` or in `Gᶜ`. -/
lemma triangle_of_three_neighbors {V : Type*} [DecidableEq V] (G : SimpleGraph V) {v a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by
  by_cases h1 : G.Adj a b
  · exact .inl fun hG => hG {v, a, b} (is3Clique_triple_iff.mpr ⟨ha, hb, h1⟩)
  by_cases h2 : G.Adj a c
  · exact .inl fun hG => hG {v, a, c} (is3Clique_triple_iff.mpr ⟨ha, hc, h2⟩)
  by_cases h3 : G.Adj b c
  · exact .inl fun hG => hG {v, b, c} (is3Clique_triple_iff.mpr ⟨hb, hc, h3⟩)
  refine .inr fun hG => hG {a, b, c} (is3Clique_triple_iff.mpr ⟨?_, ?_, ?_⟩)
  · exact (compl_adj G a b).mpr ⟨hab, h1⟩
  · exact (compl_adj G a c).mpr ⟨hac, h2⟩
  · exact (compl_adj G b c).mpr ⟨hbc, h3⟩

/-- Vertex 0 has five other vertices, so it has three neighbors in `G` or in
`Gᶜ`, giving a triangle in one of them. -/
theorem upper : Ramsey.UpperBound 3 3 6 := by
  intro G
  classical
  set others := Finset.univ.erase (0 : Fin 6)
  have hcard := Finset.card_filter_add_card_filter_not (s := others) (G.Adj 0)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  by_cases hN : 2 < (others.filter (G.Adj 0)).card
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hN
    simp only [Finset.mem_filter] at ha hb hc
    exact triangle_of_three_neighbors G ha.2 hb.2 hc.2 hab hac hbc
  · have hM : 2 < (others.filter fun w => ¬G.Adj 0 w).card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hM
    simp only [Finset.mem_filter, others, Finset.mem_erase] at ha hb hc
    have := triangle_of_three_neighbors Gᶜ (v := 0)
      ((compl_adj G _ _).mpr ⟨Ne.symm ha.1.1, ha.2⟩)
      ((compl_adj G _ _).mpr ⟨Ne.symm hb.1.1, hb.2⟩)
      ((compl_adj G _ _).mpr ⟨Ne.symm hc.1.1, hc.2⟩) hab hac hbc
    rw [compl_compl] at this
    exact this.symm

end LeapsInBounds.Proofs.Ramsey33
