module

public import LeapsInBounds.Statements.Cage
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cages of girth 3 and 4

Lower bounds `n(k, 3) ≥ k + 1` and `n(k, 4) ≥ 2k`, which are exact since the
complete graph `K_{k+1}` and the complete bipartite graph `K_{k,k}` attain them.

- Girth 3: each vertex has `k` neighbors other than itself.
- Girth 4: the neighborhoods of two adjacent vertices are disjoint, since a
  common neighbor would form a triangle.
-/

public section

namespace LeapsInBounds.Proofs.CageSmallGirth

open SimpleGraph

variable {m : ℕ} (G : SimpleGraph (Fin m))

lemma ncard_neighborSet [DecidableRel G.Adj] (v : Fin m) :
    (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]

/-- A graph with girth `g` has a cycle, so it has a vertex. -/
lemma pos_of_egirth {g : ℕ} (h : G.egirth = g) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : G.IsAcyclic := fun v => Fin.elim0 v
    rw [← egirth_eq_top] at this
    simp [this] at h
  · exact hm

/-- A triangle in `G` means its girth is at most 3. -/
lemma egirth_le_three {u v w : Fin m} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    G.egirth ≤ 3 := by
  have hc : ¬ G.CliqueFree 3 := fun h => h {u, v, w} (is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩)
  calc G.egirth ≤ (⊤ : SimpleGraph (Fin 3)).egirth :=
        ((not_cliqueFree_iff_top_isContained 3).mp hc).egirth_le
    _ = 3 := egirth_top (by simp)

theorem girth3 (k : ℕ) : Cage.LowerBound k 3 (k + 1) := by
  intro m hm G ⟨hreg, hgirth⟩
  classical
  have hpos := pos_of_egirth G hgirth
  have hdeg := G.degree_lt_card_verts ⟨0, hpos⟩
  rw [← ncard_neighborSet, hreg, Fintype.card_fin] at hdeg
  omega

theorem girth4 (k : ℕ) : Cage.LowerBound k 4 (2 * k) := by
  intro m hm G ⟨hreg, hgirth⟩
  classical
  have hpos := pos_of_egirth G hgirth
  have hdeg (v : Fin m) : G.degree v = k := by rw [← ncard_neighborSet, hreg]
  -- Vertex 0 has a neighbor u, since k > 0 (as m < 2k)
  obtain ⟨u, hu⟩ : ∃ u, G.Adj ⟨0, hpos⟩ u := by
    have : 0 < G.degree ⟨0, hpos⟩ := by rw [hdeg]; omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp this
    exact ⟨u, (mem_neighborFinset _ _ _).mp hu⟩
  have hdisj : Disjoint (G.neighborFinset ⟨0, hpos⟩) (G.neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [mem_neighborFinset] at hw hw'
    have := egirth_le_three G hu hw hw'
    rw [hgirth] at this
    exact absurd this (by decide)
  have := Finset.card_le_univ (G.neighborFinset ⟨0, hpos⟩ ∪ G.neighborFinset u)
  rw [Finset.card_union_of_disjoint hdisj, card_neighborFinset_eq_degree,
    card_neighborFinset_eq_degree, hdeg, hdeg, Fintype.card_fin] at this
  omega

/-! Certificates, one per constant. -/

theorem lower_3_3 : Cage.LowerBound 3 3 4 := girth3 3
theorem lower_4_3 : Cage.LowerBound 4 3 5 := girth3 4
theorem lower_5_3 : Cage.LowerBound 5 3 6 := girth3 5
theorem lower_6_3 : Cage.LowerBound 6 3 7 := girth3 6
theorem lower_7_3 : Cage.LowerBound 7 3 8 := girth3 7
theorem lower_8_3 : Cage.LowerBound 8 3 9 := girth3 8
theorem lower_9_3 : Cage.LowerBound 9 3 10 := girth3 9
theorem lower_10_3 : Cage.LowerBound 10 3 11 := girth3 10
theorem lower_11_3 : Cage.LowerBound 11 3 12 := girth3 11
theorem lower_12_3 : Cage.LowerBound 12 3 13 := girth3 12
theorem lower_13_3 : Cage.LowerBound 13 3 14 := girth3 13
theorem lower_14_3 : Cage.LowerBound 14 3 15 := girth3 14
theorem lower_15_3 : Cage.LowerBound 15 3 16 := girth3 15
theorem lower_16_3 : Cage.LowerBound 16 3 17 := girth3 16
theorem lower_17_3 : Cage.LowerBound 17 3 18 := girth3 17
theorem lower_18_3 : Cage.LowerBound 18 3 19 := girth3 18
theorem lower_19_3 : Cage.LowerBound 19 3 20 := girth3 19
theorem lower_20_3 : Cage.LowerBound 20 3 21 := girth3 20
theorem lower_3_4 : Cage.LowerBound 3 4 6 := girth4 3
theorem lower_4_4 : Cage.LowerBound 4 4 8 := girth4 4
theorem lower_5_4 : Cage.LowerBound 5 4 10 := girth4 5
theorem lower_6_4 : Cage.LowerBound 6 4 12 := girth4 6
theorem lower_7_4 : Cage.LowerBound 7 4 14 := girth4 7
theorem lower_8_4 : Cage.LowerBound 8 4 16 := girth4 8
theorem lower_9_4 : Cage.LowerBound 9 4 18 := girth4 9
theorem lower_10_4 : Cage.LowerBound 10 4 20 := girth4 10
theorem lower_11_4 : Cage.LowerBound 11 4 22 := girth4 11
theorem lower_12_4 : Cage.LowerBound 12 4 24 := girth4 12
theorem lower_13_4 : Cage.LowerBound 13 4 26 := girth4 13
theorem lower_14_4 : Cage.LowerBound 14 4 28 := girth4 14
theorem lower_15_4 : Cage.LowerBound 15 4 30 := girth4 15
theorem lower_16_4 : Cage.LowerBound 16 4 32 := girth4 16
theorem lower_17_4 : Cage.LowerBound 17 4 34 := girth4 17
theorem lower_18_4 : Cage.LowerBound 18 4 36 := girth4 18
theorem lower_19_4 : Cage.LowerBound 19 4 38 := girth4 19
theorem lower_20_4 : Cage.LowerBound 20 4 40 := girth4 20

end LeapsInBounds.Proofs.CageSmallGirth
