module

public import LeapsInBounds.Statements.Ramsey
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Upper bounds on Ramsey numbers from the Erdős–Szekeres recurrence

`R(r, s) ≤ R(r - 1, s) + R(r, s - 1)`: in a graph on that many vertices, pick a
vertex `v`. Among the others, either at least `R(r - 1, s)` are neighbors of
`v`, giving an `(r - 1)`-clique (which `v` extends to an `r`-clique) or an
independent `s`-set, or at least `R(r, s - 1)` are non-neighbors, giving an
`r`-clique or an independent `(s - 1)`-set (which `v` extends).

If both terms are even, one vertex fewer suffices: otherwise every vertex has
exactly `R(r - 1, s) - 1` neighbors, an odd number, on an odd number of
vertices, so the degree sum is odd.

Starting from `R(1, s) = R(r, 1) = 1`, this gives a bound for each `r, s ≤ 15`.
-/

public section

namespace LeapsInBounds.Proofs.RamseyRecurrence

open SimpleGraph Finset

/-- `R(r, s) ≤ n`, for vertex subsets of any finite graph: every `n` vertices of
a graph contain an `r`-clique or an independent set of size `s`. -/
def P (r s n : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V), n ≤ #S →
    (∃ t ⊆ S, G.IsNClique r t) ∨ (∃ t ⊆ S, Gᶜ.IsNClique s t)

theorem P.symm {r s n : ℕ} (h : P r s n) : P s r n := by
  intro V _ _ G S hS
  rcases h Gᶜ S hS with h | h
  · exact .inr h
  · rw [compl_compl] at h
    exact .inl h

theorem one_left {s : ℕ} : P 1 s 1 := by
  intro V _ _ G S hS
  obtain ⟨v, hv⟩ := (card_pos (s := S)).1 (by omega)
  exact .inl ⟨{v}, by simpa using hv, isNClique_singleton.2 rfl⟩

theorem one_right {r : ℕ} : P r 1 1 := one_left.symm

/-- The recurrence at one vertex `v`: enough neighbors or enough non-neighbors
of `v` in `S` give a clique or an independent set. -/
lemma of_vertex {V : Type} [Fintype V] [DecidableEq V] {r s a b : ℕ} (ha : P r (s + 1) a)
    (hb : P (r + 1) s b) (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {v : V}
    (hv : v ∈ S)
    (h : a ≤ #((S.erase v).filter (G.Adj v)) ∨ b ≤ #((S.erase v).filter fun w => ¬G.Adj v w)) :
    (∃ t ⊆ S, G.IsNClique (r + 1) t) ∨ (∃ t ⊆ S, Gᶜ.IsNClique (s + 1) t) := by
  have hsub {p : V → Prop} [DecidablePred p] : (S.erase v).filter p ⊆ S :=
    filter_subset _ _ |>.trans (erase_subset _ _)
  rcases h with h | h
  · rcases ha G _ h with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · refine .inl ⟨insert v t, insert_subset hv (ht.trans hsub), hc.insert fun w hw => ?_⟩
      exact (mem_filter.1 (ht hw)).2
    · exact .inr ⟨t, ht.trans hsub, hc⟩
  · rcases hb G _ h with ⟨t, ht, hc⟩ | ⟨t, ht, hc⟩
    · exact .inl ⟨t, ht.trans hsub, hc⟩
    · refine .inr ⟨insert v t, insert_subset hv (ht.trans hsub), hc.insert fun w hw => ?_⟩
      have hw' := mem_filter.1 (ht hw)
      exact (compl_adj G v w).2 ⟨(ne_of_mem_erase hw'.1).symm, hw'.2⟩

/-- `R(r + 1, s + 1) ≤ R(r, s + 1) + R(r + 1, s)`. -/
theorem step {r s a b n : ℕ} (ha : P r (s + 1) a) (hb : P (r + 1) s b) (hn : a + b ≤ n)
    (h1 : 1 ≤ n) : P (r + 1) (s + 1) n := by
  intro V _ _ G S hS
  classical
  obtain ⟨v, hv⟩ := (card_pos (s := S)).1 (by omega)
  apply of_vertex ha hb G S hv
  have := card_filter_add_card_filter_not (s := S.erase v) (G.Adj v)
  rw [card_erase_of_mem hv] at this
  omega

/-- The graph `G` restricted to the vertices `S`. -/
def restrict {V : Type} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v ∈ S ∧ w ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

lemma restrict_adj {V : Type} {G : SimpleGraph V} {S : Finset V} {v w : V} :
    (restrict G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S := Iff.rfl

/-- `R(r + 1, s + 1) ≤ R(r, s + 1) + R(r + 1, s) - 1` when both terms are even. -/
theorem step_even {r s a b n : ℕ} (ha : P r (s + 1) a) (hb : P (r + 1) s b) (hae : a % 2 = 0)
    (hbe : b % 2 = 0) (hn : a + b ≤ n + 1) (h1 : 1 ≤ n) : P (r + 1) (s + 1) n := by
  intro V _ _ G S hS
  classical
  by_contra hcon
  have key : ∀ v ∈ S, #((S.erase v).filter (G.Adj v)) = a - 1 ∧ #S = a + b - 1 := by
    intro v hv
    have h := card_filter_add_card_filter_not (s := S.erase v) (G.Adj v)
    rw [card_erase_of_mem hv] at h
    by_cases h' : a ≤ #((S.erase v).filter (G.Adj v)) ∨
        b ≤ #((S.erase v).filter fun w => ¬G.Adj v w)
    · exact absurd (of_vertex ha hb G S hv h') hcon
    · omega
  obtain ⟨v₀, hv₀⟩ := (card_pos (s := S)).1 (by omega)
  have hS' := (key v₀ hv₀).2
  have ha1 : 1 ≤ a := by
    have := card_filter_add_card_filter_not (s := S.erase v₀) (G.Adj v₀)
    rw [card_erase_of_mem hv₀] at this
    by_contra h0
    exact hcon (of_vertex ha hb G S hv₀ (.inl (by omega)))
  have hdeg : ∀ v, (restrict G S).degree v = if v ∈ S then a - 1 else 0 := by
    intro v
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter (G := restrict G S)]
    split_ifs with hv
    · rw [← (key v hv).1]
      congr 1
      ext w
      rw [mem_filter, mem_filter, mem_erase, restrict_adj]
      simp only [mem_univ, true_and]
      constructor
      · rintro ⟨h, -, hw⟩
        exact ⟨⟨(G.ne_of_adj h).symm, hw⟩, h⟩
      · rintro ⟨⟨-, hw⟩, h⟩
        exact ⟨h, hv, hw⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      exact fun w _ h => hv (restrict_adj.1 h).2.1
  have hsum := (restrict G S).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hsum
  rw [sum_ite_mem, univ_inter, sum_const, smul_eq_mul] at hsum
  have heven : Even (#S * (a - 1)) := ⟨#(restrict G S).edgeFinset, by omega⟩
  rcases Nat.even_mul.1 heven with ⟨k, hk⟩ | ⟨k, hk⟩ <;> omega

theorem toUpper {r s n : ℕ} (h : P r s n) : Ramsey.UpperBound r s n := by
  intro G
  classical
  rcases h G univ (by simp) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  · exact .inl fun hf => hf t ht
  · exact .inr fun hf => hf t ht

theorem p_2_2 : P 2 2 2 :=
  step (r := 1) (s := 1) one_left one_right (by decide) (by decide)
theorem p_2_3 : P 2 3 3 :=
  step (r := 1) (s := 2) one_left p_2_2 (by decide) (by decide)
theorem p_2_4 : P 2 4 4 :=
  step (r := 1) (s := 3) one_left p_2_3 (by decide) (by decide)
theorem p_2_5 : P 2 5 5 :=
  step (r := 1) (s := 4) one_left p_2_4 (by decide) (by decide)
theorem p_2_6 : P 2 6 6 :=
  step (r := 1) (s := 5) one_left p_2_5 (by decide) (by decide)
theorem p_2_7 : P 2 7 7 :=
  step (r := 1) (s := 6) one_left p_2_6 (by decide) (by decide)
theorem p_2_8 : P 2 8 8 :=
  step (r := 1) (s := 7) one_left p_2_7 (by decide) (by decide)
theorem p_2_9 : P 2 9 9 :=
  step (r := 1) (s := 8) one_left p_2_8 (by decide) (by decide)
theorem p_2_10 : P 2 10 10 :=
  step (r := 1) (s := 9) one_left p_2_9 (by decide) (by decide)
theorem p_2_11 : P 2 11 11 :=
  step (r := 1) (s := 10) one_left p_2_10 (by decide) (by decide)
theorem p_2_12 : P 2 12 12 :=
  step (r := 1) (s := 11) one_left p_2_11 (by decide) (by decide)
theorem p_2_13 : P 2 13 13 :=
  step (r := 1) (s := 12) one_left p_2_12 (by decide) (by decide)
theorem p_2_14 : P 2 14 14 :=
  step (r := 1) (s := 13) one_left p_2_13 (by decide) (by decide)
theorem p_2_15 : P 2 15 15 :=
  step (r := 1) (s := 14) one_left p_2_14 (by decide) (by decide)
theorem p_3_3 : P 3 3 6 :=
  step (r := 2) (s := 2) p_2_3 p_2_3.symm (by decide) (by decide)
theorem p_3_4 : P 3 4 9 :=
  step_even (r := 2) (s := 3) p_2_4 p_3_3 rfl rfl (by decide) (by decide)
theorem p_3_5 : P 3 5 14 :=
  step (r := 2) (s := 4) p_2_5 p_3_4 (by decide) (by decide)
theorem p_3_6 : P 3 6 19 :=
  step_even (r := 2) (s := 5) p_2_6 p_3_5 rfl rfl (by decide) (by decide)
theorem p_3_7 : P 3 7 26 :=
  step (r := 2) (s := 6) p_2_7 p_3_6 (by decide) (by decide)
theorem p_3_8 : P 3 8 33 :=
  step_even (r := 2) (s := 7) p_2_8 p_3_7 rfl rfl (by decide) (by decide)
theorem p_3_9 : P 3 9 42 :=
  step (r := 2) (s := 8) p_2_9 p_3_8 (by decide) (by decide)
theorem p_3_10 : P 3 10 51 :=
  step_even (r := 2) (s := 9) p_2_10 p_3_9 rfl rfl (by decide) (by decide)
theorem p_3_11 : P 3 11 62 :=
  step (r := 2) (s := 10) p_2_11 p_3_10 (by decide) (by decide)
theorem p_3_12 : P 3 12 73 :=
  step_even (r := 2) (s := 11) p_2_12 p_3_11 rfl rfl (by decide) (by decide)
theorem p_3_13 : P 3 13 86 :=
  step (r := 2) (s := 12) p_2_13 p_3_12 (by decide) (by decide)
theorem p_3_14 : P 3 14 99 :=
  step_even (r := 2) (s := 13) p_2_14 p_3_13 rfl rfl (by decide) (by decide)
theorem p_3_15 : P 3 15 114 :=
  step (r := 2) (s := 14) p_2_15 p_3_14 (by decide) (by decide)
theorem p_4_4 : P 4 4 18 :=
  step (r := 3) (s := 3) p_3_4 p_3_4.symm (by decide) (by decide)
theorem p_4_5 : P 4 5 31 :=
  step_even (r := 3) (s := 4) p_3_5 p_4_4 rfl rfl (by decide) (by decide)
theorem p_4_6 : P 4 6 50 :=
  step (r := 3) (s := 5) p_3_6 p_4_5 (by decide) (by decide)
theorem p_4_7 : P 4 7 75 :=
  step_even (r := 3) (s := 6) p_3_7 p_4_6 rfl rfl (by decide) (by decide)
theorem p_4_8 : P 4 8 108 :=
  step (r := 3) (s := 7) p_3_8 p_4_7 (by decide) (by decide)
theorem p_4_9 : P 4 9 149 :=
  step_even (r := 3) (s := 8) p_3_9 p_4_8 rfl rfl (by decide) (by decide)
theorem p_4_10 : P 4 10 200 :=
  step (r := 3) (s := 9) p_3_10 p_4_9 (by decide) (by decide)
theorem p_4_11 : P 4 11 261 :=
  step_even (r := 3) (s := 10) p_3_11 p_4_10 rfl rfl (by decide) (by decide)
theorem p_4_12 : P 4 12 334 :=
  step (r := 3) (s := 11) p_3_12 p_4_11 (by decide) (by decide)
theorem p_4_13 : P 4 13 419 :=
  step_even (r := 3) (s := 12) p_3_13 p_4_12 rfl rfl (by decide) (by decide)
theorem p_4_14 : P 4 14 518 :=
  step (r := 3) (s := 13) p_3_14 p_4_13 (by decide) (by decide)
theorem p_4_15 : P 4 15 631 :=
  step_even (r := 3) (s := 14) p_3_15 p_4_14 rfl rfl (by decide) (by decide)
theorem p_5_5 : P 5 5 62 :=
  step (r := 4) (s := 4) p_4_5 p_4_5.symm (by decide) (by decide)
theorem p_5_6 : P 5 6 111 :=
  step_even (r := 4) (s := 5) p_4_6 p_5_5 rfl rfl (by decide) (by decide)
theorem p_5_7 : P 5 7 186 :=
  step (r := 4) (s := 6) p_4_7 p_5_6 (by decide) (by decide)
theorem p_5_8 : P 5 8 293 :=
  step_even (r := 4) (s := 7) p_4_8 p_5_7 rfl rfl (by decide) (by decide)
theorem p_5_9 : P 5 9 442 :=
  step (r := 4) (s := 8) p_4_9 p_5_8 (by decide) (by decide)
theorem p_5_10 : P 5 10 641 :=
  step_even (r := 4) (s := 9) p_4_10 p_5_9 rfl rfl (by decide) (by decide)
theorem p_5_11 : P 5 11 902 :=
  step (r := 4) (s := 10) p_4_11 p_5_10 (by decide) (by decide)
theorem p_5_12 : P 5 12 1235 :=
  step_even (r := 4) (s := 11) p_4_12 p_5_11 rfl rfl (by decide) (by decide)
theorem p_5_13 : P 5 13 1654 :=
  step (r := 4) (s := 12) p_4_13 p_5_12 (by decide) (by decide)
theorem p_5_14 : P 5 14 2171 :=
  step_even (r := 4) (s := 13) p_4_14 p_5_13 rfl rfl (by decide) (by decide)
theorem p_5_15 : P 5 15 2802 :=
  step (r := 4) (s := 14) p_4_15 p_5_14 (by decide) (by decide)
theorem p_6_6 : P 6 6 222 :=
  step (r := 5) (s := 5) p_5_6 p_5_6.symm (by decide) (by decide)
theorem p_6_7 : P 6 7 407 :=
  step_even (r := 5) (s := 6) p_5_7 p_6_6 rfl rfl (by decide) (by decide)
theorem p_6_8 : P 6 8 700 :=
  step (r := 5) (s := 7) p_5_8 p_6_7 (by decide) (by decide)
theorem p_6_9 : P 6 9 1141 :=
  step_even (r := 5) (s := 8) p_5_9 p_6_8 rfl rfl (by decide) (by decide)
theorem p_6_10 : P 6 10 1782 :=
  step (r := 5) (s := 9) p_5_10 p_6_9 (by decide) (by decide)
theorem p_6_11 : P 6 11 2683 :=
  step_even (r := 5) (s := 10) p_5_11 p_6_10 rfl rfl (by decide) (by decide)
theorem p_6_12 : P 6 12 3918 :=
  step (r := 5) (s := 11) p_5_12 p_6_11 (by decide) (by decide)
theorem p_6_13 : P 6 13 5571 :=
  step_even (r := 5) (s := 12) p_5_13 p_6_12 rfl rfl (by decide) (by decide)
theorem p_6_14 : P 6 14 7742 :=
  step (r := 5) (s := 13) p_5_14 p_6_13 (by decide) (by decide)
theorem p_6_15 : P 6 15 10543 :=
  step_even (r := 5) (s := 14) p_5_15 p_6_14 rfl rfl (by decide) (by decide)
theorem p_7_7 : P 7 7 814 :=
  step (r := 6) (s := 6) p_6_7 p_6_7.symm (by decide) (by decide)
theorem p_7_8 : P 7 8 1513 :=
  step_even (r := 6) (s := 7) p_6_8 p_7_7 rfl rfl (by decide) (by decide)
theorem p_7_9 : P 7 9 2654 :=
  step (r := 6) (s := 8) p_6_9 p_7_8 (by decide) (by decide)
theorem p_7_10 : P 7 10 4435 :=
  step_even (r := 6) (s := 9) p_6_10 p_7_9 rfl rfl (by decide) (by decide)
theorem p_7_11 : P 7 11 7118 :=
  step (r := 6) (s := 10) p_6_11 p_7_10 (by decide) (by decide)
theorem p_7_12 : P 7 12 11035 :=
  step_even (r := 6) (s := 11) p_6_12 p_7_11 rfl rfl (by decide) (by decide)
theorem p_7_13 : P 7 13 16606 :=
  step (r := 6) (s := 12) p_6_13 p_7_12 (by decide) (by decide)
theorem p_7_14 : P 7 14 24347 :=
  step_even (r := 6) (s := 13) p_6_14 p_7_13 rfl rfl (by decide) (by decide)
theorem p_7_15 : P 7 15 34890 :=
  step (r := 6) (s := 14) p_6_15 p_7_14 (by decide) (by decide)
theorem p_8_8 : P 8 8 3026 :=
  step (r := 7) (s := 7) p_7_8 p_7_8.symm (by decide) (by decide)
theorem p_8_9 : P 8 9 5679 :=
  step_even (r := 7) (s := 8) p_7_9 p_8_8 rfl rfl (by decide) (by decide)
theorem p_8_10 : P 8 10 10114 :=
  step (r := 7) (s := 9) p_7_10 p_8_9 (by decide) (by decide)
theorem p_8_11 : P 8 11 17231 :=
  step_even (r := 7) (s := 10) p_7_11 p_8_10 rfl rfl (by decide) (by decide)
theorem p_8_12 : P 8 12 28266 :=
  step (r := 7) (s := 11) p_7_12 p_8_11 (by decide) (by decide)
theorem p_8_13 : P 8 13 44871 :=
  step_even (r := 7) (s := 12) p_7_13 p_8_12 rfl rfl (by decide) (by decide)
theorem p_8_14 : P 8 14 69218 :=
  step (r := 7) (s := 13) p_7_14 p_8_13 (by decide) (by decide)
theorem p_8_15 : P 8 15 104107 :=
  step_even (r := 7) (s := 14) p_7_15 p_8_14 rfl rfl (by decide) (by decide)
theorem p_9_9 : P 9 9 11358 :=
  step (r := 8) (s := 8) p_8_9 p_8_9.symm (by decide) (by decide)
theorem p_9_10 : P 9 10 21471 :=
  step_even (r := 8) (s := 9) p_8_10 p_9_9 rfl rfl (by decide) (by decide)
theorem p_9_11 : P 9 11 38702 :=
  step (r := 8) (s := 10) p_8_11 p_9_10 (by decide) (by decide)
theorem p_9_12 : P 9 12 66967 :=
  step_even (r := 8) (s := 11) p_8_12 p_9_11 rfl rfl (by decide) (by decide)
theorem p_9_13 : P 9 13 111838 :=
  step (r := 8) (s := 12) p_8_13 p_9_12 (by decide) (by decide)
theorem p_9_14 : P 9 14 181055 :=
  step_even (r := 8) (s := 13) p_8_14 p_9_13 rfl rfl (by decide) (by decide)
theorem p_9_15 : P 9 15 285162 :=
  step (r := 8) (s := 14) p_8_15 p_9_14 (by decide) (by decide)
theorem p_10_10 : P 10 10 42942 :=
  step (r := 9) (s := 9) p_9_10 p_9_10.symm (by decide) (by decide)
theorem p_10_11 : P 10 11 81643 :=
  step_even (r := 9) (s := 10) p_9_11 p_10_10 rfl rfl (by decide) (by decide)
theorem p_10_12 : P 10 12 148610 :=
  step (r := 9) (s := 11) p_9_12 p_10_11 (by decide) (by decide)
theorem p_10_13 : P 10 13 260447 :=
  step_even (r := 9) (s := 12) p_9_13 p_10_12 rfl rfl (by decide) (by decide)
theorem p_10_14 : P 10 14 441502 :=
  step (r := 9) (s := 13) p_9_14 p_10_13 (by decide) (by decide)
theorem p_10_15 : P 10 15 726663 :=
  step_even (r := 9) (s := 14) p_9_15 p_10_14 rfl rfl (by decide) (by decide)
theorem p_11_11 : P 11 11 163286 :=
  step (r := 10) (s := 10) p_10_11 p_10_11.symm (by decide) (by decide)
theorem p_11_12 : P 11 12 311895 :=
  step_even (r := 10) (s := 11) p_10_12 p_11_11 rfl rfl (by decide) (by decide)
theorem p_11_13 : P 11 13 572342 :=
  step (r := 10) (s := 12) p_10_13 p_11_12 (by decide) (by decide)
theorem p_11_14 : P 11 14 1013843 :=
  step_even (r := 10) (s := 13) p_10_14 p_11_13 rfl rfl (by decide) (by decide)
theorem p_11_15 : P 11 15 1740506 :=
  step (r := 10) (s := 14) p_10_15 p_11_14 (by decide) (by decide)
theorem p_12_12 : P 12 12 623790 :=
  step (r := 11) (s := 11) p_11_12 p_11_12.symm (by decide) (by decide)
theorem p_12_13 : P 12 13 1196131 :=
  step_even (r := 11) (s := 12) p_11_13 p_12_12 rfl rfl (by decide) (by decide)
theorem p_12_14 : P 12 14 2209974 :=
  step (r := 11) (s := 13) p_11_14 p_12_13 (by decide) (by decide)
theorem p_12_15 : P 12 15 3950479 :=
  step_even (r := 11) (s := 14) p_11_15 p_12_14 rfl rfl (by decide) (by decide)
theorem p_13_13 : P 13 13 2392262 :=
  step (r := 12) (s := 12) p_12_13 p_12_13.symm (by decide) (by decide)
theorem p_13_14 : P 13 14 4602235 :=
  step_even (r := 12) (s := 13) p_12_14 p_13_13 rfl rfl (by decide) (by decide)
theorem p_13_15 : P 13 15 8552714 :=
  step (r := 12) (s := 14) p_12_15 p_13_14 (by decide) (by decide)
theorem p_14_14 : P 14 14 9204470 :=
  step (r := 13) (s := 13) p_13_14 p_13_14.symm (by decide) (by decide)
theorem p_14_15 : P 14 15 17757183 :=
  step_even (r := 13) (s := 14) p_13_15 p_14_14 rfl rfl (by decide) (by decide)
theorem p_15_15 : P 15 15 35514366 :=
  step (r := 14) (s := 14) p_14_15 p_14_15.symm (by decide) (by decide)

theorem upper_3_4 : Ramsey.UpperBound 3 4 9 := toUpper p_3_4
theorem upper_3_5 : Ramsey.UpperBound 3 5 14 := toUpper p_3_5
theorem upper_3_6 : Ramsey.UpperBound 3 6 19 := toUpper p_3_6
theorem upper_3_7 : Ramsey.UpperBound 3 7 26 := toUpper p_3_7
theorem upper_3_8 : Ramsey.UpperBound 3 8 33 := toUpper p_3_8
theorem upper_3_9 : Ramsey.UpperBound 3 9 42 := toUpper p_3_9
theorem upper_3_10 : Ramsey.UpperBound 3 10 51 := toUpper p_3_10
theorem upper_3_11 : Ramsey.UpperBound 3 11 62 := toUpper p_3_11
theorem upper_3_12 : Ramsey.UpperBound 3 12 73 := toUpper p_3_12
theorem upper_3_13 : Ramsey.UpperBound 3 13 86 := toUpper p_3_13
theorem upper_3_14 : Ramsey.UpperBound 3 14 99 := toUpper p_3_14
theorem upper_3_15 : Ramsey.UpperBound 3 15 114 := toUpper p_3_15
theorem upper_4_4 : Ramsey.UpperBound 4 4 18 := toUpper p_4_4
theorem upper_4_5 : Ramsey.UpperBound 4 5 31 := toUpper p_4_5
theorem upper_4_6 : Ramsey.UpperBound 4 6 50 := toUpper p_4_6
theorem upper_4_7 : Ramsey.UpperBound 4 7 75 := toUpper p_4_7
theorem upper_4_8 : Ramsey.UpperBound 4 8 108 := toUpper p_4_8
theorem upper_4_9 : Ramsey.UpperBound 4 9 149 := toUpper p_4_9
theorem upper_4_10 : Ramsey.UpperBound 4 10 200 := toUpper p_4_10
theorem upper_4_11 : Ramsey.UpperBound 4 11 261 := toUpper p_4_11
theorem upper_4_12 : Ramsey.UpperBound 4 12 334 := toUpper p_4_12
theorem upper_4_13 : Ramsey.UpperBound 4 13 419 := toUpper p_4_13
theorem upper_4_14 : Ramsey.UpperBound 4 14 518 := toUpper p_4_14
theorem upper_4_15 : Ramsey.UpperBound 4 15 631 := toUpper p_4_15
theorem upper_5_5 : Ramsey.UpperBound 5 5 62 := toUpper p_5_5
theorem upper_5_6 : Ramsey.UpperBound 5 6 111 := toUpper p_5_6
theorem upper_5_7 : Ramsey.UpperBound 5 7 186 := toUpper p_5_7
theorem upper_5_8 : Ramsey.UpperBound 5 8 293 := toUpper p_5_8
theorem upper_5_9 : Ramsey.UpperBound 5 9 442 := toUpper p_5_9
theorem upper_5_10 : Ramsey.UpperBound 5 10 641 := toUpper p_5_10
theorem upper_5_11 : Ramsey.UpperBound 5 11 902 := toUpper p_5_11
theorem upper_5_12 : Ramsey.UpperBound 5 12 1235 := toUpper p_5_12
theorem upper_5_13 : Ramsey.UpperBound 5 13 1654 := toUpper p_5_13
theorem upper_5_14 : Ramsey.UpperBound 5 14 2171 := toUpper p_5_14
theorem upper_5_15 : Ramsey.UpperBound 5 15 2802 := toUpper p_5_15
theorem upper_6_6 : Ramsey.UpperBound 6 6 222 := toUpper p_6_6
theorem upper_6_7 : Ramsey.UpperBound 6 7 407 := toUpper p_6_7
theorem upper_6_8 : Ramsey.UpperBound 6 8 700 := toUpper p_6_8
theorem upper_6_9 : Ramsey.UpperBound 6 9 1141 := toUpper p_6_9
theorem upper_6_10 : Ramsey.UpperBound 6 10 1782 := toUpper p_6_10
theorem upper_6_11 : Ramsey.UpperBound 6 11 2683 := toUpper p_6_11
theorem upper_6_12 : Ramsey.UpperBound 6 12 3918 := toUpper p_6_12
theorem upper_6_13 : Ramsey.UpperBound 6 13 5571 := toUpper p_6_13
theorem upper_6_14 : Ramsey.UpperBound 6 14 7742 := toUpper p_6_14
theorem upper_6_15 : Ramsey.UpperBound 6 15 10543 := toUpper p_6_15
theorem upper_7_7 : Ramsey.UpperBound 7 7 814 := toUpper p_7_7
theorem upper_7_8 : Ramsey.UpperBound 7 8 1513 := toUpper p_7_8
theorem upper_7_9 : Ramsey.UpperBound 7 9 2654 := toUpper p_7_9
theorem upper_7_10 : Ramsey.UpperBound 7 10 4435 := toUpper p_7_10
theorem upper_7_11 : Ramsey.UpperBound 7 11 7118 := toUpper p_7_11
theorem upper_7_12 : Ramsey.UpperBound 7 12 11035 := toUpper p_7_12
theorem upper_7_13 : Ramsey.UpperBound 7 13 16606 := toUpper p_7_13
theorem upper_7_14 : Ramsey.UpperBound 7 14 24347 := toUpper p_7_14
theorem upper_7_15 : Ramsey.UpperBound 7 15 34890 := toUpper p_7_15
theorem upper_8_8 : Ramsey.UpperBound 8 8 3026 := toUpper p_8_8
theorem upper_8_9 : Ramsey.UpperBound 8 9 5679 := toUpper p_8_9
theorem upper_8_10 : Ramsey.UpperBound 8 10 10114 := toUpper p_8_10
theorem upper_8_11 : Ramsey.UpperBound 8 11 17231 := toUpper p_8_11
theorem upper_8_12 : Ramsey.UpperBound 8 12 28266 := toUpper p_8_12
theorem upper_8_13 : Ramsey.UpperBound 8 13 44871 := toUpper p_8_13
theorem upper_8_14 : Ramsey.UpperBound 8 14 69218 := toUpper p_8_14
theorem upper_8_15 : Ramsey.UpperBound 8 15 104107 := toUpper p_8_15
theorem upper_9_9 : Ramsey.UpperBound 9 9 11358 := toUpper p_9_9
theorem upper_9_10 : Ramsey.UpperBound 9 10 21471 := toUpper p_9_10
theorem upper_9_11 : Ramsey.UpperBound 9 11 38702 := toUpper p_9_11
theorem upper_9_12 : Ramsey.UpperBound 9 12 66967 := toUpper p_9_12
theorem upper_9_13 : Ramsey.UpperBound 9 13 111838 := toUpper p_9_13
theorem upper_9_14 : Ramsey.UpperBound 9 14 181055 := toUpper p_9_14
theorem upper_9_15 : Ramsey.UpperBound 9 15 285162 := toUpper p_9_15
theorem upper_10_10 : Ramsey.UpperBound 10 10 42942 := toUpper p_10_10
theorem upper_10_11 : Ramsey.UpperBound 10 11 81643 := toUpper p_10_11
theorem upper_10_12 : Ramsey.UpperBound 10 12 148610 := toUpper p_10_12
theorem upper_10_13 : Ramsey.UpperBound 10 13 260447 := toUpper p_10_13
theorem upper_10_14 : Ramsey.UpperBound 10 14 441502 := toUpper p_10_14
theorem upper_10_15 : Ramsey.UpperBound 10 15 726663 := toUpper p_10_15

end LeapsInBounds.Proofs.RamseyRecurrence
