module

public import LeapsInBounds.Statements.DegreeDiameter
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Moore bound for the degree-diameter problem

A graph of maximum degree `d` and diameter `k` has at most
`1 + d + d(d-1) + ... + d(d-1)^(k-1)` vertices.

Fix a vertex `v`, and let `B i` be the vertices joined to `v` by a walk of
length at most `i`. There are at most `d` vertices in `B 1` other than `v`.
For `i ≥ 1`, each vertex of `B (i+1)` outside `B i` is adjacent to a vertex `u`
of `B i` outside `B (i-1)`, and such a `u` has a neighbor in `B (i-1)`, so at
most `d - 1` neighbors outside `B i`. The diameter makes `B k` every vertex.
-/

public section

namespace LeapsInBounds.Proofs.DegreeDiameterMoore

open SimpleGraph Walk Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable (G) in
open Classical in
/-- The vertices joined to `v` by a walk of length at most `i`. -/
noncomputable def ball (v : V) (i : ℕ) : Finset V :=
  univ.filter fun w => ∃ p : G.Walk w v, p.length ≤ i

lemma mem_ball {v w : V} {i : ℕ} : w ∈ ball G v i ↔ ∃ p : G.Walk w v, p.length ≤ i := by
  simp [ball]

lemma ball_mono {v : V} {i j : ℕ} (h : i ≤ j) : ball G v i ⊆ ball G v j := by
  intro w hw
  obtain ⟨p, hp⟩ := mem_ball.mp hw
  exact mem_ball.mpr ⟨p, hp.trans h⟩

lemma card_ball_zero (v : V) : #(ball G v 0) ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨p, hp⟩ := mem_ball.mp ha
  obtain ⟨q, hq⟩ := mem_ball.mp hb
  rw [Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp), Walk.eq_of_length_eq_zero (Nat.le_zero.mp hq)]

variable [DecidableEq V] [DecidableRel G.Adj]

lemma layer_one_subset (v : V) : ball G v 1 \ ball G v 0 ⊆ G.neighborFinset v := by
  intro w hw
  rw [mem_sdiff, mem_ball, mem_ball] at hw
  obtain ⟨⟨p, hp⟩, hw⟩ := hw
  cases p with
  | nil => exact (hw ⟨Walk.nil, by simp⟩).elim
  | @cons _ u _ h q =>
    rw [Walk.length_cons] at hp
    have := Walk.eq_of_length_eq_zero (show q.length = 0 by omega)
    subst this
    rw [mem_neighborFinset]
    exact h.symm

/-- The vertices at distance `i + 2` are at most `d - 1` times as many as those
at distance `i + 1`. -/
lemma card_layer_succ {d : ℕ} (hdeg : ∀ w, G.degree w ≤ d) (v : V) (i : ℕ) :
    #(ball G v (i + 2) \ ball G v (i + 1)) ≤ (d - 1) * #(ball G v (i + 1) \ ball G v i) := by
  have hsub : ball G v (i + 2) \ ball G v (i + 1) ⊆
      (ball G v (i + 1) \ ball G v i).biUnion fun u => G.neighborFinset u \ ball G v (i + 1) := by
    intro w hw
    rw [mem_sdiff, mem_ball, mem_ball] at hw
    obtain ⟨⟨p, hp⟩, hw⟩ := hw
    cases p with
    | nil => exact (hw ⟨Walk.nil, by simp⟩).elim
    | @cons _ u _ h q =>
      rw [Walk.length_cons] at hp
      rw [mem_biUnion]
      refine ⟨u, ?_, ?_⟩
      · rw [mem_sdiff, mem_ball, mem_ball]
        refine ⟨⟨q, by omega⟩, ?_⟩
        rintro ⟨r, hr⟩
        exact hw ⟨Walk.cons h r, by rw [Walk.length_cons]; omega⟩
      · rw [mem_sdiff, mem_neighborFinset, mem_ball]
        exact ⟨h.symm, hw⟩
  have hcard : ∀ u ∈ ball G v (i + 1) \ ball G v i,
      #(G.neighborFinset u \ ball G v (i + 1)) ≤ d - 1 := by
    intro u hu
    rw [mem_sdiff, mem_ball, mem_ball] at hu
    obtain ⟨⟨q, hq⟩, hu⟩ := hu
    cases q with
    | nil => exact (hu ⟨Walk.nil, by simp⟩).elim
    | @cons _ x _ h q =>
      rw [Walk.length_cons] at hq
      have hx : x ∈ G.neighborFinset u ∩ ball G v (i + 1) := by
        rw [mem_inter, mem_neighborFinset, mem_ball]
        exact ⟨h, q, by omega⟩
      have h1 := card_sdiff_add_card_inter (G.neighborFinset u) (ball G v (i + 1))
      have h2 := card_pos.mpr ⟨x, hx⟩
      rw [card_neighborFinset_eq_degree] at h1
      have := hdeg u
      omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ u ∈ ball G v (i + 1) \ ball G v i, #(G.neighborFinset u \ ball G v (i + 1)) :=
      card_biUnion_le
    _ ≤ ∑ _u ∈ ball G v (i + 1) \ ball G v i, (d - 1) := sum_le_sum hcard
    _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The ball of radius `n` has at most `1 + d(1 + (d-1) + ... + (d-1)^(n-1))` vertices. -/
lemma card_ball_le {d : ℕ} (hdeg : ∀ w, G.degree w ≤ d) (v : V) (n : ℕ) :
    #(ball G v n) ≤ 1 + d * ∑ j ∈ range n, (d - 1) ^ j := by
  have hlayer : ∀ j, #(ball G v (j + 1) \ ball G v j) ≤ d * (d - 1) ^ j := by
    intro j
    induction j with
    | zero =>
      have := card_le_card (layer_one_subset (G := G) v)
      rw [card_neighborFinset_eq_degree] at this
      simpa using this.trans (hdeg v)
    | succ j ih =>
      calc _ ≤ (d - 1) * #(ball G v (j + 1) \ ball G v j) := card_layer_succ hdeg v j
        _ ≤ (d - 1) * (d * (d - 1) ^ j) := Nat.mul_le_mul_left _ ih
        _ = d * (d - 1) ^ (j + 1) := by rw [pow_succ', Nat.mul_left_comm]
  induction n with
  | zero => simpa using card_ball_zero (G := G) v
  | succ n ih =>
    have h1 := card_sdiff_add_card_inter (ball G v (n + 1)) (ball G v n)
    rw [inter_eq_right.mpr (ball_mono (Nat.le_succ n))] at h1
    rw [sum_range_succ, mul_add]
    have := hlayer n
    omega

/-- Moore bound: `N(d, k) ≤ 1 + d(1 + (d-1) + ... + (d-1)^(k-1))`. -/
theorem upper (d k : ℕ) :
    DegreeDiameter.UpperBound d k (1 + d * ∑ j ∈ range k, (d - 1) ^ j) := by
  intro m G ⟨hdeg, hdiam⟩
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · omega
  have hdeg' (w : Fin m) : G.degree w ≤ d := by
    refine le_trans (le_of_eq ?_) (hdeg w)
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  have huniv : ball G (⟨0, hm⟩ : Fin m) k = univ := by
    ext w
    simp only [mem_univ, iff_true, mem_ball]
    exact hdiam w _
  have := card_ball_le hdeg' (⟨0, hm⟩ : Fin m) k
  rwa [huniv, card_univ, Fintype.card_fin] at this

/-! Certificates, one per constant. -/

theorem upper_3_2 : DegreeDiameter.UpperBound 3 2 10 := by
  simpa [sum_range_succ] using upper 3 2

theorem upper_4_2 : DegreeDiameter.UpperBound 4 2 17 := by
  simpa [sum_range_succ] using upper 4 2

theorem upper_5_2 : DegreeDiameter.UpperBound 5 2 26 := by
  simpa [sum_range_succ] using upper 5 2

theorem upper_6_2 : DegreeDiameter.UpperBound 6 2 37 := by
  simpa [sum_range_succ] using upper 6 2

theorem upper_7_2 : DegreeDiameter.UpperBound 7 2 50 := by
  simpa [sum_range_succ] using upper 7 2

theorem upper_8_2 : DegreeDiameter.UpperBound 8 2 65 := by
  simpa [sum_range_succ] using upper 8 2

theorem upper_9_2 : DegreeDiameter.UpperBound 9 2 82 := by
  simpa [sum_range_succ] using upper 9 2

theorem upper_10_2 : DegreeDiameter.UpperBound 10 2 101 := by
  simpa [sum_range_succ] using upper 10 2

theorem upper_11_2 : DegreeDiameter.UpperBound 11 2 122 := by
  simpa [sum_range_succ] using upper 11 2

theorem upper_12_2 : DegreeDiameter.UpperBound 12 2 145 := by
  simpa [sum_range_succ] using upper 12 2

theorem upper_13_2 : DegreeDiameter.UpperBound 13 2 170 := by
  simpa [sum_range_succ] using upper 13 2

theorem upper_14_2 : DegreeDiameter.UpperBound 14 2 197 := by
  simpa [sum_range_succ] using upper 14 2

theorem upper_15_2 : DegreeDiameter.UpperBound 15 2 226 := by
  simpa [sum_range_succ] using upper 15 2

theorem upper_16_2 : DegreeDiameter.UpperBound 16 2 257 := by
  simpa [sum_range_succ] using upper 16 2

theorem upper_17_2 : DegreeDiameter.UpperBound 17 2 290 := by
  simpa [sum_range_succ] using upper 17 2

theorem upper_18_2 : DegreeDiameter.UpperBound 18 2 325 := by
  simpa [sum_range_succ] using upper 18 2

theorem upper_19_2 : DegreeDiameter.UpperBound 19 2 362 := by
  simpa [sum_range_succ] using upper 19 2

theorem upper_20_2 : DegreeDiameter.UpperBound 20 2 401 := by
  simpa [sum_range_succ] using upper 20 2

theorem upper_3_3 : DegreeDiameter.UpperBound 3 3 22 := by
  simpa [sum_range_succ] using upper 3 3

theorem upper_4_3 : DegreeDiameter.UpperBound 4 3 53 := by
  simpa [sum_range_succ] using upper 4 3

theorem upper_5_3 : DegreeDiameter.UpperBound 5 3 106 := by
  simpa [sum_range_succ] using upper 5 3

theorem upper_6_3 : DegreeDiameter.UpperBound 6 3 187 := by
  simpa [sum_range_succ] using upper 6 3

theorem upper_7_3 : DegreeDiameter.UpperBound 7 3 302 := by
  simpa [sum_range_succ] using upper 7 3

theorem upper_8_3 : DegreeDiameter.UpperBound 8 3 457 := by
  simpa [sum_range_succ] using upper 8 3

theorem upper_9_3 : DegreeDiameter.UpperBound 9 3 658 := by
  simpa [sum_range_succ] using upper 9 3

theorem upper_10_3 : DegreeDiameter.UpperBound 10 3 911 := by
  simpa [sum_range_succ] using upper 10 3

theorem upper_11_3 : DegreeDiameter.UpperBound 11 3 1222 := by
  simpa [sum_range_succ] using upper 11 3

theorem upper_12_3 : DegreeDiameter.UpperBound 12 3 1597 := by
  simpa [sum_range_succ] using upper 12 3

theorem upper_13_3 : DegreeDiameter.UpperBound 13 3 2042 := by
  simpa [sum_range_succ] using upper 13 3

theorem upper_14_3 : DegreeDiameter.UpperBound 14 3 2563 := by
  simpa [sum_range_succ] using upper 14 3

theorem upper_15_3 : DegreeDiameter.UpperBound 15 3 3166 := by
  simpa [sum_range_succ] using upper 15 3

theorem upper_16_3 : DegreeDiameter.UpperBound 16 3 3857 := by
  simpa [sum_range_succ] using upper 16 3

theorem upper_17_3 : DegreeDiameter.UpperBound 17 3 4642 := by
  simpa [sum_range_succ] using upper 17 3

theorem upper_18_3 : DegreeDiameter.UpperBound 18 3 5527 := by
  simpa [sum_range_succ] using upper 18 3

theorem upper_19_3 : DegreeDiameter.UpperBound 19 3 6518 := by
  simpa [sum_range_succ] using upper 19 3

theorem upper_20_3 : DegreeDiameter.UpperBound 20 3 7621 := by
  simpa [sum_range_succ] using upper 20 3

theorem upper_3_4 : DegreeDiameter.UpperBound 3 4 46 := by
  simpa [sum_range_succ] using upper 3 4

theorem upper_4_4 : DegreeDiameter.UpperBound 4 4 161 := by
  simpa [sum_range_succ] using upper 4 4

theorem upper_5_4 : DegreeDiameter.UpperBound 5 4 426 := by
  simpa [sum_range_succ] using upper 5 4

theorem upper_6_4 : DegreeDiameter.UpperBound 6 4 937 := by
  simpa [sum_range_succ] using upper 6 4

theorem upper_7_4 : DegreeDiameter.UpperBound 7 4 1814 := by
  simpa [sum_range_succ] using upper 7 4

theorem upper_8_4 : DegreeDiameter.UpperBound 8 4 3201 := by
  simpa [sum_range_succ] using upper 8 4

theorem upper_9_4 : DegreeDiameter.UpperBound 9 4 5266 := by
  simpa [sum_range_succ] using upper 9 4

theorem upper_10_4 : DegreeDiameter.UpperBound 10 4 8201 := by
  simpa [sum_range_succ] using upper 10 4

theorem upper_11_4 : DegreeDiameter.UpperBound 11 4 12222 := by
  simpa [sum_range_succ] using upper 11 4

theorem upper_12_4 : DegreeDiameter.UpperBound 12 4 17569 := by
  simpa [sum_range_succ] using upper 12 4

theorem upper_13_4 : DegreeDiameter.UpperBound 13 4 24506 := by
  simpa [sum_range_succ] using upper 13 4

theorem upper_14_4 : DegreeDiameter.UpperBound 14 4 33321 := by
  simpa [sum_range_succ] using upper 14 4

theorem upper_15_4 : DegreeDiameter.UpperBound 15 4 44326 := by
  simpa [sum_range_succ] using upper 15 4

theorem upper_16_4 : DegreeDiameter.UpperBound 16 4 57857 := by
  simpa [sum_range_succ] using upper 16 4

theorem upper_17_4 : DegreeDiameter.UpperBound 17 4 74274 := by
  simpa [sum_range_succ] using upper 17 4

theorem upper_18_4 : DegreeDiameter.UpperBound 18 4 93961 := by
  simpa [sum_range_succ] using upper 18 4

theorem upper_19_4 : DegreeDiameter.UpperBound 19 4 117326 := by
  simpa [sum_range_succ] using upper 19 4

theorem upper_20_4 : DegreeDiameter.UpperBound 20 4 144801 := by
  simpa [sum_range_succ] using upper 20 4

theorem upper_3_5 : DegreeDiameter.UpperBound 3 5 94 := by
  simpa [sum_range_succ] using upper 3 5

theorem upper_4_5 : DegreeDiameter.UpperBound 4 5 485 := by
  simpa [sum_range_succ] using upper 4 5

theorem upper_5_5 : DegreeDiameter.UpperBound 5 5 1706 := by
  simpa [sum_range_succ] using upper 5 5

theorem upper_6_5 : DegreeDiameter.UpperBound 6 5 4687 := by
  simpa [sum_range_succ] using upper 6 5

theorem upper_7_5 : DegreeDiameter.UpperBound 7 5 10886 := by
  simpa [sum_range_succ] using upper 7 5

theorem upper_8_5 : DegreeDiameter.UpperBound 8 5 22409 := by
  simpa [sum_range_succ] using upper 8 5

theorem upper_9_5 : DegreeDiameter.UpperBound 9 5 42130 := by
  simpa [sum_range_succ] using upper 9 5

theorem upper_10_5 : DegreeDiameter.UpperBound 10 5 73811 := by
  simpa [sum_range_succ] using upper 10 5

theorem upper_11_5 : DegreeDiameter.UpperBound 11 5 122222 := by
  simpa [sum_range_succ] using upper 11 5

theorem upper_12_5 : DegreeDiameter.UpperBound 12 5 193261 := by
  simpa [sum_range_succ] using upper 12 5

theorem upper_13_5 : DegreeDiameter.UpperBound 13 5 294074 := by
  simpa [sum_range_succ] using upper 13 5

theorem upper_14_5 : DegreeDiameter.UpperBound 14 5 433175 := by
  simpa [sum_range_succ] using upper 14 5

theorem upper_15_5 : DegreeDiameter.UpperBound 15 5 620566 := by
  simpa [sum_range_succ] using upper 15 5

theorem upper_16_5 : DegreeDiameter.UpperBound 16 5 867857 := by
  simpa [sum_range_succ] using upper 16 5

theorem upper_17_5 : DegreeDiameter.UpperBound 17 5 1188386 := by
  simpa [sum_range_succ] using upper 17 5

theorem upper_18_5 : DegreeDiameter.UpperBound 18 5 1597339 := by
  simpa [sum_range_succ] using upper 18 5

theorem upper_19_5 : DegreeDiameter.UpperBound 19 5 2111870 := by
  simpa [sum_range_succ] using upper 19 5

theorem upper_20_5 : DegreeDiameter.UpperBound 20 5 2751221 := by
  simpa [sum_range_succ] using upper 20 5

theorem upper_3_6 : DegreeDiameter.UpperBound 3 6 190 := by
  simpa [sum_range_succ] using upper 3 6

theorem upper_4_6 : DegreeDiameter.UpperBound 4 6 1457 := by
  simpa [sum_range_succ] using upper 4 6

theorem upper_5_6 : DegreeDiameter.UpperBound 5 6 6826 := by
  simpa [sum_range_succ] using upper 5 6

theorem upper_6_6 : DegreeDiameter.UpperBound 6 6 23437 := by
  simpa [sum_range_succ] using upper 6 6

theorem upper_7_6 : DegreeDiameter.UpperBound 7 6 65318 := by
  simpa [sum_range_succ] using upper 7 6

theorem upper_8_6 : DegreeDiameter.UpperBound 8 6 156865 := by
  simpa [sum_range_succ] using upper 8 6

theorem upper_9_6 : DegreeDiameter.UpperBound 9 6 337042 := by
  simpa [sum_range_succ] using upper 9 6

theorem upper_10_6 : DegreeDiameter.UpperBound 10 6 664301 := by
  simpa [sum_range_succ] using upper 10 6

theorem upper_11_6 : DegreeDiameter.UpperBound 11 6 1222222 := by
  simpa [sum_range_succ] using upper 11 6

theorem upper_12_6 : DegreeDiameter.UpperBound 12 6 2125873 := by
  simpa [sum_range_succ] using upper 12 6

theorem upper_13_6 : DegreeDiameter.UpperBound 13 6 3528890 := by
  simpa [sum_range_succ] using upper 13 6

theorem upper_14_6 : DegreeDiameter.UpperBound 14 6 5631277 := by
  simpa [sum_range_succ] using upper 14 6

theorem upper_15_6 : DegreeDiameter.UpperBound 15 6 8687926 := by
  simpa [sum_range_succ] using upper 15 6

theorem upper_16_6 : DegreeDiameter.UpperBound 16 6 13017857 := by
  simpa [sum_range_succ] using upper 16 6

theorem upper_17_6 : DegreeDiameter.UpperBound 17 6 19014178 := by
  simpa [sum_range_succ] using upper 17 6

theorem upper_18_6 : DegreeDiameter.UpperBound 18 6 27154765 := by
  simpa [sum_range_succ] using upper 18 6

theorem upper_19_6 : DegreeDiameter.UpperBound 19 6 38013662 := by
  simpa [sum_range_succ] using upper 19 6

theorem upper_20_6 : DegreeDiameter.UpperBound 20 6 52273201 := by
  simpa [sum_range_succ] using upper 20 6

theorem upper_3_7 : DegreeDiameter.UpperBound 3 7 382 := by
  simpa [sum_range_succ] using upper 3 7

theorem upper_4_7 : DegreeDiameter.UpperBound 4 7 4373 := by
  simpa [sum_range_succ] using upper 4 7

theorem upper_5_7 : DegreeDiameter.UpperBound 5 7 27306 := by
  simpa [sum_range_succ] using upper 5 7

theorem upper_6_7 : DegreeDiameter.UpperBound 6 7 117187 := by
  simpa [sum_range_succ] using upper 6 7

theorem upper_7_7 : DegreeDiameter.UpperBound 7 7 391910 := by
  simpa [sum_range_succ] using upper 7 7

theorem upper_8_7 : DegreeDiameter.UpperBound 8 7 1098057 := by
  simpa [sum_range_succ] using upper 8 7

theorem upper_9_7 : DegreeDiameter.UpperBound 9 7 2696338 := by
  simpa [sum_range_succ] using upper 9 7

theorem upper_10_7 : DegreeDiameter.UpperBound 10 7 5978711 := by
  simpa [sum_range_succ] using upper 10 7

theorem upper_11_7 : DegreeDiameter.UpperBound 11 7 12222222 := by
  simpa [sum_range_succ] using upper 11 7

theorem upper_12_7 : DegreeDiameter.UpperBound 12 7 23384605 := by
  simpa [sum_range_succ] using upper 12 7

theorem upper_13_7 : DegreeDiameter.UpperBound 13 7 42346682 := by
  simpa [sum_range_succ] using upper 13 7

theorem upper_14_7 : DegreeDiameter.UpperBound 14 7 73206603 := by
  simpa [sum_range_succ] using upper 14 7

theorem upper_15_7 : DegreeDiameter.UpperBound 15 7 121630966 := by
  simpa [sum_range_succ] using upper 15 7

theorem upper_16_7 : DegreeDiameter.UpperBound 16 7 195267857 := by
  simpa [sum_range_succ] using upper 16 7

theorem upper_17_7 : DegreeDiameter.UpperBound 17 7 304226850 := by
  simpa [sum_range_succ] using upper 17 7

theorem upper_18_7 : DegreeDiameter.UpperBound 18 7 461631007 := by
  simpa [sum_range_succ] using upper 18 7

theorem upper_19_7 : DegreeDiameter.UpperBound 19 7 684245918 := by
  simpa [sum_range_succ] using upper 19 7

theorem upper_20_7 : DegreeDiameter.UpperBound 20 7 993190821 := by
  simpa [sum_range_succ] using upper 20 7

theorem upper_3_8 : DegreeDiameter.UpperBound 3 8 766 := by
  simpa [sum_range_succ] using upper 3 8

theorem upper_4_8 : DegreeDiameter.UpperBound 4 8 13121 := by
  simpa [sum_range_succ] using upper 4 8

theorem upper_5_8 : DegreeDiameter.UpperBound 5 8 109226 := by
  simpa [sum_range_succ] using upper 5 8

theorem upper_6_8 : DegreeDiameter.UpperBound 6 8 585937 := by
  simpa [sum_range_succ] using upper 6 8

theorem upper_7_8 : DegreeDiameter.UpperBound 7 8 2351462 := by
  simpa [sum_range_succ] using upper 7 8

theorem upper_8_8 : DegreeDiameter.UpperBound 8 8 7686401 := by
  simpa [sum_range_succ] using upper 8 8

theorem upper_9_8 : DegreeDiameter.UpperBound 9 8 21570706 := by
  simpa [sum_range_succ] using upper 9 8

theorem upper_10_8 : DegreeDiameter.UpperBound 10 8 53808401 := by
  simpa [sum_range_succ] using upper 10 8

theorem upper_11_8 : DegreeDiameter.UpperBound 11 8 122222222 := by
  simpa [sum_range_succ] using upper 11 8

theorem upper_12_8 : DegreeDiameter.UpperBound 12 8 257230657 := by
  simpa [sum_range_succ] using upper 12 8

theorem upper_13_8 : DegreeDiameter.UpperBound 13 8 508160186 := by
  simpa [sum_range_succ] using upper 13 8

theorem upper_14_8 : DegreeDiameter.UpperBound 14 8 951685841 := by
  simpa [sum_range_succ] using upper 14 8

theorem upper_15_8 : DegreeDiameter.UpperBound 15 8 1702833526 := by
  simpa [sum_range_succ] using upper 15 8

theorem upper_16_8 : DegreeDiameter.UpperBound 16 8 2929017857 := by
  simpa [sum_range_succ] using upper 16 8

theorem upper_17_8 : DegreeDiameter.UpperBound 17 8 4867629602 := by
  simpa [sum_range_succ] using upper 17 8

theorem upper_18_8 : DegreeDiameter.UpperBound 18 8 7847727121 := by
  simpa [sum_range_succ] using upper 18 8

theorem upper_19_8 : DegreeDiameter.UpperBound 19 8 12316426526 := by
  simpa [sum_range_succ] using upper 19 8

theorem upper_20_8 : DegreeDiameter.UpperBound 20 8 18870625601 := by
  simpa [sum_range_succ] using upper 20 8

theorem upper_3_9 : DegreeDiameter.UpperBound 3 9 1534 := by
  simpa [sum_range_succ] using upper 3 9

theorem upper_4_9 : DegreeDiameter.UpperBound 4 9 39365 := by
  simpa [sum_range_succ] using upper 4 9

theorem upper_5_9 : DegreeDiameter.UpperBound 5 9 436906 := by
  simpa [sum_range_succ] using upper 5 9

theorem upper_6_9 : DegreeDiameter.UpperBound 6 9 2929687 := by
  simpa [sum_range_succ] using upper 6 9

theorem upper_7_9 : DegreeDiameter.UpperBound 7 9 14108774 := by
  simpa [sum_range_succ] using upper 7 9

theorem upper_8_9 : DegreeDiameter.UpperBound 8 9 53804809 := by
  simpa [sum_range_succ] using upper 8 9

theorem upper_9_9 : DegreeDiameter.UpperBound 9 9 172565650 := by
  simpa [sum_range_succ] using upper 9 9

theorem upper_10_9 : DegreeDiameter.UpperBound 10 9 484275611 := by
  simpa [sum_range_succ] using upper 10 9

theorem upper_11_9 : DegreeDiameter.UpperBound 11 9 1222222222 := by
  simpa [sum_range_succ] using upper 11 9

theorem upper_12_9 : DegreeDiameter.UpperBound 12 9 2829537229 := by
  simpa [sum_range_succ] using upper 12 9

theorem upper_13_9 : DegreeDiameter.UpperBound 13 9 6097922234 := by
  simpa [sum_range_succ] using upper 13 9

theorem upper_14_9 : DegreeDiameter.UpperBound 14 9 12371915935 := by
  simpa [sum_range_succ] using upper 14 9

theorem upper_15_9 : DegreeDiameter.UpperBound 15 9 23839669366 := by
  simpa [sum_range_succ] using upper 15 9

theorem upper_16_9 : DegreeDiameter.UpperBound 16 9 43935267857 := by
  simpa [sum_range_succ] using upper 16 9

theorem upper_17_9 : DegreeDiameter.UpperBound 17 9 77882073634 := by
  simpa [sum_range_succ] using upper 17 9

theorem upper_18_9 : DegreeDiameter.UpperBound 18 9 133411361059 := by
  simpa [sum_range_succ] using upper 18 9

theorem upper_19_9 : DegreeDiameter.UpperBound 19 9 221695677470 := by
  simpa [sum_range_succ] using upper 19 9

theorem upper_20_9 : DegreeDiameter.UpperBound 20 9 358541886421 := by
  simpa [sum_range_succ] using upper 20 9

theorem upper_3_10 : DegreeDiameter.UpperBound 3 10 3070 := by
  simpa [sum_range_succ] using upper 3 10

theorem upper_4_10 : DegreeDiameter.UpperBound 4 10 118097 := by
  simpa [sum_range_succ] using upper 4 10

theorem upper_5_10 : DegreeDiameter.UpperBound 5 10 1747626 := by
  simpa [sum_range_succ] using upper 5 10

theorem upper_6_10 : DegreeDiameter.UpperBound 6 10 14648437 := by
  simpa [sum_range_succ] using upper 6 10

theorem upper_7_10 : DegreeDiameter.UpperBound 7 10 84652646 := by
  simpa [sum_range_succ] using upper 7 10

theorem upper_8_10 : DegreeDiameter.UpperBound 8 10 376633665 := by
  simpa [sum_range_succ] using upper 8 10

theorem upper_9_10 : DegreeDiameter.UpperBound 9 10 1380525202 := by
  simpa [sum_range_succ] using upper 9 10

theorem upper_10_10 : DegreeDiameter.UpperBound 10 10 4358480501 := by
  simpa [sum_range_succ] using upper 10 10

theorem upper_11_10 : DegreeDiameter.UpperBound 11 10 12222222222 := by
  simpa [sum_range_succ] using upper 11 10

theorem upper_12_10 : DegreeDiameter.UpperBound 12 10 31124909521 := by
  simpa [sum_range_succ] using upper 12 10

theorem upper_13_10 : DegreeDiameter.UpperBound 13 10 73175066810 := by
  simpa [sum_range_succ] using upper 13 10

theorem upper_14_10 : DegreeDiameter.UpperBound 14 10 160834907157 := by
  simpa [sum_range_succ] using upper 14 10

theorem upper_15_10 : DegreeDiameter.UpperBound 15 10 333755371126 := by
  simpa [sum_range_succ] using upper 15 10

theorem upper_16_10 : DegreeDiameter.UpperBound 16 10 659029017857 := by
  simpa [sum_range_succ] using upper 16 10

theorem upper_17_10 : DegreeDiameter.UpperBound 17 10 1246113178146 := by
  simpa [sum_range_succ] using upper 17 10

theorem upper_18_10 : DegreeDiameter.UpperBound 18 10 2267993138005 := by
  simpa [sum_range_succ] using upper 18 10

theorem upper_19_10 : DegreeDiameter.UpperBound 19 10 3990522194462 := by
  simpa [sum_range_succ] using upper 19 10

theorem upper_20_10 : DegreeDiameter.UpperBound 20 10 6812295842001 := by
  simpa [sum_range_succ] using upper 20 10

end LeapsInBounds.Proofs.DegreeDiameterMoore
