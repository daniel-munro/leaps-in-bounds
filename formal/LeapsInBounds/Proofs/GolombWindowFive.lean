module

public import LeapsInBounds.Statements.Golomb
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Five-window lower bounds for Golomb rulers

The selected pairs are explicit finite sets of indices. Their validity and
cardinalities are checked by kernel reduction. All distances and their lower
sum bounds are derived from the trusted `Golomb.IsGolomb` predicate.
-/

public section

namespace LeapsInBounds.Proofs.GolombWindowFive

open Finset

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] def pairSum {n : ℕ} (a : Fin n → ℕ) (P : Finset (Fin n × Fin n)) : ℤ :=
  ∑ p ∈ P, ((a p.2 : ℤ) - (a p.1 : ℤ))

/-- Distinct positive distances indexed by any set of increasing index pairs
have sum at least the sum of the first `P.card` positive integers. -/
theorem pair_sum_lower {n : ℕ} {s : Finset ℕ} (hs : s.card = n)
    (hg : Golomb.IsGolomb s) (P : Finset (Fin n × Fin n))
    (hP : ∀ p ∈ P, p.1 < p.2) :
    (∑ k ∈ range P.card, (1 + (k : ℤ))) ≤ pairSum (s.orderEmbOfFin hs) P := by
  let a := s.orderEmbOfFin hs
  let d : Fin n × Fin n → ℤ := fun p => (a p.2 : ℤ) - (a p.1 : ℤ)
  have hmem (i : Fin n) : a i ∈ s := s.orderEmbOfFin_mem hs i
  have hlt (p : Fin n × Fin n) (hp : p ∈ P) : a p.1 < a p.2 :=
    a.strictMono (hP p hp)
  have hinj : Set.InjOn d P := by
    intro p hp q hq he
    have hp' := hlt p hp
    have hq' := hlt q hq
    have hnat : a p.2 - a p.1 = a q.2 - a q.1 := by
      dsimp [d] at he
      omega
    obtain ⟨h1, h2⟩ := hg _ (hmem p.1) _ (hmem p.2)
      _ (hmem q.1) _ (hmem q.2) hp' hq' hnat
    exact Prod.ext (a.injective h1) (a.injective h2)
  have hpos : ∀ x ∈ P.image d, (1 : ℤ) ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    have := hlt p hp
    dsimp [d]
    omega
  have h := Finset.sum_range_le_sum hpos
  rw [card_image_of_injOn hinj, sum_image hinj] at h
  exact h

def windowPairs29 : List (Fin 29 × Fin 29) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8),
   (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16),
   (16, 17), (17, 18), (18, 19), (19, 20), (20, 21), (21, 22), (22, 23), (23, 24),
   (24, 25), (25, 26), (26, 27), (27, 28), (0, 2), (1, 3), (2, 4), (3, 5),
   (4, 6), (5, 7), (6, 8), (7, 9), (8, 10), (9, 11), (10, 12), (11, 13),
   (12, 14), (13, 15), (14, 16), (15, 17), (16, 18), (17, 19), (18, 20), (19, 21),
   (20, 22), (21, 23), (22, 24), (23, 25), (24, 26), (25, 27), (26, 28), (0, 3),
   (1, 4), (2, 5), (3, 6), (4, 7), (5, 8), (6, 9), (7, 10), (8, 11),
   (9, 12), (10, 13), (11, 14), (12, 15), (13, 16), (14, 17), (15, 18), (16, 19),
   (17, 20), (18, 21), (19, 22), (20, 23), (21, 24), (22, 25), (23, 26), (24, 27),
   (25, 28), (0, 4), (1, 5), (2, 6), (3, 7), (4, 8), (5, 9), (6, 10),
   (7, 11), (8, 12), (9, 13), (10, 14), (11, 15), (12, 16), (13, 17), (14, 18),
   (15, 19), (16, 20), (17, 21), (18, 22), (19, 23), (20, 24), (21, 25), (22, 26),
   (23, 27), (24, 28), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 10),
   (6, 11), (7, 12), (8, 13), (9, 14), (10, 15), (11, 16), (12, 17), (13, 18),
   (14, 19), (15, 20), (16, 21), (17, 22), (18, 23), (19, 24), (20, 25), (21, 26),
   (22, 27), (23, 28)]

def window29 : Finset (Fin 29 × Fin 29) := windowPairs29.toFinset

def fourteenPairs29 : List (Fin 29 × Fin 29) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4), (27, 28),
   (26, 28), (25, 28), (26, 27), (25, 27), (25, 26), (24, 25)]

def fourteen29 : Finset (Fin 29 × Fin 29) := fourteenPairs29.toFinset

def sixPairs29 : List (Fin 29 × Fin 29) :=
  [(0, 1), (0, 2), (1, 2), (27, 28), (26, 28), (26, 27)]

def six29 : Finset (Fin 29 × Fin 29) := sixPairs29.toFinset

def twoPairs29 : List (Fin 29 × Fin 29) :=
  [(0, 1), (27, 28)]

def two29 : Finset (Fin 29 × Fin 29) := twoPairs29.toFinset

/-- Exact cancellation identity for the five-window and endpoint sums. -/
theorem identity_29 (a : Fin 29 → ℕ) :
    pairSum a window29 + pairSum a fourteen29 + pairSum a six29 +
      5 * pairSum a two29 = 15 * ((a 28 : ℤ) - (a 0 : ℤ)) := by
  simp only [pairSum, window29, fourteen29, six29, two29]
  rw [List.sum_toFinset _ (by decide : windowPairs29.Nodup)]
  rw [List.sum_toFinset _ (by decide : fourteenPairs29.Nodup)]
  rw [List.sum_toFinset _ (by decide : sixPairs29.Nodup)]
  rw [List.sum_toFinset _ (by decide : twoPairs29.Nodup)]
  norm_num [windowPairs29, fourteenPairs29, sixPairs29, twoPairs29]
  ring

/-- The full trusted 29-mark lower bound, with no external mathematical hypotheses. -/
theorem lower_29 : Golomb.LowerBound 29 578 := by
  intro s hs hg
  let a := s.orderEmbOfFin hs
  have h_window := pair_sum_lower hs hg window29 (by decide)
  have hc_window : window29.card = 130 := by decide
  rw [hc_window] at h_window
  norm_num [Finset.sum_range_succ] at h_window
  change (8515 : ℤ) ≤ pairSum a window29 at h_window
  have h_fourteen := pair_sum_lower hs hg fourteen29 (by decide)
  have hc_fourteen : fourteen29.card = 14 := by decide
  rw [hc_fourteen] at h_fourteen
  norm_num [Finset.sum_range_succ] at h_fourteen
  change (105 : ℤ) ≤ pairSum a fourteen29 at h_fourteen
  have h_six := pair_sum_lower hs hg six29 (by decide)
  have hc_six : six29.card = 6 := by decide
  rw [hc_six] at h_six
  norm_num [Finset.sum_range_succ] at h_six
  change (21 : ℤ) ≤ pairSum a six29 at h_six
  have h_two := pair_sum_lower hs hg two29 (by decide)
  have hc_two : two29.card = 2 := by decide
  rw [hc_two] at h_two
  norm_num [Finset.sum_range_succ] at h_two
  change (3 : ℤ) ≤ pairSum a two29 at h_two
  have hi := identity_29 a
  have hends : a 0 ≤ a 28 := a.monotone (by decide)
  refine ⟨a 0, s.orderEmbOfFin_mem hs 0, a 28, s.orderEmbOfFin_mem hs 28, ?_⟩
  omega

def windowPairs30 : List (Fin 30 × Fin 30) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8),
   (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16),
   (16, 17), (17, 18), (18, 19), (19, 20), (20, 21), (21, 22), (22, 23), (23, 24),
   (24, 25), (25, 26), (26, 27), (27, 28), (28, 29), (0, 2), (1, 3), (2, 4),
   (3, 5), (4, 6), (5, 7), (6, 8), (7, 9), (8, 10), (9, 11), (10, 12),
   (11, 13), (12, 14), (13, 15), (14, 16), (15, 17), (16, 18), (17, 19), (18, 20),
   (19, 21), (20, 22), (21, 23), (22, 24), (23, 25), (24, 26), (25, 27), (26, 28),
   (27, 29), (0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8), (6, 9),
   (7, 10), (8, 11), (9, 12), (10, 13), (11, 14), (12, 15), (13, 16), (14, 17),
   (15, 18), (16, 19), (17, 20), (18, 21), (19, 22), (20, 23), (21, 24), (22, 25),
   (23, 26), (24, 27), (25, 28), (26, 29), (0, 4), (1, 5), (2, 6), (3, 7),
   (4, 8), (5, 9), (6, 10), (7, 11), (8, 12), (9, 13), (10, 14), (11, 15),
   (12, 16), (13, 17), (14, 18), (15, 19), (16, 20), (17, 21), (18, 22), (19, 23),
   (20, 24), (21, 25), (22, 26), (23, 27), (24, 28), (25, 29), (0, 5), (1, 6),
   (2, 7), (3, 8), (4, 9), (5, 10), (6, 11), (7, 12), (8, 13), (9, 14),
   (10, 15), (11, 16), (12, 17), (13, 18), (14, 19), (15, 20), (16, 21), (17, 22),
   (18, 23), (19, 24), (20, 25), (21, 26), (22, 27), (23, 28), (24, 29)]

def window30 : Finset (Fin 30 × Fin 30) := windowPairs30.toFinset

def fourteenPairs30 : List (Fin 30 × Fin 30) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4), (28, 29),
   (27, 29), (26, 29), (27, 28), (26, 28), (26, 27), (25, 26)]

def fourteen30 : Finset (Fin 30 × Fin 30) := fourteenPairs30.toFinset

def sixPairs30 : List (Fin 30 × Fin 30) :=
  [(0, 1), (0, 2), (1, 2), (28, 29), (27, 29), (27, 28)]

def six30 : Finset (Fin 30 × Fin 30) := sixPairs30.toFinset

def twoPairs30 : List (Fin 30 × Fin 30) :=
  [(0, 1), (28, 29)]

def two30 : Finset (Fin 30 × Fin 30) := twoPairs30.toFinset

/-- Exact cancellation identity for the five-window and endpoint sums. -/
theorem identity_30 (a : Fin 30 → ℕ) :
    pairSum a window30 + pairSum a fourteen30 + pairSum a six30 +
      5 * pairSum a two30 = 15 * ((a 29 : ℤ) - (a 0 : ℤ)) := by
  simp only [pairSum, window30, fourteen30, six30, two30]
  rw [List.sum_toFinset _ (by decide : windowPairs30.Nodup)]
  rw [List.sum_toFinset _ (by decide : fourteenPairs30.Nodup)]
  rw [List.sum_toFinset _ (by decide : sixPairs30.Nodup)]
  rw [List.sum_toFinset _ (by decide : twoPairs30.Nodup)]
  norm_num [windowPairs30, fourteenPairs30, sixPairs30, twoPairs30]
  ring

/-- The full trusted 30-mark lower bound, with no external mathematical hypotheses. -/
theorem lower_30 : Golomb.LowerBound 30 622 := by
  intro s hs hg
  let a := s.orderEmbOfFin hs
  have h_window := pair_sum_lower hs hg window30 (by decide)
  have hc_window : window30.card = 135 := by decide
  rw [hc_window] at h_window
  norm_num [Finset.sum_range_succ] at h_window
  change (9180 : ℤ) ≤ pairSum a window30 at h_window
  have h_fourteen := pair_sum_lower hs hg fourteen30 (by decide)
  have hc_fourteen : fourteen30.card = 14 := by decide
  rw [hc_fourteen] at h_fourteen
  norm_num [Finset.sum_range_succ] at h_fourteen
  change (105 : ℤ) ≤ pairSum a fourteen30 at h_fourteen
  have h_six := pair_sum_lower hs hg six30 (by decide)
  have hc_six : six30.card = 6 := by decide
  rw [hc_six] at h_six
  norm_num [Finset.sum_range_succ] at h_six
  change (21 : ℤ) ≤ pairSum a six30 at h_six
  have h_two := pair_sum_lower hs hg two30 (by decide)
  have hc_two : two30.card = 2 := by decide
  rw [hc_two] at h_two
  norm_num [Finset.sum_range_succ] at h_two
  change (3 : ℤ) ≤ pairSum a two30 at h_two
  have hi := identity_30 a
  have hends : a 0 ≤ a 29 := a.monotone (by decide)
  refine ⟨a 0, s.orderEmbOfFin_mem hs 0, a 29, s.orderEmbOfFin_mem hs 29, ?_⟩
  omega

end LeapsInBounds.Proofs.GolombWindowFive
