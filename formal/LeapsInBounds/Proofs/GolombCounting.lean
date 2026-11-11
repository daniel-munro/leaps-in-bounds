module

public import LeapsInBounds.Statements.Golomb
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting lower bound for Golomb rulers

A Golomb ruler with `n` marks has length at least `n(n-1)/2`: the `n(n-1)/2`
pairs of marks `a < b` have distinct differences `b - a`, all between `1` and
the length of the ruler.
-/

public section

namespace LeapsInBounds.Proofs.GolombCounting

open Finset

/-- `G(n) ≥ n(n-1)/2` for `n ≥ 1`. -/
theorem lower {n : ℕ} (hn : 1 ≤ n) : Golomb.LowerBound n (n * (n - 1) / 2) := by
  intro s hs hg
  have hne : s.Nonempty := card_pos.mp (by omega)
  refine ⟨s.min' hne, min'_mem _ _, s.max' hne, max'_mem _ _, ?_⟩
  set P := (s ×ˢ s).filter fun p : ℕ × ℕ => p.1 < p.2
  -- the pairs `a < b` cover the 2-element subsets
  have h1 : #(s.powersetCard 2) ≤ #P := by
    apply card_le_card_of_surjOn (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ))
    intro t ht
    rw [mem_coe, mem_powersetCard] at ht
    obtain ⟨hts, htc⟩ := ht
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp htc
    have hx : x ∈ s := hts (by simp)
    have hy : y ∈ s := hts (by simp)
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨(x, y), by simp [P, hx, hy, h], rfl⟩
    · exact ⟨(y, x), by simp [P, hx, hy, h], pair_comm _ _⟩
  -- their differences are distinct and lie in `1, …, max - min`
  have h2 : #P ≤ #(Icc 1 (s.max' hne - s.min' hne)) := by
    apply card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1)
    · intro p hp
      simp only [P, coe_filter, mem_product, Set.mem_ofPred_eq] at hp
      obtain ⟨⟨ha, hb⟩, hab⟩ := hp
      have := s.min'_le _ ha
      have := s.le_max' _ hb
      simp only [coe_Icc, Set.mem_Icc]
      omega
    · intro p hp q hq h
      simp only [P, coe_filter, mem_product, Set.mem_ofPred_eq] at hp hq
      obtain ⟨h1, h2⟩ := hg _ hp.1.1 _ hp.1.2 _ hq.1.1 _ hq.1.2 hp.2 hq.2 h
      exact Prod.ext h1 h2
  rw [card_powersetCard, hs, Nat.choose_two_right] at h1
  rw [Nat.card_Icc] at h2
  omega

theorem lower_1 : Golomb.LowerBound 1 0 := lower (n := 1) (by decide)
theorem lower_2 : Golomb.LowerBound 2 1 := lower (n := 2) (by decide)
theorem lower_3 : Golomb.LowerBound 3 3 := lower (n := 3) (by decide)
theorem lower_4 : Golomb.LowerBound 4 6 := lower (n := 4) (by decide)
theorem lower_5 : Golomb.LowerBound 5 10 := lower (n := 5) (by decide)
theorem lower_6 : Golomb.LowerBound 6 15 := lower (n := 6) (by decide)
theorem lower_7 : Golomb.LowerBound 7 21 := lower (n := 7) (by decide)
theorem lower_8 : Golomb.LowerBound 8 28 := lower (n := 8) (by decide)
theorem lower_9 : Golomb.LowerBound 9 36 := lower (n := 9) (by decide)
theorem lower_10 : Golomb.LowerBound 10 45 := lower (n := 10) (by decide)
theorem lower_11 : Golomb.LowerBound 11 55 := lower (n := 11) (by decide)
theorem lower_12 : Golomb.LowerBound 12 66 := lower (n := 12) (by decide)
theorem lower_13 : Golomb.LowerBound 13 78 := lower (n := 13) (by decide)
theorem lower_14 : Golomb.LowerBound 14 91 := lower (n := 14) (by decide)
theorem lower_15 : Golomb.LowerBound 15 105 := lower (n := 15) (by decide)
theorem lower_16 : Golomb.LowerBound 16 120 := lower (n := 16) (by decide)
theorem lower_17 : Golomb.LowerBound 17 136 := lower (n := 17) (by decide)
theorem lower_18 : Golomb.LowerBound 18 153 := lower (n := 18) (by decide)
theorem lower_19 : Golomb.LowerBound 19 171 := lower (n := 19) (by decide)
theorem lower_20 : Golomb.LowerBound 20 190 := lower (n := 20) (by decide)
theorem lower_21 : Golomb.LowerBound 21 210 := lower (n := 21) (by decide)
theorem lower_22 : Golomb.LowerBound 22 231 := lower (n := 22) (by decide)
theorem lower_23 : Golomb.LowerBound 23 253 := lower (n := 23) (by decide)
theorem lower_24 : Golomb.LowerBound 24 276 := lower (n := 24) (by decide)
theorem lower_25 : Golomb.LowerBound 25 300 := lower (n := 25) (by decide)
theorem lower_26 : Golomb.LowerBound 26 325 := lower (n := 26) (by decide)
theorem lower_27 : Golomb.LowerBound 27 351 := lower (n := 27) (by decide)
theorem lower_28 : Golomb.LowerBound 28 378 := lower (n := 28) (by decide)
theorem lower_29 : Golomb.LowerBound 29 406 := lower (n := 29) (by decide)
theorem lower_30 : Golomb.LowerBound 30 435 := lower (n := 30) (by decide)

end LeapsInBounds.Proofs.GolombCounting
