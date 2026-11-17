module

public import LeapsInBounds.Statements.DiskCovering
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The area bound for covering a disk with disks

`n` disks of radius `r` that cover the unit disk have total area `n π r²` at
least the area `π` of the unit disk, so `r ≥ 1 / √n`.
-/

public section

namespace LeapsInBounds.Proofs.DiskCoveringArea

open DiskCovering MeasureTheory

/-- `n` disks of radius `r` covering the unit disk have `1 ≤ n r²`, with `r ≥ 0`. -/
theorem one_le_of_covers {n : ℕ} {r : ℝ} {c : Fin n → Plane} (h : Covers r c) :
    0 ≤ r ∧ 1 ≤ (n : ℝ) * r ^ 2 := by
  have h0 : (0 : Plane) ∈ ⋃ i, Metric.closedBall (c i) r :=
    h (Metric.mem_closedBall_self zero_le_one)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h0
  have hr : 0 ≤ r := le_trans dist_nonneg (Metric.mem_closedBall.mp hi)
  refine ⟨hr, ?_⟩
  have hv := (measure_mono (μ := (volume : Measure Plane)) h).trans
    (measure_iUnion_fintype_le volume fun i => Metric.closedBall (c i) r)
  simp only [EuclideanSpace.volume_closedBall_fin_two, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_one, one_pow, one_mul] at hv
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hv
  have hpi := Real.pi_pos
  nlinarith

/-- `r(n) ≥ 1 / √n`, written as `√n / n`. -/
theorem lower (n : ℕ) (hn : 0 < n) : LowerBound n (Real.sqrt n / n) := by
  intro r c h
  obtain ⟨hr, h1⟩ := one_le_of_covers h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn', Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith

/-- `r(n) ≥ √n / n` as a `radical`. -/
theorem lower_radical (n : ℕ) (hn : 0 < n) : RadicalLowerBound n [(1, n)] n := by
  simpa [RadicalLowerBound, radical] using lower n hn

theorem lower_21 : RadicalLowerBound 21 [(1, 21)] 21 := lower_radical 21 (by norm_num)
theorem lower_22 : RadicalLowerBound 22 [(1, 22)] 22 := lower_radical 22 (by norm_num)
theorem lower_23 : RadicalLowerBound 23 [(1, 23)] 23 := lower_radical 23 (by norm_num)
theorem lower_24 : RadicalLowerBound 24 [(1, 6)] 12 := by
  have h := lower 24 (by norm_num)
  unfold RadicalLowerBound radical
  convert h using 1
  have : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 2 ^ 2 * 6 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  rw [this]
  ring

theorem lower_25 : RadicalLowerBound 25 [(1, 1)] 5 := by
  have h := lower 25 (by norm_num)
  unfold RadicalLowerBound radical
  convert h using 1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

end LeapsInBounds.Proofs.DiskCoveringArea
