module

public import LeapsInBounds.Statements.DiskCovering

/-!
# Covering the unit disk with one or two disks

`r(1) = 1`: the unit disk covers itself, and a disk of radius `r` covering the
unit disk contains two opposite points `p` and `-p` of the unit circle, so
`2 r² ≥ ‖p - c‖² + ‖p + c‖² = 2 + 2 ‖c‖² ≥ 2`. And `r(2) ≤ 1`, since one of
the two disks can be the unit disk.
-/

public section

namespace LeapsInBounds.Proofs.DiskCoveringOne

open DiskCovering

private lemma radical_one : radical [(1, 1)] 1 = 1 := by
  simp [radical]

/-- `r(1) ≤ 1`. -/
theorem upper_one : RadicalUpperBound 1 [(1, 1)] 1 := by
  rw [RadicalUpperBound, radical_one]
  refine ⟨fun _ => 0, fun p hp => Set.mem_iUnion.mpr ⟨0, hp⟩⟩

/-- `r(2) ≤ 1`. -/
theorem upper_two : RadicalUpperBound 2 [(1, 1)] 1 := by
  rw [RadicalUpperBound, radical_one]
  refine ⟨fun _ => 0, fun p hp => Set.mem_iUnion.mpr ⟨0, hp⟩⟩

/-- `r(1) ≥ 1`. -/
theorem lower_one : RadicalLowerBound 1 [(1, 1)] 1 := by
  rw [RadicalLowerBound, radical_one]
  intro r c hc
  set p : Plane := EuclideanSpace.single 0 1
  have hp : ‖p‖ = 1 := by simp [p]
  have mem : ∀ q : Plane, ‖q‖ = 1 → ‖q - c 0‖ ≤ r := by
    intro q hq
    have : q ∈ Metric.closedBall (0 : Plane) 1 := by simp [hq]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc this)
    rw [Fin.fin_one_eq_zero i, Metric.mem_closedBall, dist_eq_norm] at hi
    exact hi
  have h1 := mem p hp
  have h2 := mem (-p) (by simpa using hp)
  have hr : 0 ≤ r := (norm_nonneg _).trans h1
  have e1 := norm_sub_sq_real p (c 0)
  have e2 := norm_sub_sq_real (-p) (c 0)
  rw [inner_neg_left, norm_neg] at e2
  have s1 : ‖p - c 0‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have s2 : ‖-p - c 0‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [sq_nonneg ‖c 0‖]

end LeapsInBounds.Proofs.DiskCoveringOne
