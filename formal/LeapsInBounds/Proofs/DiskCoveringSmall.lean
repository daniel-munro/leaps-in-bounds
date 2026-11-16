module

public import LeapsInBounds.Statements.DiskCovering

/-!
# Optimal coverings of the unit disk with 2, 3, 4 and 7 disks

- `r(2) ≥ 1`: if the disks had radius `r < 1`, the two points `±q` of the
  unit circle perpendicular to the first center `c` are at distance
  `√(1 + ‖c‖²) ≥ 1` from it, so both lie in the second disk, which then has
  diameter at least 2.
- `r(3) ≤ √3 / 2`: disks centered at `u / 2` for the unit vectors `u` at
  angles 0°, 120° and 240°. A point `p` of the unit disk is within 60° of one
  of them, so `⟨p, u⟩ ≥ ‖p‖ / 2` and `‖p - u / 2‖² ≤ ‖p‖² - ‖p‖ / 2 + 1 / 4 ≤ 3 / 4`.
- `r(4) ≤ √2 / 2`: disks centered at `(±1/2, ±1/2)`, each the circumscribed
  disk of a quarter of the square `[-1, 1]²`.
- `r(7) ≤ 1 / 2`: one disk at the center, covering `‖p‖ ≤ 1 / 2`, and six at
  distance `√3 / 2` in the directions `u` at multiples of 60°. A point with
  `1 / 2 ≤ ‖p‖ ≤ 1` is within 30° of one of them, so `√3 ⟨p, u⟩ ≥ 3 ‖p‖ / 2`, and
  `‖p - (√3 / 2) u‖² ≤ ‖p‖² - 3 ‖p‖ / 2 + 3 / 4 ≤ 1 / 4`.

For the last two, the point is rotated so that the nearest direction `u` is
the first axis, and the bounds are proved for points `(x, y)` with
`√3 |y| ≤ 3 x` or `√3 |y| ≤ x`.
-/

public section

namespace LeapsInBounds.Proofs.DiskCoveringSmall

open DiskCovering

/-- The coordinates of a point of the closed unit disk. -/
lemma coords_of_mem {p : Plane} (hp : p ∈ Metric.closedBall (0 : Plane) 1) :
    p 0 ^ 2 + p 1 ^ 2 ≤ 1 := by
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two] at hp
  simp only [PiLp.zero_apply, Real.dist_eq, sub_zero, sq_abs] at hp
  have h0 : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (p 0 ^ 2 + p 1 ^ 2)]

/-- A point is in the closed disk of radius `r` about `(a, b)` if its squared
distance is at most `r²`. -/
lemma mem_of_coords {p : Plane} {a b r : ℝ} (hr : 0 ≤ r)
    (h : (p 0 - a) ^ 2 + (p 1 - b) ^ 2 ≤ r ^ 2) : p ∈ Metric.closedBall !₂[a, b] r := by
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  calc √((p 0 - a) ^ 2 + (p 1 - b) ^ 2) ≤ √(r ^ 2) := Real.sqrt_le_sqrt h
    _ = r := Real.sqrt_sq hr

/-- The squared distance from a point of a closed disk to its center. -/
lemma coords_of_mem_ball {p c : Plane} {r : ℝ} (hp : p ∈ Metric.closedBall c r) :
    (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 ≤ r ^ 2 ∧ 0 ≤ r := by
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two] at hp
  simp only [Real.dist_eq, sq_abs] at hp
  have h0 : 0 ≤ (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 := by positivity
  have hs := Real.sqrt_nonneg ((p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2)
  refine ⟨?_, hs.trans hp⟩
  nlinarith [Real.sq_sqrt h0]

lemma sqrt_three_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-! ## Two disks -/

/-- A unit vector perpendicular to `(a, b)`. -/
lemma exists_perp (a b : ℝ) : ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ u * a + v * b = 0 := by
  by_cases h : a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact ⟨1, 0, by norm_num, by simp [ha, hb]⟩
  · have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    set n := √(a ^ 2 + b ^ 2)
    have hn : 0 < n := Real.sqrt_pos.2 hpos
    have hn2 : n ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨-b / n, a / n, ?_, ?_⟩
    · rw [div_pow, div_pow, neg_sq, ← add_div, hn2, add_comm, div_self h]
    · field_simp; ring

/-- A point `(u, v)` with `u² + v² ≤ 1` is in the closed unit disk. -/
lemma mem_unit_of_coords {u v : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1) :
    !₂[u, v] ∈ Metric.closedBall (0 : Plane) 1 := by
  have : (0 : Plane) = !₂[0, 0] := by ext i; fin_cases i <;> simp
  rw [this]
  exact mem_of_coords zero_le_one (by simpa using h)

/-- `r(2) ≥ 1`. -/
theorem lower_two : RadicalLowerBound 2 [(1, 1)] 1 := by
  have hv : radical [(1, 1)] 1 = 1 := by simp [radical]
  rw [RadicalLowerBound, hv]
  intro r c hc
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, v, huv, hperp⟩ := exists_perp (c 0 0) (c 0 1)
  -- `±(u, v)` are too far from the first center, so both lie in the second disk
  have second (u v : ℝ) (huv : u ^ 2 + v ^ 2 = 1) (hperp : u * c 0 0 + v * c 0 1 = 0) :
      (u - c 1 0) ^ 2 + (v - c 1 1) ^ 2 ≤ r ^ 2 ∧ 0 ≤ r := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc (mem_unit_of_coords huv.le))
    have hi' := coords_of_mem_ball hi
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hi'
    fin_cases i
    · exfalso
      simp only [Fin.zero_eta, Fin.isValue] at hi'
      nlinarith [sq_nonneg (c 0 0), sq_nonneg (c 0 1)]
    · simpa using hi'
  obtain ⟨h1, hr⟩ := second u v huv hperp
  obtain ⟨h2, -⟩ := second (-u) (-v) (by linear_combination huv) (by linear_combination -hperp)
  nlinarith [sq_nonneg (c 1 0), sq_nonneg (c 1 1)]

/-! ## Three disks -/

/-- A point `(x, y)` of the unit disk with `√3 |y| ≤ 3 x` is within `√3 / 2` of
`(1 / 2, 0)`. -/
lemma three_sector {s x y : ℝ} (hs : s ^ 2 = 3) (h : x ^ 2 + y ^ 2 ≤ 1)
    (ha : 0 ≤ 3 * x - s * y) (hb : 0 ≤ 3 * x + s * y) :
    x ^ 2 + y ^ 2 - x + 1 / 4 ≤ 3 / 4 := by
  have hx : 0 ≤ x := by linarith
  have hsy : s ^ 2 * y ^ 2 = 3 * y ^ 2 := by rw [hs]
  have hy : y ^ 2 ≤ 3 * x ^ 2 := by nlinarith [mul_nonneg ha hb]
  rcases le_total x (1 / 2) with hx2 | hx2
  · nlinarith [mul_nonneg hx (sub_nonneg.2 hx2)]
  · nlinarith

/-- `r(3) ≤ √3 / 2`. -/
theorem upper_three : RadicalUpperBound 3 [(1, 3)] 2 := by
  have hv : radical [(1, 3)] 2 = √3 / 2 := by simp [radical]
  rw [RadicalUpperBound, hv]
  set s := √3 with hs_def
  have hs : s ^ 2 = 3 := sqrt_three_sq
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hr : 0 ≤ s / 2 := by positivity
  have hr2 : (s / 2) ^ 2 = 3 / 4 := by rw [div_pow, hs]; norm_num
  refine ⟨![!₂[1 / 2, 0], !₂[-1 / 4, s / 4], !₂[-1 / 4, -s / 4]], fun p hp => ?_⟩
  have h := coords_of_mem hp
  set x := p 0
  set y := p 1
  rw [Set.mem_iUnion]
  -- The sector at 240°, for `y ≤ 0` and `3 x ≤ -√3 y`
  have sector2 (hy : y ≤ 0) (hb : 0 ≤ -s * y - 3 * x) :
      p ∈ Metric.closedBall ((![!₂[1 / 2, 0], !₂[-1 / 4, s / 4], !₂[-1 / 4, -s / 4]] : Fin 3 → Plane) 2) (s / 2) := by
    refine mem_of_coords hr ?_
    have hsy : 0 ≤ -(s * y) := by nlinarith [mul_nonneg hs0 (neg_nonneg.2 hy)]
    have := three_sector (x := -x / 2 - s * y / 2) (y := s * x / 2 - y / 2) hs
      (by linear_combination h + ((x ^ 2 + y ^ 2) / 4) * hs)
      (by linear_combination hb + (x / 2) * hs) (by linear_combination 2 * hsy - (x / 2) * hs)
    rw [hr2]; linear_combination this + (-(4 * x ^ 2 + 4 * y ^ 2 - 1) / 16) * hs
  by_cases ha : 0 ≤ 3 * x - s * y
  · by_cases hb : 0 ≤ 3 * x + s * y
    · -- The sector at 0°
      refine ⟨0, mem_of_coords hr ?_⟩
      have := three_sector hs h ha hb
      rw [hr2]; linear_combination this
    · have hb' : 0 ≤ -s * y - 3 * x := by linarith
      have hy : y ≤ 0 := by nlinarith
      exact ⟨2, sector2 hy hb'⟩
  · have ha' : 0 ≤ s * y - 3 * x := by linarith
    rcases le_total 0 y with hy | hy
    · -- The sector at 120°
      refine ⟨1, mem_of_coords hr ?_⟩
      have hsy : 0 ≤ s * y := mul_nonneg hs0 hy
      have := three_sector (x := -x / 2 + s * y / 2) (y := -s * x / 2 - y / 2) hs
        (by linear_combination h + ((x ^ 2 + y ^ 2) / 4) * hs)
        (by linear_combination 2 * hsy - (x / 2) * hs) (by linear_combination ha' + (x / 2) * hs)
      rw [hr2]; linear_combination this + (-(4 * x ^ 2 + 4 * y ^ 2 - 1) / 16) * hs
    · have hsy : 0 ≤ -(s * y) := by nlinarith [mul_nonneg hs0 (neg_nonneg.2 hy)]
      exact ⟨2, sector2 hy (by linarith)⟩

/-! ## Four disks -/

/-- `r(4) ≤ √2 / 2`. -/
theorem upper_four : RadicalUpperBound 4 [(1, 2)] 2 := by
  have hv : radical [(1, 2)] 2 = √2 / 2 := by simp [radical]
  rw [RadicalUpperBound, hv]
  have hr : 0 ≤ √2 / 2 := by positivity
  have hr2 : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  refine ⟨![!₂[1 / 2, 1 / 2], !₂[-1 / 2, 1 / 2], !₂[-1 / 2, -1 / 2], !₂[1 / 2, -1 / 2]],
    fun p hp => ?_⟩
  have h := coords_of_mem hp
  set x := p 0
  set y := p 1
  have hx1 : x ^ 2 ≤ 1 := by nlinarith
  have hy1 : y ^ 2 ≤ 1 := by nlinarith
  have hx : |x| ≤ 1 := abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  have hy : |y| ≤ 1 := abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  rw [Set.mem_iUnion]
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · refine ⟨0, mem_of_coords hr ?_⟩
    rw [abs_of_nonneg hx0] at hx; rw [abs_of_nonneg hy0] at hy
    rw [hr2]; nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx), mul_nonneg hy0 (sub_nonneg.2 hy)]
  · refine ⟨3, mem_of_coords hr ?_⟩
    rw [abs_of_nonneg hx0] at hx; rw [abs_of_nonpos hy0] at hy
    rw [hr2]; nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx), mul_nonneg (neg_nonneg.2 hy0) (sub_nonneg.2 hy)]
  · refine ⟨1, mem_of_coords hr ?_⟩
    rw [abs_of_nonpos hx0] at hx; rw [abs_of_nonneg hy0] at hy
    rw [hr2]; nlinarith [mul_nonneg (neg_nonneg.2 hx0) (sub_nonneg.2 hx), mul_nonneg hy0 (sub_nonneg.2 hy)]
  · refine ⟨2, mem_of_coords hr ?_⟩
    rw [abs_of_nonpos hx0] at hx; rw [abs_of_nonpos hy0] at hy
    rw [hr2]; nlinarith [mul_nonneg (neg_nonneg.2 hx0) (sub_nonneg.2 hx),
      mul_nonneg (neg_nonneg.2 hy0) (sub_nonneg.2 hy)]

/-! ## Seven disks -/

/-- A point `(x, y)` with `1 / 2 ≤ ‖(x, y)‖ ≤ 1` and `√3 |y| ≤ x` is within
`1 / 2` of `(√3 / 2, 0)`. -/
lemma seven_sector {s x y : ℝ} (hs : s ^ 2 = 3) (hs0 : 0 ≤ s) (h1 : x ^ 2 + y ^ 2 ≤ 1)
    (h2 : 1 / 4 ≤ x ^ 2 + y ^ 2) (ha : 0 ≤ x - s * y) (hb : 0 ≤ x + s * y) :
    x ^ 2 + y ^ 2 - s * x + 3 / 4 ≤ 1 / 4 := by
  have hx : 0 ≤ x := by linarith
  have hsy : s ^ 2 * y ^ 2 = 3 * y ^ 2 := by rw [hs]
  have hy : 3 * y ^ 2 ≤ x ^ 2 := by nlinarith [mul_nonneg ha hb]
  set t := x ^ 2 + y ^ 2 with ht
  -- `(√3 x)² = 3 x² ≥ 9 t / 4 ≥ (t + 1 / 2)²`
  have hsx : (s * x) ^ 2 = 3 * x ^ 2 := by rw [mul_pow, hs]
  have hq : (t + 1 / 2) ^ 2 ≤ (s * x) ^ 2 := by
    rw [hsx]; nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  have hsx0 : 0 ≤ s * x := mul_nonneg hs0 hx
  have : t + 1 / 2 ≤ s * x := by
    nlinarith [sq_nonneg (t + 1 / 2 - s * x), sq_nonneg (t + 1 / 2 + s * x)]
  linarith

/-- The sector of one of the outer disks for `r(7) ≤ 1 / 2`, given the point's
coordinates `(X, Y)` rotated so that the disk's center is on the first axis. -/
lemma seven_case {s x y X Y cx cy : ℝ} (hs : s ^ 2 = 3) (hs0 : 0 ≤ s) (h1 : x ^ 2 + y ^ 2 ≤ 1)
    (h2 : 1 / 4 ≤ x ^ 2 + y ^ 2) (hN : X ^ 2 + Y ^ 2 = x ^ 2 + y ^ 2) (ha : 0 ≤ X - s * Y)
    (hb : 0 ≤ X + s * Y) (hD : (x - cx) ^ 2 + (y - cy) ^ 2 = X ^ 2 + Y ^ 2 - s * X + 3 / 4) :
    (x - cx) ^ 2 + (y - cy) ^ 2 ≤ (1 / 2) ^ 2 := by
  have := seven_sector hs hs0 (hN ▸ h1) (hN ▸ h2) ha hb
  rw [hD]; linarith

/-- `r(7) ≤ 1 / 2`. -/
theorem upper_seven : RadicalUpperBound 7 [(1, 1)] 2 := by
  have hv : radical [(1, 1)] 2 = 1 / 2 := by simp [radical]
  rw [RadicalUpperBound, hv]
  set s := √3 with hs_def
  have hs : s ^ 2 = 3 := sqrt_three_sq
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 3
  have hr : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨![!₂[0, 0], !₂[s / 2, 0], !₂[s / 4, 3 / 4], !₂[-s / 4, 3 / 4], !₂[-s / 2, 0],
    !₂[-s / 4, -3 / 4], !₂[s / 4, -3 / 4]], fun p hp => ?_⟩
  have h := coords_of_mem hp
  set x := p 0
  set y := p 1
  rw [Set.mem_iUnion]
  by_cases hc : x ^ 2 + y ^ 2 ≤ 1 / 4
  · exact ⟨0, mem_of_coords hr (by linear_combination hc)⟩
  have h2 : 1 / 4 ≤ x ^ 2 + y ^ 2 := by linarith
  rcases le_total 0 x with hx | hx
  · by_cases ha : 0 ≤ x - s * y
    · by_cases hb : 0 ≤ x + s * y
      · -- 0°
        exact ⟨1, mem_of_coords hr (seven_case (X := x) (Y := y) hs hs0 h h2 rfl ha hb
          (by linear_combination (1 / 4) * hs))⟩
      · -- 300°
        have hb' : 0 ≤ -s * y - x := by linarith
        exact ⟨6, mem_of_coords hr (seven_case (X := (x - s * y) / 2) (Y := (s * x + y) / 2)
          hs hs0 h h2 (by linear_combination ((x ^ 2 + y ^ 2) / 4) * hs)
          (by linear_combination hb' + (x / 2) * hs) (by linear_combination 2 * hx - (x / 2) * hs)
          (by linear_combination (-(4 * x ^ 2 + 4 * y ^ 2 + 8 * y - 1) / 16) * hs))⟩
    · -- 60°
      have ha' : 0 ≤ s * y - x := by linarith
      exact ⟨2, mem_of_coords hr (seven_case (X := (x + s * y) / 2) (Y := -(s * x - y) / 2)
        hs hs0 h h2 (by linear_combination ((x ^ 2 + y ^ 2) / 4) * hs)
        (by linear_combination 2 * hx - (x / 2) * hs) (by linear_combination ha' + (x / 2) * hs)
        (by linear_combination (-(4 * x ^ 2 + 4 * y ^ 2 - 8 * y - 1) / 16) * hs))⟩
  · have hx' : 0 ≤ -x := by linarith
    by_cases hb : 0 ≤ x + s * y
    · -- 120°
      exact ⟨3, mem_of_coords hr (seven_case (X := -(x - s * y) / 2) (Y := -(s * x + y) / 2)
        hs hs0 h h2 (by linear_combination ((x ^ 2 + y ^ 2) / 4) * hs)
        (by linear_combination hb - (x / 2) * hs) (by linear_combination 2 * hx' + (x / 2) * hs)
        (by linear_combination (-(4 * x ^ 2 + 4 * y ^ 2 - 8 * y - 1) / 16) * hs))⟩
    · have hb' : 0 ≤ -s * y - x := by linarith
      by_cases ha : 0 ≤ x - s * y
      · -- 240°
        exact ⟨5, mem_of_coords hr (seven_case (X := -(x + s * y) / 2) (Y := (s * x - y) / 2)
          hs hs0 h h2 (by linear_combination ((x ^ 2 + y ^ 2) / 4) * hs)
          (by linear_combination 2 * hx' + (x / 2) * hs) (by linear_combination ha - (x / 2) * hs)
          (by linear_combination (-(4 * x ^ 2 + 4 * y ^ 2 + 8 * y - 1) / 16) * hs))⟩
      · -- 180°
        have ha' : 0 ≤ s * y - x := by linarith
        exact ⟨4, mem_of_coords hr (seven_case (X := -x) (Y := -y) hs hs0 h h2 (by ring)
          (by linear_combination ha') (by linear_combination hb')
          (by linear_combination (1 / 4) * hs))⟩

end LeapsInBounds.Proofs.DiskCoveringSmall
