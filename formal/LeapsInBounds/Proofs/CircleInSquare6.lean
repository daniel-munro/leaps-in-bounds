module

public import LeapsInBounds.Statements.CircleInSquare

/-!
# Lower bound for packing 6 unit circles in a square

Proves `s(6) ≥ 2 + 12√13 / 13` (`RadicalLowerBound 6 [(26, 1), (12, 13)] 13`).
Rescaling a strictly smaller packing of 6 unit circles into `[0, 6]²` gives
pairwise squared distances strictly greater than `13`. This forces bijections
with both the `2 × 3` (`3 × 2` cell) and `3 × 2` (`2 × 3` cell) grids,
excludes all grid boundary lines, and leaves only two `4 × 4` micro-cell
patterns up to square symmetry. The boundary-cycle pattern is refuted by a
single exact nonnegative polynomial identity on a weighted edge sum, and the
centered pattern (with WLOG `x₃ ≤ y₃`) is refuted using three rational circular-arc
secants.
-/

public section

namespace LeapsInBounds.Proofs.CircleInSquare6

open CircleInSquare

private lemma add_mem_closedBall (p : Plane) {u v : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1) :
    p + !₂[u, v] ∈ Metric.closedBall p 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq]
  simpa [Fin.sum_univ_two] using h

private lemma center_bounds {s : ℝ} {p : Plane} (h : Metric.closedBall p 1 ⊆ square s) :
    1 ≤ p 0 ∧ p 0 ≤ s - 1 ∧ 1 ≤ p 1 ∧ p 1 ≤ s - 1 := by
  have h1 := h (add_mem_closedBall p (u := -1) (v := 0) (by norm_num))
  have h2 := h (add_mem_closedBall p (u := 1) (v := 0) (by norm_num))
  have h3 := h (add_mem_closedBall p (u := 0) (v := -1) (by norm_num))
  have h4 := h (add_mem_closedBall p (u := 0) (v := 1) (by norm_num))
  simp only [square, Set.mem_ofPred_eq, PiLp.add_apply] at h1 h2 h3 h4
  simp at h1 h2 h3 h4
  refine ⟨by linarith [h1.1], by linarith [h2.2.1], by linarith [h3.2.2.1], by linarith [h4.2.2.2]⟩

private lemma four_le_dist_sq {n : ℕ} {s : ℝ} {c : Fin n → Plane} (h : IsPacking s c)
    {i j : Fin n} (hij : i ≠ j) :
    4 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 := by
  have h2 := (disjoint_ball_ball_iff one_pos one_pos).1 (h.2.2 i j hij)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at h2
  nlinarith [Real.sq_sqrt (show 0 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 by positivity)]

private noncomputable def half (t : ℝ) : Fin 2 :=
  if t < 3 then 0 else 1

private noncomputable def third (t : ℝ) : Fin 3 :=
  if t < 2 then 0 else if t < 4 then 1 else 2

private noncomputable def cellA (x y : Fin 6 → ℝ) (i : Fin 6) : Fin 2 × Fin 3 :=
  (half (x i), third (y i))

private noncomputable def cellB (x y : Fin 6 → ℝ) (i : Fin 6) : Fin 3 × Fin 2 :=
  (third (x i), half (y i))

private lemma sq_le_of_mem_Icc {u v l r : ℝ} (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) :
    (u - v) ^ 2 ≤ (r - l) ^ 2 := by
  nlinarith only [mul_nonneg (show 0 ≤ (r - l) - (u - v) by linarith)
                             (show 0 ≤ (r - l) + (u - v) by linarith)]

private lemma half_bounds {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 6) :
    (half u = 0 → 0 ≤ u ∧ u < 3) ∧ (half u = 1 → 3 ≤ u ∧ u ≤ 6) := by
  unfold half
  split_ifs with h
  · exact ⟨fun _ => ⟨hu.1, h⟩, fun h01 => by contradiction⟩
  · exact ⟨fun h10 => by contradiction, fun _ => ⟨le_of_not_gt h, hu.2⟩⟩

private lemma third_bounds {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 6) :
    (third u = 0 → 0 ≤ u ∧ u < 2) ∧
    (third u = 1 → 2 ≤ u ∧ u < 4) ∧
    (third u = 2 → 4 ≤ u ∧ u ≤ 6) := by
  unfold third
  split_ifs with h1 h2
  · exact ⟨fun _ => ⟨hu.1, h1⟩, fun h => by contradiction, fun h => by contradiction⟩
  · exact ⟨fun h => by contradiction, fun _ => ⟨le_of_not_gt h1, h2⟩, fun h => by contradiction⟩
  · exact ⟨fun h => by contradiction, fun h => by contradiction, fun _ => ⟨le_of_not_gt h2, hu.2⟩⟩

private lemma half_sq_le {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 6) (hv : 0 ≤ v ∧ v ≤ 6)
    (heq : half u = half v) : (u - v) ^ 2 ≤ 9 := by
  have h : half u = 0 ∨ half u = 1 := by unfold half; split_ifs <;> simp
  rcases h with h | h
  · have hu' := (half_bounds hu).1 h
    have hv' := (half_bounds hv).1 (heq.symm.trans h)
    nlinarith only [sq_le_of_mem_Icc ⟨hu'.1, hu'.2.le⟩ ⟨hv'.1, hv'.2.le⟩]
  · have hu' := (half_bounds hu).2 h
    have hv' := (half_bounds hv).2 (heq.symm.trans h)
    nlinarith only [sq_le_of_mem_Icc hu' hv']

private lemma third_sq_le {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 6) (hv : 0 ≤ v ∧ v ≤ 6)
    (heq : third u = third v) : (u - v) ^ 2 ≤ 4 := by
  have h : third u = 0 ∨ third u = 1 ∨ third u = 2 := by unfold third; split_ifs <;> simp
  rcases h with h | h | h
  · have hu' := (third_bounds hu).1 h
    have hv' := (third_bounds hv).1 (heq.symm.trans h)
    nlinarith only [sq_le_of_mem_Icc ⟨hu'.1, hu'.2.le⟩ ⟨hv'.1, hv'.2.le⟩]
  · have hu' := (third_bounds hu).2.1 h
    have hv' := (third_bounds hv).2.1 (heq.symm.trans h)
    nlinarith only [sq_le_of_mem_Icc ⟨hu'.1, hu'.2.le⟩ ⟨hv'.1, hv'.2.le⟩]
  · have hu' := (third_bounds hu).2.2 h
    have hv' := (third_bounds hv).2.2 (heq.symm.trans h)
    nlinarith only [sq_le_of_mem_Icc hu' hv']

private lemma cellA_inj {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) :
    Function.Injective (cellA x y) := by
  intro i j hij
  by_contra hne
  simp only [cellA, Prod.mk.injEq] at hij
  have hx9 := half_sq_le (hx i) (hx j) hij.1
  have hy4 := third_sq_le (hy i) (hy j) hij.2
  linarith [hsep i j hne]

private lemma cellA_bij {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) :
    Function.Bijective (cellA x y) :=
  (Fintype.bijective_iff_injective_and_card (cellA x y)).2 ⟨cellA_inj hx hy hsep, by decide⟩

private lemma cellB_inj {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) :
    Function.Injective (cellB x y) := by
  have hsep' : ∀ i j, i ≠ j → 13 < (y i - y j) ^ 2 + (x i - x j) ^ 2 := fun i j hij => by
    linarith [hsep i j hij]
  intro i j hij
  apply cellA_inj hy hx hsep'
  simp only [cellB, Prod.mk.injEq] at hij
  simp only [cellA, Prod.mk.injEq]
  exact ⟨hij.2, hij.1⟩

private lemma gridA_no_boundary {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) (i : Fin 6) :
    x i ≠ 3 ∧ y i ≠ 2 ∧ y i ≠ 4 := by
  have hbij := cellA_bij hx hy hsep
  refine ⟨?_, ?_, ?_⟩
  · intro hxi
    obtain ⟨j, hj⟩ := hbij.2 (0, third (y i))
    simp only [cellA, Prod.mk.injEq] at hj
    have hne : i ≠ j := by
      intro heq
      subst heq
      have h0 : half (x i) = 0 := hj.1
      have := (half_bounds (hx i)).1 h0
      linarith
    have hxj := (half_bounds (hx j)).1 hj.1
    have hx9 : (x i - x j) ^ 2 ≤ 9 := by
      have := sq_le_of_mem_Icc (u := x i) (v := x j) (l := 0) (r := 3)
        ⟨(hx i).1, hxi.le⟩ ⟨hxj.1, hxj.2.le⟩
      nlinarith
    have hy4 : (y i - y j) ^ 2 ≤ 4 := third_sq_le (hy i) (hy j) hj.2.symm
    linarith [hsep i j hne]
  · intro hyi
    obtain ⟨j, hj⟩ := hbij.2 (half (x i), 0)
    simp only [cellA, Prod.mk.injEq] at hj
    have hne : i ≠ j := by
      intro heq
      subst heq
      have h0 : third (y i) = 0 := hj.2
      have := (third_bounds (hy i)).1 h0
      linarith
    have hyj := (third_bounds (hy j)).1 hj.2
    have hx9 : (x i - x j) ^ 2 ≤ 9 := half_sq_le (hx i) (hx j) hj.1.symm
    have hy4 : (y i - y j) ^ 2 ≤ 4 := by
      have := sq_le_of_mem_Icc (u := y i) (v := y j) (l := 0) (r := 2)
        ⟨(hy i).1, hyi.le⟩ ⟨hyj.1, hyj.2.le⟩
      nlinarith
    linarith [hsep i j hne]
  · intro hyi
    obtain ⟨j, hj⟩ := hbij.2 (half (x i), 1)
    simp only [cellA, Prod.mk.injEq] at hj
    have hne : i ≠ j := by
      intro heq
      subst heq
      have h1 : third (y i) = 1 := hj.2
      have := (third_bounds (hy i)).2.1 h1
      linarith
    have hyj := (third_bounds (hy j)).2.1 hj.2
    have hx9 : (x i - x j) ^ 2 ≤ 9 := half_sq_le (hx i) (hx j) hj.1.symm
    have hy4 : (y i - y j) ^ 2 ≤ 4 := by
      have := sq_le_of_mem_Icc (u := y i) (v := y j) (l := 2) (r := 4)
        ⟨by linarith, hyi.le⟩ ⟨hyj.1, hyj.2.le⟩
      nlinarith
    linarith [hsep i j hne]

private lemma no_boundary {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) (i : Fin 6) :
    x i ≠ 2 ∧ x i ≠ 3 ∧ x i ≠ 4 ∧ y i ≠ 2 ∧ y i ≠ 3 ∧ y i ≠ 4 := by
  have hA := gridA_no_boundary hx hy hsep i
  have hsep' : ∀ a b, a ≠ b → 13 < (y a - y b) ^ 2 + (x a - x b) ^ 2 := fun a b hab => by
    linarith [hsep a b hab]
  have hB := gridA_no_boundary hy hx hsep' i
  exact ⟨hB.2.1, hA.1, hB.2.2, hA.2.1, hB.1, hA.2.2⟩

private lemma pattern1_coord_bound {u0 u1 u2 u3 u4 u5 : ℝ}
    (h0 : 2 ≤ u0 ∧ u0 ≤ 3) (h1 : 4 ≤ u1 ∧ u1 ≤ 6) (h2 : 0 ≤ u2 ∧ u2 ≤ 2)
    (h3 : 4 ≤ u3 ∧ u3 ≤ 6) (h4 : 0 ≤ u4 ∧ u4 ≤ 2) (h5 : 3 ≤ u5 ∧ u5 ≤ 4) :
    (u1 - u0) ^ 2 + (u0 - u2) ^ 2 + 2 * (u3 - u1) ^ 2 +
        (u4 - u2) ^ 2 + 3 * (u3 - u5) ^ 2 + 2 * (u5 - u4) ^ 2 ≤ 65 := by
  have hid :
      65 - ((u1 - u0) ^ 2 + (u0 - u2) ^ 2 + 2 * (u3 - u1) ^ 2 +
            (u4 - u2) ^ 2 + 3 * (u3 - u5) ^ 2 + 2 * (u5 - u4) ^ 2) =
        2 * (u0 - 2) * (3 - u0) + 3 * (u1 - 4) * (6 - u1) + 2 * u2 * (2 - u2)
          + 5 * (u3 - 4) * (6 - u3) + 3 * u4 * (2 - u4) + 5 * (u5 - 3) * (4 - u5)
          + (u0 - 2) * (u1 - 4) + (3 - u0) * (6 - u1) + 2 * (u0 - 2) * u2
          + 4 * (6 - u1) * (6 - u3) + 2 * u2 * u4 + 6 * (6 - u3) * (4 - u5)
          + 4 * u4 * (u5 - 3) + (6 - u1) + 2 * (6 - u3) + 6 * u4 + (u5 - 3) := by
    ring
  have hnonneg :
      0 ≤ 2 * (u0 - 2) * (3 - u0) + 3 * (u1 - 4) * (6 - u1) + 2 * u2 * (2 - u2)
        + 5 * (u3 - 4) * (6 - u3) + 3 * u4 * (2 - u4) + 5 * (u5 - 3) * (4 - u5)
        + (u0 - 2) * (u1 - 4) + (3 - u0) * (6 - u1) + 2 * (u0 - 2) * u2
        + 4 * (6 - u1) * (6 - u3) + 2 * u2 * u4 + 6 * (6 - u3) * (4 - u5)
        + 4 * u4 * (u5 - 3) + (6 - u1) + 2 * (6 - u3) + 6 * u4 + (u5 - 3) := by
    nlinarith only [
      mul_nonneg (show 0 ≤ u0 - 2 by linarith) (show 0 ≤ 3 - u0 by linarith),
      mul_nonneg (show 0 ≤ u1 - 4 by linarith) (show 0 ≤ 6 - u1 by linarith),
      mul_nonneg (show 0 ≤ u2 by linarith) (show 0 ≤ 2 - u2 by linarith),
      mul_nonneg (show 0 ≤ u3 - 4 by linarith) (show 0 ≤ 6 - u3 by linarith),
      mul_nonneg (show 0 ≤ u4 by linarith) (show 0 ≤ 2 - u4 by linarith),
      mul_nonneg (show 0 ≤ u5 - 3 by linarith) (show 0 ≤ 4 - u5 by linarith),
      mul_nonneg (show 0 ≤ u0 - 2 by linarith) (show 0 ≤ u1 - 4 by linarith),
      mul_nonneg (show 0 ≤ 3 - u0 by linarith) (show 0 ≤ 6 - u1 by linarith),
      mul_nonneg (show 0 ≤ u0 - 2 by linarith) (show 0 ≤ u2 by linarith),
      mul_nonneg (show 0 ≤ 6 - u1 by linarith) (show 0 ≤ 6 - u3 by linarith),
      mul_nonneg (show 0 ≤ u2 by linarith) (show 0 ≤ u4 by linarith),
      mul_nonneg (show 0 ≤ 6 - u3 by linarith) (show 0 ≤ 4 - u5 by linarith),
      mul_nonneg (show 0 ≤ u4 by linarith) (show 0 ≤ u5 - 3 by linarith),
      h1.2, h3.2, h4.1, h5.1]
  linarith

private lemma pattern1_contradiction {x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 : ℝ}
    (hx0 : 2 ≤ x0 ∧ x0 ≤ 3) (hy0 : 0 ≤ y0 ∧ y0 ≤ 2)
    (hx1 : 4 ≤ x1 ∧ x1 ≤ 6) (hy1 : 0 ≤ y1 ∧ y1 ≤ 2)
    (hx2 : 0 ≤ x2 ∧ x2 ≤ 2) (hy2 : 2 ≤ y2 ∧ y2 ≤ 3)
    (hx3 : 4 ≤ x3 ∧ x3 ≤ 6) (hy3 : 3 ≤ y3 ∧ y3 ≤ 4)
    (hx4 : 0 ≤ x4 ∧ x4 ≤ 2) (hy4 : 4 ≤ y4 ∧ y4 ≤ 6)
    (hx5 : 3 ≤ x5 ∧ x5 ≤ 4) (hy5 : 4 ≤ y5 ∧ y5 ≤ 6)
    (h01 : 13 < (x0 - x1) ^ 2 + (y0 - y1) ^ 2)
    (h02 : 13 < (x0 - x2) ^ 2 + (y0 - y2) ^ 2)
    (h13 : 13 < (x1 - x3) ^ 2 + (y1 - y3) ^ 2)
    (h24 : 13 < (x2 - x4) ^ 2 + (y2 - y4) ^ 2)
    (h35 : 13 < (x3 - x5) ^ 2 + (y3 - y5) ^ 2)
    (h45 : 13 < (x4 - x5) ^ 2 + (y4 - y5) ^ 2) : False := by
  have bx := pattern1_coord_bound hx0 hx1 hx2 hx3 hx4 hx5
  have by' := pattern1_coord_bound hy2 hy4 hy0 hy5 hy1 hy3
  linarith

private lemma secant_e2_lo {X Y : ℝ} (hX1 : 2 ≤ X) (hX2 : X ≤ 5 / 2) (hY : 0 ≤ Y)
    (hgt : 13 < X ^ 2 + Y ^ 2) : 28 < 5 * X + 6 * Y := by
  by_contra! hle
  have hYsq : 36 * Y ^ 2 ≤ (28 - 5 * X) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (28 - 5 * X) - 6 * Y by linarith)
                               (show 0 ≤ (28 - 5 * X) + 6 * Y by linarith)]
  have hpoly : 36 * X ^ 2 + (28 - 5 * X) ^ 2 - 468 = (X - 2) * (61 * X - 158) := by ring
  have hle0 : (X - 2) * (61 * X - 158) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith

private lemma secant_left {X Y : ℝ} (hX1 : 5 / 2 ≤ X) (hX2 : X ≤ 3) (hY : 0 ≤ Y)
    (hgt : 13 < X ^ 2 + Y ^ 2) : 33 < 7 * X + 6 * Y := by
  by_contra! hle
  have hYsq : 36 * Y ^ 2 ≤ (33 - 7 * X) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (33 - 7 * X) - 6 * Y by linarith)
                               (show 0 ≤ (33 - 7 * X) + 6 * Y by linarith)]
  have hpoly : 36 * X ^ 2 + (33 - 7 * X) ^ 2 - 468 = (X - 3) * (85 * X - 207) := by ring
  have hle0 : (X - 3) * (85 * X - 207) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

private lemma secant_right {X Y : ℝ} (hX1 : 3 ≤ X) (hX2 : X ≤ 7 / 2) (hY : 0 ≤ Y)
    (hgt : 13 < X ^ 2 + Y ^ 2) : 27 < 7 * X + 3 * Y := by
  by_contra! hle
  have hYsq : 9 * Y ^ 2 ≤ (27 - 7 * X) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (27 - 7 * X) - 3 * Y by linarith)
                               (show 0 ≤ (27 - 7 * X) + 3 * Y by linarith)]
  have hpoly : 9 * X ^ 2 + (27 - 7 * X) ^ 2 - 117 = 2 * (X - 3) * (29 * X - 102) := by ring
  have hle0 : 2 * (X - 3) * (29 * X - 102) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith

private lemma pattern2_ordered_contradiction {x0 y0 x1 y1 x2 y2 x3 y3 x5 y5 : ℝ}
    (hx0 : 2 ≤ x0 ∧ x0 ≤ 3) (hy0 : 0 ≤ y0 ∧ y0 ≤ 2)
    (hx1 : 4 ≤ x1 ∧ x1 ≤ 6) (hy1 : 0 ≤ y1 ∧ y1 ≤ 2)
    (hx2 : 0 ≤ x2 ∧ x2 ≤ 2) (hy2 : 2 ≤ y2 ∧ y2 ≤ 3)
    (hx3 : 3 ≤ x3 ∧ x3 ≤ 4) (hy3 : 3 ≤ y3 ∧ y3 ≤ 4)
    (hx5 : 4 ≤ x5 ∧ x5 ≤ 6) (hy5 : 4 ≤ y5 ∧ y5 ≤ 6)
    (hxy3 : x3 ≤ y3)
    (h01 : 13 < (x0 - x1) ^ 2 + (y0 - y1) ^ 2)
    (h02 : 13 < (x0 - x2) ^ 2 + (y0 - y2) ^ 2)
    (h13 : 13 < (x1 - x3) ^ 2 + (y1 - y3) ^ 2)
    (h23 : 13 < (x2 - x3) ^ 2 + (y2 - y3) ^ 2)
    (h35 : 13 < (x3 - x5) ^ 2 + (y3 - y5) ^ 2) : False := by
  have e1 : 13 < (6 - x0) ^ 2 + (y1 - y0) ^ 2 := by
    have : (x0 - x1) ^ 2 ≤ (6 - x0) ^ 2 := by
      have := sq_le_of_mem_Icc (u := x0) (v := x1) (l := x0) (r := 6) ⟨le_rfl, by linarith⟩ ⟨by linarith, hx1.2⟩
      nlinarith
    linarith
  have e2 : 13 < x0 ^ 2 + (y2 - y0) ^ 2 := by
    have : (x0 - x2) ^ 2 ≤ x0 ^ 2 := by
      have := sq_le_of_mem_Icc (u := x0) (v := x2) (l := 0) (r := x0) ⟨hx0.1.trans' (by norm_num), le_rfl⟩ ⟨hx2.1, by linarith⟩
      nlinarith
    linarith
  have e3 : 13 < (6 - x3) ^ 2 + (y3 - y1) ^ 2 := by
    have : (x1 - x3) ^ 2 ≤ (6 - x3) ^ 2 := by
      have := sq_le_of_mem_Icc (u := x1) (v := x3) (l := x3) (r := 6) ⟨by linarith, hx1.2⟩ ⟨le_rfl, by linarith⟩
      nlinarith
    linarith
  have e4 : 13 < x3 ^ 2 + (y3 - y2) ^ 2 := by
    have : (x2 - x3) ^ 2 ≤ x3 ^ 2 := by
      have := sq_le_of_mem_Icc (u := x2) (v := x3) (l := 0) (r := x3) ⟨hx2.1, by linarith⟩ ⟨hx3.1.trans' (by norm_num), le_rfl⟩
      nlinarith
    linarith
  have e5 : 13 < (6 - x3) ^ 2 + (6 - y3) ^ 2 := by
    have hx35 : (x3 - x5) ^ 2 ≤ (6 - x3) ^ 2 := by
      have := sq_le_of_mem_Icc (u := x3) (v := x5) (l := x3) (r := 6) ⟨le_rfl, by linarith⟩ ⟨by linarith, hx5.2⟩
      nlinarith
    have hy35 : (y3 - y5) ^ 2 ≤ (6 - y3) ^ 2 := by
      have := sq_le_of_mem_Icc (u := y3) (v := y5) (l := y3) (r := 6) ⟨le_rfl, by linarith⟩ ⟨by linarith, hy5.2⟩
      nlinarith
    linarith
  have hx3_hi : x3 ≤ 7 / 2 := by
    by_contra! hgt
    have : (6 - y3) ^ 2 ≤ (6 - x3) ^ 2 := by
      nlinarith only [mul_nonneg (show 0 ≤ (6 - x3) - (6 - y3) by linarith)
                                 (show 0 ≤ (6 - x3) + (6 - y3) by linarith)]
    have h6x : (6 - x3) ^ 2 < (5 / 2) ^ 2 := by
      nlinarith only [mul_pos (show 0 < 5 / 2 - (6 - x3) by linarith)
                              (show 0 < 5 / 2 + (6 - x3) by linarith)]
    linarith
  have h6x3_lo : 5 / 2 ≤ 6 - x3 := by linarith only [hx3_hi]
  have h6x3_hi : 6 - x3 ≤ 3 := by linarith only [hx3.1]
  have h6y3_nn : 0 ≤ 6 - y3 := by linarith only [hy3.2]
  have hy32_nn : 0 ≤ y3 - y2 := by linarith only [hy2.2, hy3.1]
  have s5 : 33 < 7 * (6 - x3) + 6 * (6 - y3) :=
    secant_left h6x3_lo h6x3_hi h6y3_nn e5
  have s4 : 27 < 7 * x3 + 3 * (y3 - y2) :=
    secant_right hx3.1 hx3_hi hy32_nn e4
  rcases le_total x0 (5 / 2) with hx0_lo | hx0_hi
  · have hy20_nn : 0 ≤ y2 - y0 := by linarith only [hy0.2, hy2.1]
    have s2 : 28 < 5 * x0 + 6 * (y2 - y0) :=
      secant_e2_lo hx0.1 hx0_lo hy20_nn e2
    linarith only [s2, s4, s5, hxy3, hx0_lo, hy0.1]
  · have hy20_nn : 0 ≤ y2 - y0 := by linarith only [hy0.2, hy2.1]
    have s2 : 33 < 7 * x0 + 6 * (y2 - y0) :=
      secant_left hx0_hi hx0.2 hy20_nn e2
    have h6x0_lo : 3 ≤ 6 - x0 := by linarith only [hx0.2]
    have h6x0_hi : 6 - x0 ≤ 7 / 2 := by linarith only [hx0_hi]
    rcases le_total y0 y1 with hy01 | hy10
    · have hy10_nn : 0 ≤ y1 - y0 := by linarith only [hy01]
      have hy31_nn : 0 ≤ y3 - y1 := by linarith only [hy1.2, hy3.1]
      have s1 : 27 < 7 * (6 - x0) + 3 * (y1 - y0) :=
        secant_right h6x0_lo h6x0_hi hy10_nn e1
      have s3 : 33 < 7 * (6 - x3) + 6 * (y3 - y1) :=
        secant_left h6x3_lo h6x3_hi hy31_nn e3
      linarith only [s1, s2, s3, s4, s5, hy0.1]
    · have hy01_nn : 0 ≤ y0 - y1 := by linarith only [hy10]
      have e1' : 13 < (6 - x0) ^ 2 + (y0 - y1) ^ 2 := by
        have hsq : (y0 - y1) ^ 2 = (y1 - y0) ^ 2 := by ring
        linarith only [e1, hsq]
      have s1' : 27 < 7 * (6 - x0) + 3 * (y0 - y1) :=
        secant_right h6x0_lo h6x0_hi hy01_nn e1'
      linarith only [s1', s2, s4, s5, hy1.1, hx0_hi, hx3_hi]

private def inCenter (x y : Fin 6 → ℝ) (i : Fin 6) : Prop :=
  2 < x i ∧ x i < 4 ∧ 2 < y i ∧ y i < 4

private lemma branch1_oriented {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2)
    (hnc : ∀ k, ¬ inCenter x y k)
    (hk : ∃ k, x k < 2 ∧ 2 < y k ∧ y k < 3) : False := by
  have hbij := cellA_bij hx hy hsep
  have hinjB := cellB_inj hx hy hsep
  let a := (Equiv.ofBijective (cellA x y) hbij).symm
  let p0 := a (0, 0)
  let p1 := a (1, 0)
  let p2 := a (0, 1)
  let p3 := a (1, 1)
  let p4 := a (0, 2)
  let p5 := a (1, 2)
  have ca0 : cellA x y p0 = (0, 0) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca1 : cellA x y p1 = (1, 0) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca2 : cellA x y p2 = (0, 1) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca3 : cellA x y p3 = (1, 1) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca4 : cellA x y p4 = (0, 2) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca5 : cellA x y p5 = (1, 2) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  simp only [cellA, Prod.mk.injEq] at ca0 ca1 ca2 ca3 ca4 ca5
  have x0_lt3 := (half_bounds (hx p0)).1 ca0.1
  have y0_lt2 := (third_bounds (hy p0)).1 ca0.2
  have x1_ge3 := (half_bounds (hx p1)).2 ca1.1
  have y1_lt2 := (third_bounds (hy p1)).1 ca1.2
  have x2_lt3 := (half_bounds (hx p2)).1 ca2.1
  have y2_mid := (third_bounds (hy p2)).2.1 ca2.2
  have x3_ge3 := (half_bounds (hx p3)).2 ca3.1
  have y3_mid := (third_bounds (hy p3)).2.1 ca3.2
  have x4_lt3 := (half_bounds (hx p4)).1 ca4.1
  have y4_ge4 := (third_bounds (hy p4)).2.2 ca4.2
  have x5_ge3 := (half_bounds (hx p5)).2 ca5.1
  have y5_ge4 := (third_bounds (hy p5)).2.2 ca5.2
  have nb0 := no_boundary hx hy hsep p0
  have nb1 := no_boundary hx hy hsep p1
  have nb2 := no_boundary hx hy hsep p2
  have nb3 := no_boundary hx hy hsep p3
  have nb4 := no_boundary hx hy hsep p4
  have nb5 := no_boundary hx hy hsep p5
  obtain ⟨k, hkx, hky1, hky2⟩ := hk
  have hpk : p2 = k := by
    apply (Equiv.ofBijective (cellA x y) hbij).injective
    simp only [Equiv.ofBijective_apply]
    have hca : cellA x y p2 = (0, 1) := by simp [cellA, ca2.1, ca2.2]
    rw [hca]
    simp [cellA, half, third, show x k < 3 by linarith, show ¬ y k < 2 by linarith, show y k < 4 by linarith]
  have hx2_lt2 : x p2 < 2 := hpk ▸ hkx
  have hy2_lt3 : y p2 < 3 := hpk ▸ hky2
  have cb2 : cellB x y p2 = (0, 0) := by
    simp [cellB, third, half, hx2_lt2, hy2_lt3]
  have hx0_gt2 : 2 < x p0 := by
    by_contra! hle
    have hlt : x p0 < 2 := lt_of_le_of_ne hle nb0.1
    have cb0 : cellB x y p0 = (0, 0) := by
      simp [cellB, third, half, hlt, show y p0 < 3 by linarith]
    have heq : p0 = p2 := hinjB (cb0.trans cb2.symm)
    have : third (y p0) = third (y p2) := congrArg (fun i => third (y i)) heq
    rw [ca0.2, ca2.2] at this
    exact absurd this (by decide)
  have cb0 : cellB x y p0 = (1, 0) := by
    simp [cellB, third, half, show ¬ x p0 < 2 by linarith, show x p0 < 4 by linarith,
      show y p0 < 3 by linarith]
  have hx1_gt4 : 4 < x p1 := by
    by_contra! hle
    have hlt : x p1 < 4 := lt_of_le_of_ne hle nb1.2.2.1
    have cb1 : cellB x y p1 = (1, 0) := by
      simp [cellB, third, half, show ¬ x p1 < 2 by linarith, hlt, show y p1 < 3 by linarith]
    have heq : p1 = p0 := hinjB (cb1.trans cb0.symm)
    have : half (x p1) = half (x p0) := congrArg (fun i => half (x i)) heq
    rw [ca1.1, ca0.1] at this
    exact absurd this (by decide)
  have cb1 : cellB x y p1 = (2, 0) := by
    simp [cellB, third, half, show ¬ x p1 < 2 by linarith, show ¬ x p1 < 4 by linarith,
      show y p1 < 3 by linarith]
  have hx3_gt4 : 4 < x p3 := by
    by_contra! hle
    have hlt : x p3 < 4 := lt_of_le_of_ne hle nb3.2.2.1
    exact hnc p3 ⟨by linarith [nb3.1], hlt, lt_of_le_of_ne y3_mid.1 nb3.2.2.2.1.symm, y3_mid.2⟩
  have hy3_gt3 : 3 < y p3 := by
    by_contra! hle
    have hlt : y p3 < 3 := lt_of_le_of_ne hle nb3.2.2.2.2.1
    have cb3 : cellB x y p3 = (2, 0) := by
      simp [cellB, third, half, show ¬ x p3 < 2 by linarith, show ¬ x p3 < 4 by linarith, hlt]
    have heq : p3 = p1 := hinjB (cb3.trans cb1.symm)
    have : third (y p3) = third (y p1) := congrArg (fun i => third (y i)) heq
    rw [ca3.2, ca1.2] at this
    exact absurd this (by decide)
  have cb3 : cellB x y p3 = (2, 1) := by
    simp [cellB, third, half, show ¬ x p3 < 2 by linarith, show ¬ x p3 < 4 by linarith,
      show ¬ y p3 < 3 by linarith]
  have hx5_lt4 : x p5 < 4 := by
    by_contra! hle
    have hgt : 4 < x p5 := lt_of_le_of_ne hle nb5.2.2.1.symm
    have cb5 : cellB x y p5 = (2, 1) := by
      simp [cellB, third, half, show ¬ x p5 < 2 by linarith, show ¬ x p5 < 4 by linarith,
        show ¬ y p5 < 3 by linarith]
    have heq : p5 = p3 := hinjB (cb5.trans cb3.symm)
    have : third (y p5) = third (y p3) := congrArg (fun i => third (y i)) heq
    rw [ca5.2, ca3.2] at this
    exact absurd this (by decide)
  have cb5 : cellB x y p5 = (1, 1) := by
    simp [cellB, third, half, show ¬ x p5 < 2 by linarith, hx5_lt4, show ¬ y p5 < 3 by linarith]
  have hx4_lt2 : x p4 < 2 := by
    by_contra! hle
    have hgt : 2 < x p4 := lt_of_le_of_ne hle nb4.1.symm
    have cb4 : cellB x y p4 = (1, 1) := by
      simp [cellB, third, half, show ¬ x p4 < 2 by linarith, show x p4 < 4 by linarith,
        show ¬ y p4 < 3 by linarith]
    have heq : p4 = p5 := hinjB (cb4.trans cb5.symm)
    have : half (x p4) = half (x p5) := congrArg (fun i => half (x i)) heq
    rw [ca4.1, ca5.1] at this
    exact absurd this (by decide)
  refine pattern1_contradiction
    ⟨hx0_gt2.le, x0_lt3.2.le⟩ ⟨y0_lt2.1, y0_lt2.2.le⟩
    ⟨hx1_gt4.le, x1_ge3.2⟩ ⟨y1_lt2.1, y1_lt2.2.le⟩
    ⟨x2_lt3.1, hx2_lt2.le⟩ ⟨y2_mid.1, hy2_lt3.le⟩
    ⟨hx3_gt4.le, x3_ge3.2⟩ ⟨hy3_gt3.le, y3_mid.2.le⟩
    ⟨x4_lt3.1, hx4_lt2.le⟩ ⟨y4_ge4.1, y4_ge4.2⟩
    ⟨x5_ge3.1, hx5_lt4.le⟩ ⟨y5_ge4.1, y5_ge4.2⟩
    (hsep p0 p1 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca0.1, ca1.1] at this; exact absurd this (by decide)))
    (hsep p0 p2 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca0.2, ca2.2] at this; exact absurd this (by decide)))
    (hsep p1 p3 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca1.2, ca3.2] at this; exact absurd this (by decide)))
    (hsep p2 p4 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca2.2, ca4.2] at this; exact absurd this (by decide)))
    (hsep p3 p5 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca3.2, ca5.2] at this; exact absurd this (by decide)))
    (hsep p4 p5 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca4.1, ca5.1] at this; exact absurd this (by decide)))

private lemma branch2_oriented {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2)
    (hk : ∃ k, 3 < x k ∧ x k < 4 ∧ 3 < y k ∧ y k < 4) : False := by
  have hbij := cellA_bij hx hy hsep
  have hinjB := cellB_inj hx hy hsep
  let a := (Equiv.ofBijective (cellA x y) hbij).symm
  let p0 := a (0, 0)
  let p1 := a (1, 0)
  let p2 := a (0, 1)
  let p3 := a (1, 1)
  let p4 := a (0, 2)
  let p5 := a (1, 2)
  have ca0 : cellA x y p0 = (0, 0) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca1 : cellA x y p1 = (1, 0) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca2 : cellA x y p2 = (0, 1) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca3 : cellA x y p3 = (1, 1) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca4 : cellA x y p4 = (0, 2) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  have ca5 : cellA x y p5 = (1, 2) := (Equiv.ofBijective _ hbij).apply_symm_apply _
  simp only [cellA, Prod.mk.injEq] at ca0 ca1 ca2 ca3 ca4 ca5
  have x0_lt3 := (half_bounds (hx p0)).1 ca0.1
  have y0_lt2 := (third_bounds (hy p0)).1 ca0.2
  have x1_ge3 := (half_bounds (hx p1)).2 ca1.1
  have y1_lt2 := (third_bounds (hy p1)).1 ca1.2
  have x2_lt3 := (half_bounds (hx p2)).1 ca2.1
  have y2_mid := (third_bounds (hy p2)).2.1 ca2.2
  have x3_ge3 := (half_bounds (hx p3)).2 ca3.1
  have y3_mid := (third_bounds (hy p3)).2.1 ca3.2
  have x4_lt3 := (half_bounds (hx p4)).1 ca4.1
  have y4_ge4 := (third_bounds (hy p4)).2.2 ca4.2
  have x5_ge3 := (half_bounds (hx p5)).2 ca5.1
  have y5_ge4 := (third_bounds (hy p5)).2.2 ca5.2
  have nb0 := no_boundary hx hy hsep p0
  have nb1 := no_boundary hx hy hsep p1
  have nb2 := no_boundary hx hy hsep p2
  have nb4 := no_boundary hx hy hsep p4
  have nb5 := no_boundary hx hy hsep p5
  obtain ⟨k, hkx1, hkx2, hky1, hky2⟩ := hk
  have hpk : p3 = k := by
    apply (Equiv.ofBijective (cellA x y) hbij).injective
    simp only [Equiv.ofBijective_apply]
    have hca : cellA x y p3 = (1, 1) := by simp [cellA, ca3.1, ca3.2]
    rw [hca]
    simp [cellA, half, third, show ¬ x k < 3 by linarith, show ¬ y k < 2 by linarith, hky2]
  have hx3_gt3 : 3 < x p3 := hpk ▸ hkx1
  have hx3_lt4 : x p3 < 4 := hpk ▸ hkx2
  have hy3_gt3 : 3 < y p3 := hpk ▸ hky1
  have hy3_lt4 : y p3 < 4 := hpk ▸ hky2
  have cb3 : cellB x y p3 = (1, 1) := by
    simp [cellB, third, half, show ¬ x p3 < 2 by linarith, hx3_lt4, show ¬ y p3 < 3 by linarith]
  have hnc : ∀ j, j ≠ p3 → ¬ inCenter x y j := by
    intro j hj hcj
    have hdx : (x p3 - x j) ^ 2 ≤ 4 := by
      have hsq := sq_le_of_mem_Icc (u := x p3) (v := x j) (l := 2) (r := 4)
        ⟨by linarith only [hx3_gt3], hx3_lt4.le⟩ ⟨hcj.1.le, hcj.2.1.le⟩
      linarith only [hsq]
    have hdy : (y p3 - y j) ^ 2 ≤ 4 := by
      have hsq := sq_le_of_mem_Icc (u := y p3) (v := y j) (l := 2) (r := 4)
        ⟨by linarith only [hy3_gt3], hy3_lt4.le⟩ ⟨hcj.2.2.1.le, hcj.2.2.2.le⟩
      linarith only [hsq]
    linarith only [hdx, hdy, hsep p3 j hj.symm]
  have hx5_gt4 : 4 < x p5 := by
    by_contra! hle
    have hlt : x p5 < 4 := lt_of_le_of_ne hle nb5.2.2.1
    have cb5 : cellB x y p5 = (1, 1) := by
      simp [cellB, third, half, show ¬ x p5 < 2 by linarith, hlt, show ¬ y p5 < 3 by linarith]
    have heq : p5 = p3 := hinjB (cb5.trans cb3.symm)
    have : third (y p5) = third (y p3) := congrArg (fun i => third (y i)) heq
    rw [ca5.2, ca3.2] at this
    exact absurd this (by decide)
  have hx4_lt2 : x p4 < 2 := by
    by_contra! hle
    have hgt : 2 < x p4 := lt_of_le_of_ne hle nb4.1.symm
    have cb4 : cellB x y p4 = (1, 1) := by
      simp [cellB, third, half, show ¬ x p4 < 2 by linarith, show x p4 < 4 by linarith,
        show ¬ y p4 < 3 by linarith]
    have heq : p4 = p3 := hinjB (cb4.trans cb3.symm)
    have : third (y p4) = third (y p3) := congrArg (fun i => third (y i)) heq
    rw [ca4.2, ca3.2] at this
    exact absurd this (by decide)
  have cb4 : cellB x y p4 = (0, 1) := by
    simp [cellB, third, half, hx4_lt2, show ¬ y p4 < 3 by linarith]
  have hx2_lt2 : x p2 < 2 := by
    by_contra! hle
    have hgt : 2 < x p2 := lt_of_le_of_ne hle nb2.1.symm
    have hne : p2 ≠ p3 := fun h => by
      have := congrArg (fun i => half (x i)) h; rw [ca2.1, ca3.1] at this; exact absurd this (by decide)
    exact hnc p2 hne ⟨hgt, show x p2 < 4 by linarith, lt_of_le_of_ne y2_mid.1 nb2.2.2.2.1.symm, y2_mid.2⟩
  have hy2_lt3 : y p2 < 3 := by
    by_contra! hle
    have hgt : 3 < y p2 := lt_of_le_of_ne hle nb2.2.2.2.2.1.symm
    have cb2 : cellB x y p2 = (0, 1) := by
      simp [cellB, third, half, hx2_lt2, show ¬ y p2 < 3 by linarith]
    have heq : p2 = p4 := hinjB (cb2.trans cb4.symm)
    have : third (y p2) = third (y p4) := congrArg (fun i => third (y i)) heq
    rw [ca2.2, ca4.2] at this
    exact absurd this (by decide)
  have cb2 : cellB x y p2 = (0, 0) := by
    simp [cellB, third, half, hx2_lt2, hy2_lt3]
  have hx0_gt2 : 2 < x p0 := by
    by_contra! hle
    have hlt : x p0 < 2 := lt_of_le_of_ne hle nb0.1
    have cb0 : cellB x y p0 = (0, 0) := by
      simp [cellB, third, half, hlt, show y p0 < 3 by linarith]
    have heq : p0 = p2 := hinjB (cb0.trans cb2.symm)
    have : third (y p0) = third (y p2) := congrArg (fun i => third (y i)) heq
    rw [ca0.2, ca2.2] at this
    exact absurd this (by decide)
  have cb0 : cellB x y p0 = (1, 0) := by
    simp [cellB, third, half, show ¬ x p0 < 2 by linarith, show x p0 < 4 by linarith,
      show y p0 < 3 by linarith]
  have hx1_gt4 : 4 < x p1 := by
    by_contra! hle
    have hlt : x p1 < 4 := lt_of_le_of_ne hle nb1.2.2.1
    have cb1 : cellB x y p1 = (1, 0) := by
      simp [cellB, third, half, show ¬ x p1 < 2 by linarith, hlt, show y p1 < 3 by linarith]
    have heq : p1 = p0 := hinjB (cb1.trans cb0.symm)
    have : half (x p1) = half (x p0) := congrArg (fun i => half (x i)) heq
    rw [ca1.1, ca0.1] at this
    exact absurd this (by decide)
  have s01 := hsep p0 p1 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca0.1, ca1.1] at this; exact absurd this (by decide))
  have s02 := hsep p0 p2 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca0.2, ca2.2] at this; exact absurd this (by decide))
  have s13 := hsep p1 p3 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca1.2, ca3.2] at this; exact absurd this (by decide))
  have s23 := hsep p2 p3 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca2.1, ca3.1] at this; exact absurd this (by decide))
  have s35 := hsep p3 p5 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca3.2, ca5.2] at this; exact absurd this (by decide))
  rcases le_total (x p3) (y p3) with hxy | hyx
  · exact pattern2_ordered_contradiction
      ⟨hx0_gt2.le, x0_lt3.2.le⟩ ⟨y0_lt2.1, y0_lt2.2.le⟩
      ⟨hx1_gt4.le, x1_ge3.2⟩ ⟨y1_lt2.1, y1_lt2.2.le⟩
      ⟨x2_lt3.1, hx2_lt2.le⟩ ⟨y2_mid.1, hy2_lt3.le⟩
      ⟨hx3_gt3.le, hx3_lt4.le⟩ ⟨hy3_gt3.le, hy3_lt4.le⟩
      ⟨hx5_gt4.le, x5_ge3.2⟩ ⟨y5_ge4.1, y5_ge4.2⟩
      hxy s01 s02 s13 s23 s35
  · exact pattern2_ordered_contradiction
      ⟨y2_mid.1, hy2_lt3.le⟩ ⟨x2_lt3.1, hx2_lt2.le⟩
      ⟨y4_ge4.1, y4_ge4.2⟩ ⟨x4_lt3.1, hx4_lt2.le⟩
      ⟨y0_lt2.1, y0_lt2.2.le⟩ ⟨hx0_gt2.le, x0_lt3.2.le⟩
      ⟨hy3_gt3.le, hy3_lt4.le⟩ ⟨hx3_gt3.le, hx3_lt4.le⟩
      ⟨y5_ge4.1, y5_ge4.2⟩ ⟨hx5_gt4.le, x5_ge3.2⟩
      hyx
      (by linarith [hsep p2 p4 (fun h => by have := congrArg (fun i => third (y i)) h; rw [ca2.2, ca4.2] at this; exact absurd this (by decide))])
      (by linarith [s02])
      (by linarith [hsep p4 p3 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca4.1, ca3.1] at this; exact absurd this (by decide))])
      (by linarith [hsep p0 p3 (fun h => by have := congrArg (fun i => half (x i)) h; rw [ca0.1, ca3.1] at this; exact absurd this (by decide))])
      (by linarith [s35])

private lemma reflect_bounds {u : Fin 6 → ℝ} (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 6) :
    ∀ i, 0 ≤ (6 - u i) ∧ (6 - u i) ≤ 6 := fun i => ⟨by linarith [(hu i).2], by linarith [(hu i).1]⟩

private lemma six_points_contradiction {x y : Fin 6 → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6)
    (hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2) : False := by
  by_cases hc : ∃ k, inCenter x y k
  · obtain ⟨k, hkx1, hkx2, hky1, hky2⟩ := hc
    have hnb := no_boundary hx hy hsep k
    rcases lt_or_gt_of_ne hnb.2.1 with hxk3 | hxk3 <;>
      rcases lt_or_gt_of_ne hnb.2.2.2.2.1 with hyk3 | hyk3
    · exact branch2_oriented (reflect_bounds hx) (reflect_bounds hy)
        (fun i j hij => by nlinarith only [hsep i j hij])
        ⟨k, by linarith, by linarith, by linarith, by linarith⟩
    · exact branch2_oriented (reflect_bounds hx) hy
        (fun i j hij => by nlinarith only [hsep i j hij])
        ⟨k, by linarith, by linarith, hyk3, hky2⟩
    · exact branch2_oriented hx (reflect_bounds hy)
        (fun i j hij => by nlinarith only [hsep i j hij])
        ⟨k, hxk3, hkx2, by linarith, by linarith⟩
    · exact branch2_oriented hx hy hsep ⟨k, hxk3, hkx2, hyk3, hky2⟩
  · have hbij := cellA_bij hx hy hsep
    let a := (Equiv.ofBijective (cellA x y) hbij).symm
    let p2 := a (0, 1)
    have ca2 : cellA x y p2 = (0, 1) := (Equiv.ofBijective _ hbij).apply_symm_apply _
    simp only [cellA, Prod.mk.injEq] at ca2
    have x2_lt3 := (half_bounds (hx p2)).1 ca2.1
    have y2_mid := (third_bounds (hy p2)).2.1 ca2.2
    have nb2 := no_boundary hx hy hsep p2
    have hx2_lt2 : x p2 < 2 := by
      by_contra! hle
      have hgt : 2 < x p2 := lt_of_le_of_ne hle nb2.1.symm
      exact hc ⟨p2, hgt, by linarith, lt_of_le_of_ne y2_mid.1 nb2.2.2.2.1.symm, y2_mid.2⟩
    rcases lt_or_gt_of_ne nb2.2.2.2.2.1 with hy23 | hy23
    · exact branch1_oriented hx hy hsep (fun k hk => hc ⟨k, hk⟩)
        ⟨p2, hx2_lt2, lt_of_le_of_ne y2_mid.1 nb2.2.2.2.1.symm, hy23⟩
    · have hnc' : ∀ k, ¬ inCenter x (fun i => 6 - y i) k := by
        intro k hck
        exact hc ⟨k, hck.1, hck.2.1, by linarith [hck.2.2.2], by linarith [hck.2.2.1]⟩
      exact branch1_oriented hx (reflect_bounds hy)
        (fun i j hij => by nlinarith only [hsep i j hij]) hnc'
        ⟨p2, hx2_lt2, by linarith [y2_mid.2], by linarith⟩

/-- `s(6) ≥ 2 + 12√13 / 13`. -/
theorem lower_six : RadicalLowerBound 6 [(26, 1), (12, 13)] 13 := by
  have hrad : radical [(26, 1), (12, 13)] 13 = 2 + 12 * Real.sqrt 13 / 13 := by
    unfold radical
    norm_num
    ring
  rw [RadicalLowerBound, hrad]
  intro s c hc
  by_contra! hs
  set L : ℝ := s - 2
  have hb := fun i => center_bounds (hc.2.1 i)
  have hL0 : 0 ≤ L := by
    have h0 := hb 0
    dsimp [L]
    linarith
  rcases hL0.eq_or_lt with hLzero | hLpos
  · have h4 := four_le_dist_sq hc (i := 0) (j := 1) (by decide)
    have h0 := hb 0
    have h1 := hb 1
    have hs2 : s = 2 := by linarith
    rw [hs2] at h0 h1
    nlinarith only [h0, h1, h4]
  · have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    have h13n : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg 13
    have hLlt : L < 12 * Real.sqrt 13 / 13 := by
      dsimp [L]
      linarith
    have h13L2 : 13 * L ^ 2 < 144 := by
      have hmul : 13 * L < 12 * Real.sqrt 13 := by linarith
      have hsq : (13 * L) ^ 2 < (12 * Real.sqrt 13) ^ 2 := by
        nlinarith only [mul_pos (show 0 < 12 * Real.sqrt 13 - 13 * L by linarith)
                                (show 0 < 12 * Real.sqrt 13 + 13 * L by linarith)]
      have hrhs : (12 * Real.sqrt 13) ^ 2 = 13 * 144 := by
        calc
          (12 * Real.sqrt 13) ^ 2 = 144 * Real.sqrt 13 ^ 2 := by ring
          _ = 13 * 144 := by rw [h13]; ring
      nlinarith only [hsq, hrhs]
    let x : Fin 6 → ℝ := fun i => 6 * (c i 0 - 1) / L
    let y : Fin 6 → ℝ := fun i => 6 * (c i 1 - 1) / L
    have hx : ∀ i, 0 ≤ x i ∧ x i ≤ 6 := by
      intro i
      obtain ⟨h0, h1, -, -⟩ := hb i
      dsimp [x]
      constructor
      · exact div_nonneg (by linarith) hLpos.le
      · rw [div_le_iff₀ hLpos]
        dsimp [L] at h1 ⊢
        nlinarith
    have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 6 := by
      intro i
      obtain ⟨-, -, h0, h1⟩ := hb i
      dsimp [y]
      constructor
      · exact div_nonneg (by linarith) hLpos.le
      · rw [div_le_iff₀ hLpos]
        dsimp [L] at h1 ⊢
        nlinarith
    have hsep : ∀ i j, i ≠ j → 13 < (x i - x j) ^ 2 + (y i - y j) ^ 2 := by
      intro i j hij
      have h4 := four_le_dist_sq hc hij
      have hscale : ((x i - x j) ^ 2 + (y i - y j) ^ 2) * L ^ 2 =
          36 * ((c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2) := by
        dsimp [x, y]
        field_simp [ne_of_gt hLpos]
        ring
      have hL2 : 0 < L ^ 2 := sq_pos_of_pos hLpos
      nlinarith only [h4, hscale, h13L2, hL2]
    exact six_points_contradiction hx hy hsep

end LeapsInBounds.Proofs.CircleInSquare6
