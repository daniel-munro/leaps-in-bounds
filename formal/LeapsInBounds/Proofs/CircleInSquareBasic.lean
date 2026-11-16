module

public import LeapsInBounds.Statements.CircleInSquare

/-!
# Basic lower bounds for packing unit circles in a square

The centers of a packing lie in the square `[1, s - 1]²` of points at distance
at least 1 from each side, which has side `t = s - 2`, and are at distance at
least 2 from each other.

- `s(1) ≥ 2`: that square is nonempty.
- `s(k² + 1) ≥ 2 + k√2`: cutting it into `k²` squares of side `t / k`, two
  centers lie in the same one, so `2 ≤ √2 t / k`. This gives `s(2) = 2 + √2` and
  `s(5) = 2 + 2√2`.
-/

public section

namespace LeapsInBounds.Proofs.CircleInSquareBasic

open CircleInSquare

lemma add_mem_closedBall (p : Plane) {u v : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1) :
    p + !₂[u, v] ∈ Metric.closedBall p 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq]
  simpa [Fin.sum_univ_two] using h

/-- The center of a unit disk in the square is at distance at least 1 from
each side. -/
lemma center_bounds {s : ℝ} {p : Plane} (h : Metric.closedBall p 1 ⊆ square s) :
    1 ≤ p 0 ∧ p 0 ≤ s - 1 ∧ 1 ≤ p 1 ∧ p 1 ≤ s - 1 := by
  have h1 := h (add_mem_closedBall p (u := -1) (v := 0) (by norm_num))
  have h2 := h (add_mem_closedBall p (u := 1) (v := 0) (by norm_num))
  have h3 := h (add_mem_closedBall p (u := 0) (v := -1) (by norm_num))
  have h4 := h (add_mem_closedBall p (u := 0) (v := 1) (by norm_num))
  simp only [square, Set.mem_ofPred_eq, PiLp.add_apply] at h1 h2 h3 h4
  simp at h1 h2 h3 h4
  refine ⟨by linarith [h1.1], by linarith [h2.2.1], by linarith [h3.2.2.1], by linarith [h4.2.2.2]⟩

lemma four_le_dist_sq {n : ℕ} {s : ℝ} {c : Fin n → Plane} (h : IsPacking s c) {i j : Fin n}
    (hij : i ≠ j) : 4 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 := by
  have h2 := (disjoint_ball_ball_iff one_pos one_pos).1 (h.2.2 i j hij)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at h2
  nlinarith [Real.sq_sqrt (show 0 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 by positivity)]

/-- The index of the interval `[i r, (i + 1) r]` containing `u ∈ [0, k r]`. -/
noncomputable def cell (r : ℝ) (k : ℕ) (u : ℝ) : ℕ := min ⌊u / r⌋₊ (k - 1)

lemma cell_lt {r : ℝ} {k : ℕ} (hk : 0 < k) (u : ℝ) : cell r k u < k := by
  unfold cell; omega

lemma cell_spec {r u : ℝ} {k : ℕ} (hk : 0 < k) (hr : 0 < r) (hu : 0 ≤ u) (huk : u ≤ k * r) :
    cell r k u * r ≤ u ∧ u ≤ (cell r k u + 1) * r := by
  have hf1 : (⌊u / r⌋₊ : ℝ) * r ≤ u := (le_div_iff₀ hr).1 (Nat.floor_le (div_nonneg hu hr.le))
  have hf2 : u < ((⌊u / r⌋₊ : ℝ) + 1) * r := (div_lt_iff₀ hr).1 (Nat.lt_floor_add_one _)
  unfold cell
  rcases le_total ⌊u / r⌋₊ (k - 1) with h | h
  · rw [min_eq_left h]; exact ⟨hf1, hf2.le⟩
  · rw [min_eq_right h]
    have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; simp
    have : ((k - 1 : ℕ) : ℝ) ≤ ⌊u / r⌋₊ := by exact_mod_cast h
    rw [hk1] at this ⊢
    constructor <;> nlinarith

/-- A lower bound for `n` circles is one for more circles too. -/
theorem LowerBound.mono {n m : ℕ} {v : ℝ} (hv : LowerBound n v) (hnm : n ≤ m) : LowerBound m v :=
  fun s x hx => hv s (x ∘ Fin.castLE hnm)
    ⟨hx.1, fun _ => hx.2.1 _, fun _ _ hij => hx.2.2 _ _ ((Fin.castLE_injective hnm).ne hij)⟩

/-- `s(k² + 1) ≥ 2 + k√2`. -/
theorem lowerBound_sq_add_one (k : ℕ) (hk : 0 < k) : LowerBound (k ^ 2 + 1) (2 + k * √2) := by
  intro s x hx
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  set r := (s - 2) / k with hr_def
  have hsr : s - 2 = k * r := by rw [hr_def]; field_simp
  have hb := fun i => center_bounds (hx.2.1 i)
  have hr0 : 0 ≤ r := div_nonneg (by linarith [(hb 0).1, (hb 0).2.1]) hkr.le
  -- Two centers whose coordinates lie in intervals of length `r` with the same index
  obtain ⟨i, j, hij, hu, hv⟩ : ∃ i j : Fin (k ^ 2 + 1), i ≠ j ∧
      |x i 0 - x j 0| ≤ r ∧ |x i 1 - x j 1| ≤ r := by
    rcases hr0.eq_or_lt with h0 | hpos
    · refine ⟨0, 1, by simp [Fin.ext_iff]; omega, ?_, ?_⟩ <;>
      · rw [← h0, abs_nonpos_iff, sub_eq_zero]
        have : s - 2 = 0 := by rw [hsr, ← h0, mul_zero]
        linarith [(hb 0).1, (hb 0).2.1, (hb 1).1, (hb 1).2.1, (hb 0).2.2.1, (hb 0).2.2.2,
          (hb 1).2.2.1, (hb 1).2.2.2]
    · let f : Fin (k ^ 2 + 1) → ℕ × ℕ := fun i => (cell r k (x i 0 - 1), cell r k (x i 1 - 1))
      obtain ⟨i, -, j, -, hij, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Finset.univ) (t := Finset.range k ×ˢ Finset.range k) (f := f) (by simp; ring_nf; omega)
        (fun i _ => by simp [f, cell_lt hk])
      simp only [f, Prod.mk.injEq] at hf
      have ci0 := cell_spec hk hpos (u := x i 0 - 1) (by linarith [(hb i).1]) (by linarith [(hb i).2.1])
      have cj0 := cell_spec hk hpos (u := x j 0 - 1) (by linarith [(hb j).1]) (by linarith [(hb j).2.1])
      have ci1 := cell_spec hk hpos (u := x i 1 - 1) (by linarith [(hb i).2.2.1]) (by linarith [(hb i).2.2.2])
      have cj1 := cell_spec hk hpos (u := x j 1 - 1) (by linarith [(hb j).2.2.1]) (by linarith [(hb j).2.2.2])
      rw [hf.1] at ci0
      rw [hf.2] at ci1
      refine ⟨i, j, hij, abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have h4 := four_le_dist_sq hx hij
  have h2r : 2 ≤ r ^ 2 := by
    have a := sq_le_sq' (abs_le.1 hu).1 (abs_le.1 hu).2
    have b := sq_le_sq' (abs_le.1 hv).1 (abs_le.1 hv).2
    linarith
  have hsqrt : √2 ≤ r := by
    rw [← Real.sqrt_sq hr0]; exact Real.sqrt_le_sqrt h2r
  nlinarith

/-! ## Certified bounds -/

/-- `s(1) ≥ 2`. -/
theorem lower_one : RadicalLowerBound 1 [(2, 1)] 1 := by
  intro s x hx
  obtain ⟨h1, h2, -, -⟩ := center_bounds (hx.2.1 0)
  simp [radical]
  linarith

/-- `s(2) ≥ 2 + √2`. -/
theorem lower_two : RadicalLowerBound 2 [(2, 1), (1, 2)] 1 := by
  have := lowerBound_sq_add_one 1 one_pos
  norm_num [RadicalLowerBound, radical] at this ⊢
  exact this

/-- `s(5) ≥ 2 + 2√2`. -/
theorem lower_five : RadicalLowerBound 5 [(2, 1), (2, 2)] 1 := by
  have := lowerBound_sq_add_one 2 two_pos
  norm_num [RadicalLowerBound, radical] at this ⊢
  exact this

end LeapsInBounds.Proofs.CircleInSquareBasic
