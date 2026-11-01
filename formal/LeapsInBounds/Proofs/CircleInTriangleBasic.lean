module

public import LeapsInBounds.Statements.CircleInTriangle

/-!
# Basic lower bounds for packing unit circles in an equilateral triangle

The centers of a packing lie in the triangle of points at distance at least 1
from each side, which has side `s - 2√3`, and are at distance at least 2 from
each other.

- `s(1) ≥ 2√3`: that triangle is nonempty.
- `s(k² + 1) ≥ 2k + 2√3`: cutting it into `k²` triangles of side
  `(s - 2√3) / k`, two centers lie in the same one. This gives `s(2)`, `s(5)` and
  `s(10)`, and so `s(3)` and `s(6)`.
- `s(4) ≥ 4√3`: cutting it into three kites, two centers lie in the same one.
-/

public section

namespace LeapsInBounds.Proofs.CircleInTriangleBasic

open CircleInTriangle

lemma sqrt3_mul_self : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)

lemma sqrt3_pos : (0 : ℝ) < √3 := by positivity

lemma add_mem_closedBall (p : Plane) {u v : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1) :
    p + !₂[u, v] ∈ Metric.closedBall p 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_eq]
  simpa [Fin.sum_univ_two] using h

/-- The center of a unit disk in the triangle is at distance at least 1 from
each side. -/
lemma center_bounds {s : ℝ} {p : Plane} (h : Metric.closedBall p 1 ⊆ triangle s) :
    1 ≤ p 1 ∧ 2 ≤ √3 * p 0 - p 1 ∧ 2 ≤ √3 * (s - p 0) - p 1 := by
  have h1 := h (add_mem_closedBall p (u := 0) (v := -1) (by norm_num))
  have h2 := h (add_mem_closedBall p (u := -(√3 / 2)) (v := 1 / 2) (by nlinarith [sqrt3_mul_self]))
  have h3 := h (add_mem_closedBall p (u := √3 / 2) (v := 1 / 2) (by nlinarith [sqrt3_mul_self]))
  simp only [triangle, Set.mem_ofPred_eq, PiLp.add_apply] at h1 h2 h3
  simp at h1 h2 h3
  refine ⟨by linarith [h1.1], by nlinarith [h2.2.1, sqrt3_mul_self], by nlinarith [h3.2.2, sqrt3_mul_self]⟩

lemma four_le_dist_sq {n : ℕ} {s : ℝ} {c : Fin n → Plane} (h : IsPacking s c) {i j : Fin n}
    (hij : i ≠ j) : 4 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 := by
  have h2 := (disjoint_ball_ball_iff one_pos one_pos).1 (h.2.2 i j hij)
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs] at h2
  nlinarith [Real.sq_sqrt (show 0 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2 by positivity)]

/-- For two points with nonnegative coordinates `(u, v, w)` and `(u', v', w')`
summing to `r`, the squared distance between the coordinate vectors is at most
`2 r²`, the value for two different vertices `(r, 0, 0)` and `(0, r, 0)`. -/
lemma core {u v w u' v' w' r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hu' : 0 ≤ u')
    (hv' : 0 ≤ v') (hw' : 0 ≤ w') (h : u + v + w = r) (h' : u' + v' + w' = r) :
    (u - u') ^ 2 + (v - v') ^ 2 + (w - w') ^ 2 ≤ 2 * r ^ 2 := by
  subst h
  nlinarith [mul_nonneg hu hv, mul_nonneg hu hw, mul_nonneg hv hw, mul_nonneg hu' hv',
    mul_nonneg hu' hw', mul_nonneg hv' hw', mul_nonneg hu hu', mul_nonneg hv hv', mul_nonneg hw hw']

/-! The centers of a packing lie in a smaller equilateral triangle with the
same center, at distance 1 inside the given one. We measure their distances
from its sides `a`, `b` and `c`, which sum to its height `h`. -/

/-- Distance from the bottom side of the triangle of centers. -/
def a (p : Plane) : ℝ := p 1 - 1

/-- Distance from the left side of the triangle of centers. -/
noncomputable def b (p : Plane) : ℝ := (√3 * p 0 - p 1 - 2) / 2

/-- Distance from the right side of the triangle of centers. -/
noncomputable def c (s : ℝ) (p : Plane) : ℝ := (√3 * (s - p 0) - p 1 - 2) / 2

/-- Height of the triangle of centers. -/
noncomputable def h (s : ℝ) : ℝ := √3 * s / 2 - 3

lemma a_add_b_add_c (s : ℝ) (p : Plane) : a p + b p + c s p = h s := by
  simp only [a, b, c, h]; ring

lemma nonneg {s : ℝ} {p : Plane} (hp : Metric.closedBall p 1 ⊆ triangle s) :
    0 ≤ a p ∧ 0 ≤ b p ∧ 0 ≤ c s p := by
  obtain ⟨h1, h2, h3⟩ := center_bounds hp
  simp only [a, b, c]
  refine ⟨by linarith, by linarith, by linarith⟩

lemma dist_sq (s : ℝ) (p q : Plane) : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 =
    2 / 3 * ((a p - a q) ^ 2 + (b p - b q) ^ 2 + (c s p - c s q) ^ 2) := by
  simp only [a, b, c]
  linear_combination (-(p 0 - q 0) ^ 2 / 3) * sqrt3_mul_self

/-- Two centers of a packing whose coordinates, shifted by `(α, β, γ)` and
possibly negated, lie in a triangle of height `r`, show that `3 ≤ r²`. -/
lemma three_le_sq {n : ℕ} {s : ℝ} {x : Fin n → Plane} (hx : IsPacking s x) {i j : Fin n}
    (hij : i ≠ j) {r α β γ σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hi : 0 ≤ σ * (a (x i) - α) ∧ 0 ≤ σ * (b (x i) - β) ∧ 0 ≤ σ * (c s (x i) - γ))
    (hj : 0 ≤ σ * (a (x j) - α) ∧ 0 ≤ σ * (b (x j) - β) ∧ 0 ≤ σ * (c s (x j) - γ))
    (hr : σ * (h s - α - β - γ) = r) : 3 ≤ r ^ 2 := by
  have h4 := four_le_dist_sq hx hij
  rw [dist_sq s] at h4
  have := core (r := r) hi.1 hi.2.1 hi.2.2 hj.1 hj.2.1 hj.2.2
    (by rw [← hr, ← a_add_b_add_c s (x i)]; ring) (by rw [← hr, ← a_add_b_add_c s (x j)]; ring)
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have e : (σ * (a (x i) - α) - σ * (a (x j) - α)) ^ 2 + (σ * (b (x i) - β) - σ * (b (x j) - β)) ^ 2 +
      (σ * (c s (x i) - γ) - σ * (c s (x j) - γ)) ^ 2 =
      (a (x i) - a (x j)) ^ 2 + (b (x i) - b (x j)) ^ 2 + (c s (x i) - c s (x j)) ^ 2 := by
    linear_combination ((a (x i) - a (x j)) ^ 2 + (b (x i) - b (x j)) ^ 2 +
      (c s (x i) - c s (x j)) ^ 2) * hσ2
  linarith

/-- If the triangle of centers has height `h ≥ √3 k`, the triangle has side at
least `2k + 2√3`. -/
lemma le_side {s k : ℝ} (hk : √3 * k ≤ h s) : 2 * k + 2 * √3 ≤ s := by
  simp only [h] at hk
  nlinarith [sqrt3_mul_self, sqrt3_pos]

/-- A lower bound for `n` circles is one for more circles too. -/
theorem LowerBound.mono {n m : ℕ} {v : ℝ} (hv : LowerBound n v) (hnm : n ≤ m) : LowerBound m v :=
  fun s x hx => hv s (x ∘ Fin.castLE hnm)
    ⟨hx.1, fun _ => hx.2.1 _, fun _ _ hij => hx.2.2 _ _ ((Fin.castLE_injective hnm).ne hij)⟩

/-! Cutting the triangle of centers into `k²` triangles of height `r = h / k`
by lines parallel to its sides, two of `k² + 1` centers lie in the same small
triangle, which has side `2r / √3`, so `2 ≤ 2r / √3`. -/

/-- The small triangles: `(i, j, true)` is the one pointing up where
`a ≥ i r`, `b ≥ j r` and `c ≥ (k - 1 - i - j) r`, and `(i, j, false)` the one
pointing down where `a ≤ (i + 1) r`, `b ≤ (j + 1) r` and
`c ≤ (k - 1 - i - j) r`. -/
def cells (k : ℕ) : Finset (ℕ × ℕ × Bool) :=
  (Finset.range k ×ˢ Finset.range k ×ˢ Finset.univ).filter
    fun x => if x.2.2 then x.1 + x.2.1 + 1 ≤ k else x.1 + x.2.1 + 2 ≤ k

/-- `p` is in the small triangle `x` of height `r`. -/
def InCell (s r : ℝ) (k : ℕ) (p : Plane) : ℕ × ℕ × Bool → Prop
  | (i, j, true) => i * r ≤ a p ∧ j * r ≤ b p ∧ ((k : ℝ) - 1 - i - j) * r ≤ c s p
  | (i, j, false) => a p ≤ (i + 1) * r ∧ b p ≤ (j + 1) * r ∧ c s p ≤ ((k : ℝ) - 1 - i - j) * r

lemma exists_cell {s r : ℝ} {k : ℕ} (hk : 0 < k) (hr : 0 ≤ r) {p : Plane}
    (ha : 0 ≤ a p) (hb : 0 ≤ b p) (hc : 0 ≤ c s p) (hsum : a p + b p + c s p = k * r) :
    ∃ x ∈ cells k, InCell s r k p x := by
  rcases hr.eq_or_lt with rfl | hr
  · refine ⟨(0, 0, true), by simp [cells]; omega, ?_⟩
    simp [InCell, ha, hb, hc]
  set i := ⌊a p / r⌋₊
  set j := ⌊b p / r⌋₊
  have hi1 : i * r ≤ a p := (le_div_iff₀ hr).1 (Nat.floor_le (div_nonneg ha hr.le))
  have hi2 : a p < (i + 1) * r := (div_lt_iff₀ hr).1 (Nat.lt_floor_add_one _)
  have hj1 : j * r ≤ b p := (le_div_iff₀ hr).1 (Nat.floor_le (div_nonneg hb hr.le))
  have hj2 : b p < (j + 1) * r := (div_lt_iff₀ hr).1 (Nat.lt_floor_add_one _)
  by_cases hup : a p + b p ≤ (i + j + 1) * r
  · by_cases hij : i + j + 1 ≤ k
    · refine ⟨(i, j, true), by simp [cells]; omega, hi1, hj1, ?_⟩
      have : ((i : ℝ) + j + 1) ≤ k := by exact_mod_cast hij
      nlinarith
    · -- `p` is the vertex `(i r, j r, 0)` on the right side
      have hle : ((i : ℝ) + j) * r ≤ k * r := by nlinarith
      have hk' : i + j = k := by
        have := le_of_mul_le_mul_right hle hr
        have : i + j ≤ k := by exact_mod_cast this
        omega
      have hk'' : (i : ℝ) + j = k := by exact_mod_cast hk'
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        refine ⟨(0, j', true), by simp [cells]; omega, by simp [ha], ?_, ?_⟩
        · have : (j : ℝ) = j' + 1 := by exact_mod_cast hj'
          nlinarith
        · have : (j : ℝ) = j' + 1 := by exact_mod_cast hj'
          have : (i : ℝ) = 0 := by exact_mod_cast hi0
          push_cast; nlinarith
      · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        refine ⟨(i', j, true), by simp [cells]; omega, ?_, hj1, ?_⟩
        · have : (i : ℝ) = i' + 1 := by exact_mod_cast hi'
          nlinarith
        · have : (i : ℝ) = i' + 1 := by exact_mod_cast hi'
          nlinarith
  · have hij : i + j + 2 ≤ k := by
      have : ((i : ℝ) + j + 1) * r < k * r := by nlinarith
      have : (i : ℝ) + j + 1 < k := lt_of_mul_lt_mul_right this hr.le
      have : i + j + 1 < k := by exact_mod_cast this
      omega
    refine ⟨(i, j, false), by simp [cells]; omega, hi2.le, hj2.le, ?_⟩
    nlinarith

/-- With `k² + 1` circles, the triangle of centers has height at least
`√3 k`, so `s(k² + 1) ≥ 2k + 2√3`, if the small triangles are counted
correctly. -/
theorem lowerBound_sq_add_one (k : ℕ) (hk : 0 < k) (hcard : (cells k).card = k ^ 2) :
    LowerBound (k ^ 2 + 1) (2 * k + 2 * √3) := by
  intro s x hx
  set r := h s / k
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hhr : h s = k * r := by simp only [r]; field_simp
  have hr : 0 ≤ r := by
    obtain ⟨h1, h2, h3⟩ := nonneg (hx.2.1 0)
    have := a_add_b_add_c s (x 0)
    exact div_nonneg (by linarith) hkr.le
  have hcell : ∀ i, ∃ y ∈ cells k, InCell s r k (x i) y := fun i => by
    obtain ⟨h1, h2, h3⟩ := nonneg (hx.2.1 i)
    exact exists_cell hk hr h1 h2 h3 (by rw [a_add_b_add_c, hhr])
  choose f hf hfc using hcell
  obtain ⟨i, -, j, -, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.univ) (t := cells k) (by simp [hcard]) (fun i _ => hf i)
  have hi := hfc i
  have hj := hfc j
  rw [← hfij] at hj
  have h3 : 3 ≤ r ^ 2 := by
    generalize f i = y at hi hj
    obtain ⟨i0, j0, u⟩ := y
    cases u
    · obtain ⟨hi1, hi2, hi3⟩ := hi
      obtain ⟨hj1, hj2, hj3⟩ := hj
      refine three_le_sq hx hij (σ := -1) (α := (i0 + 1) * r) (β := (j0 + 1) * r)
        (γ := ((k : ℝ) - 1 - i0 - j0) * r) (Or.inr rfl) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩ ?_ <;>
        [linarith; linarith; linarith; linarith; linarith; linarith; (rw [hhr]; ring)]
    · obtain ⟨hi1, hi2, hi3⟩ := hi
      obtain ⟨hj1, hj2, hj3⟩ := hj
      refine three_le_sq hx hij (σ := 1) (α := i0 * r) (β := j0 * r)
        (γ := ((k : ℝ) - 1 - i0 - j0) * r) (Or.inl rfl) ⟨?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩ ?_ <;>
        [linarith; linarith; linarith; linarith; linarith; linarith; (rw [hhr]; ring)]
  apply le_side
  rw [hhr, mul_comm]
  apply mul_le_mul_of_nonneg_left _ hkr.le
  nlinarith [sqrt3_mul_self, sqrt3_pos]

/-! Cutting the triangle of centers into three kites by the lines from its
center to the midpoints of its sides, two of 4 centers lie in the same kite,
in which points are at most `2h / 3` apart (from the center to a vertex). -/

/-- In the kite where the first coordinate is the largest, the squared distance
between coordinate vectors is at most `2 r² / 3`. -/
lemma kite {u v w u' v' w' r : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) (hv' : 0 ≤ v') (hw' : 0 ≤ w')
    (h : u + v + w = r) (h' : u' + v' + w' = r)
    (h1 : v ≤ u) (h2 : w ≤ u) (h1' : v' ≤ u') (h2' : w' ≤ u') :
    (u - u') ^ 2 + (v - v') ^ 2 + (w - w') ^ 2 ≤ 2 * r ^ 2 / 3 := by
  subst h
  obtain rfl : w' = u + v + w - u' - v' := by linarith
  nlinarith [mul_nonneg hv hv', mul_nonneg hw hv', mul_nonneg hv hw', mul_nonneg hw hw',
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1'), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2'),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2'), mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1'),
    mul_nonneg hv (sub_nonneg.2 h1'), mul_nonneg hw (sub_nonneg.2 h2'), mul_nonneg hv' (sub_nonneg.2 h1),
    mul_nonneg hw' (sub_nonneg.2 h2), mul_nonneg hv (sub_nonneg.2 h2'), mul_nonneg hw (sub_nonneg.2 h1'),
    mul_nonneg hv' (sub_nonneg.2 h2), mul_nonneg hw' (sub_nonneg.2 h1)]

/-- The kite containing `p`: the index of its largest coordinate. -/
noncomputable def kiteOf (s : ℝ) (p : Plane) : Fin 3 :=
  if b p ≤ a p ∧ c s p ≤ a p then 0 else if c s p ≤ b p then 1 else 2

lemma kiteOf_spec (s : ℝ) (p : Plane) :
    (kiteOf s p = 0 → b p ≤ a p ∧ c s p ≤ a p) ∧ (kiteOf s p = 1 → a p ≤ b p ∧ c s p ≤ b p) ∧
      (kiteOf s p = 2 → a p ≤ c s p ∧ b p ≤ c s p) := by
  unfold kiteOf
  split_ifs with h1 h2
  · simp [h1]
  · rw [not_and_or, not_le, not_le] at h1
    refine ⟨by simp, fun _ => ⟨?_, h2⟩, by simp⟩
    rcases h1 with h1 | h1 <;> linarith
  · rw [not_and_or, not_le, not_le] at h1
    rw [not_le] at h2
    refine ⟨by simp, by simp, fun _ => ⟨?_, h2.le⟩⟩
    rcases h1 with h1 | h1 <;> linarith

/-! ## Certified bounds -/

/-- `s(1) ≥ 2√3`: the triangle of centers has height at least 0. -/
theorem lower_one : RadicalLowerBound 1 [(2, 3)] 1 := by
  intro s x hx
  obtain ⟨h1, h2, h3⟩ := nonneg (hx.2.1 0)
  have := a_add_b_add_c s (x 0)
  have : (2 : ℝ) * (0 : ℕ) + 2 * √3 ≤ s := le_side (by simp; linarith)
  simpa [radical] using this

/-- `s(2) ≥ 2 + 2√3`. -/
theorem lower_two : RadicalLowerBound 2 [(2, 1), (2, 3)] 1 := by
  have := lowerBound_sq_add_one 1 one_pos (by decide)
  simpa [RadicalLowerBound, radical] using this

/-- `s(3) ≥ 2 + 2√3`. -/
theorem lower_three : RadicalLowerBound 3 [(2, 1), (2, 3)] 1 := LowerBound.mono lower_two (by norm_num)

/-- `s(4) ≥ 4√3`. -/
theorem lower_four : RadicalLowerBound 4 [(4, 3)] 1 := by
  intro s x hx
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => kiteOf s (x i)) (by simp)
  have h4 := four_le_dist_sq hx hij
  rw [dist_sq s] at h4
  obtain ⟨ai, bi, ci⟩ := nonneg (hx.2.1 i)
  obtain ⟨aj, bj, cj⟩ := nonneg (hx.2.1 j)
  have si := a_add_b_add_c s (x i)
  have sj := a_add_b_add_c s (x j)
  have key : (a (x i) - a (x j)) ^ 2 + (b (x i) - b (x j)) ^ 2 + (c s (x i) - c s (x j)) ^ 2 ≤
      2 * h s ^ 2 / 3 := by
    obtain ⟨i0, i1, i2⟩ := kiteOf_spec s (x i)
    obtain ⟨j0, j1, j2⟩ := kiteOf_spec s (x j)
    have hf : kiteOf s (x i) = kiteOf s (x j) := hf
    rcases (by decide : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2) (kiteOf s (x i)) with hk | hk | hk <;>
      rw [hk] at hf
    · exact kite bi ci bj cj si sj (i0 hk).1 (i0 hk).2 (j0 hf.symm).1 (j0 hf.symm).2
    · have := kite (u := b (x i)) (v := a (x i)) (w := c s (x i)) (u' := b (x j))
        (v' := a (x j)) (w' := c s (x j)) (r := h s) ai ci aj cj (by linarith) (by linarith)
        (i1 hk).1 (i1 hk).2 (j1 hf.symm).1 (j1 hf.symm).2
      linarith
    · have := kite (u := c s (x i)) (v := a (x i)) (w := b (x i)) (u' := c s (x j))
        (v' := a (x j)) (w' := b (x j)) (r := h s) ai bi aj bj (by linarith) (by linarith)
        (i2 hk).1 (i2 hk).2 (j2 hf.symm).1 (j2 hf.symm).2
      linarith
  have : (0 : ℝ) ≤ h s := by linarith
  have : √3 * √3 ≤ h s := by nlinarith [sqrt3_mul_self]
  have := le_side this
  simp only [radical]
  norm_num
  linarith

/-- `s(5) ≥ 4 + 2√3`. -/
theorem lower_five : RadicalLowerBound 5 [(4, 1), (2, 3)] 1 := by
  have := lowerBound_sq_add_one 2 two_pos (by decide)
  norm_num [RadicalLowerBound, radical] at this ⊢
  exact this

/-- `s(6) ≥ 4 + 2√3`. -/
theorem lower_six : RadicalLowerBound 6 [(4, 1), (2, 3)] 1 := LowerBound.mono lower_five (by norm_num)

/-- `s(10) ≥ 6 + 2√3`. -/
theorem lower_ten : RadicalLowerBound 10 [(6, 1), (2, 3)] 1 := by
  have := lowerBound_sq_add_one 3 (by norm_num) (by decide)
  norm_num [RadicalLowerBound, radical] at this ⊢
  exact this

end LeapsInBounds.Proofs.CircleInTriangleBasic
