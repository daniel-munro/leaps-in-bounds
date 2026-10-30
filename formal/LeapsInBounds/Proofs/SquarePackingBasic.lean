module

public import LeapsInBounds.Statements.SquarePacking
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Basic bounds for packing unit squares in a square

- `s(n) ≥ √n`: the squares have disjoint interiors, so their total area `n` is
  at most the area `s²` of the square containing them.
- `s(n) ≤ k` when `n ≤ k²`: put the squares in a `k × k` grid.
-/

public section

namespace LeapsInBounds.Proofs.SquarePackingBasic

open SquarePacking MeasureTheory

lemma square_eq (s : ℝ) : square s = WithLp.ofLp ⁻¹' Set.univ.pi fun _ => Set.Icc 0 s := by
  ext x; simp only [square, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

lemma volume_square {s : ℝ} (hs : 0 ≤ s) : volume (square s) = ENNReal.ofReal (s ^ 2) := by
  rw [square_eq, ← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage]
  · change volume (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) s) = _
    rw [volume_pi_pi]
    simp [Real.volume_Icc, sq, ENNReal.ofReal_mul hs]
  · exact ((MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage (by fun_prop)).nullMeasurableSet

lemma isClosed_square (s : ℝ) : IsClosed (square s) := by
  rw [square_eq]
  exact (isClosed_set_pi fun _ _ => isClosed_Icc).preimage (by fun_prop)

lemma convex_square (s : ℝ) : Convex ℝ (square s) := by
  rw [square_eq]
  exact (convex_pi fun _ _ => convex_Icc 0 s).linear_preimage (WithLp.linearEquiv 2 ℝ _).toLinearMap

lemma volume_image (f : Plane ≃ᵃⁱ[ℝ] Plane) {A : Set Plane} (hA : MeasurableSet A) :
    volume (f '' A) = volume A := by
  have hf : MeasurePreserving f.symm := by
    have : ⇑f.symm = (· + f.symm 0) ∘ f.symm.linearIsometryEquiv := by
      ext1 x
      have := f.symm.map_vadd 0 x
      simp only [vadd_eq_add, add_zero] at this
      exact this
    rw [this]
    exact (measurePreserving_add_right volume _).comp f.symm.linearIsometryEquiv.measurePreserving
  have : f '' A = f.symm ⁻¹' A := by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun hx => ⟨_, hx, by simp⟩⟩
  rw [this]
  exact hf.measure_preimage hA.nullMeasurableSet

/-- The squares of a packing have total area `n`, at most the area `s²` of the
square containing them. -/
theorem le_sq_of_isPacking {n : ℕ} {s : ℝ} {f : Fin n → Plane ≃ᵃⁱ[ℝ] Plane}
    (h : IsPacking s f) : (n : ℝ) ≤ s ^ 2 := by
  obtain ⟨hs, hsub, hdisj⟩ := h
  have hU : ∀ i, volume (interior (f i '' square 1)) = 1 := by
    intro i
    have hc : Convex ℝ (f i '' square 1) := (convex_square 1).affine_image (f i).toAffineMap
    rw [measure_interior_of_null_frontier (hc.addHaar_frontier volume),
      volume_image _ ((isClosed_square 1).measurableSet), volume_square zero_le_one]
    simp
  have hle : volume (⋃ i, interior (f i '' square 1)) ≤ volume (square s) :=
    measure_mono (Set.iUnion_subset fun i => interior_subset.trans (hsub i))
  rw [measure_iUnion (fun i j hij => hdisj i j hij) (fun i => isOpen_interior.measurableSet),
    tsum_fintype, volume_square hs] at hle
  simp only [hU, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hle
  rw [← ENNReal.ofReal_natCast] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle

/-- `s(n) ≥ √n`. -/
theorem sqrtLowerBound (n : ℕ) : SqrtLowerBound n n := fun _ _ h =>
  Real.sqrt_le_sqrt (le_sq_of_isPacking h) |>.trans_eq (Real.sqrt_sq h.1)

/-- A point inside a box `[v, v + 1]²` that has a neighborhood in it is strictly
inside the box. -/
lemma lt_of_mem_interior {T : Set Plane} {v y : Plane}
    (hT : T ⊆ {x | ∀ c, v c ≤ x c ∧ x c ≤ v c + 1}) (hy : y ∈ interior T) (c : Fin 2) :
    v c < y c ∧ y c < v c + 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have step (t : ℝ) (ht : |t| < ε) : v c ≤ y c + t ∧ y c + t ≤ v c + 1 := by
    have hmem : y + EuclideanSpace.single c t ∈ T := by
      apply hball
      simpa [dist_eq_norm, PiLp.norm_single] using ht
    simpa using hT hmem c
  have h1 := step (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  have h2 := step (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  constructor <;> linarith [h1.1, h2.2]

/-- `n ≤ k²` unit squares fit in a `k × k` square, in a grid. -/
theorem grid (n k : ℕ) (h : n ≤ k ^ 2) : UpperBound n k := by
  let pos : Fin n → Fin 2 → ℕ := fun i c => if c = 0 then i / k else i % k
  have pos_lt (i : Fin n) (c : Fin 2) : pos i c < k := by
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have := i.2; simp at h; omega
      · exact hk
    by_cases hc : c = 0
    · simp only [pos, hc, ite_true]
      exact Nat.div_lt_of_lt_mul (by nlinarith [i.2])
    · simp only [pos, hc, ite_false]
      exact Nat.mod_lt _ hk
  let v : Fin n → Plane := fun i => WithLp.toLp 2 fun c => (pos i c : ℝ)
  have hv (i : Fin n) (c : Fin 2) : v i c = pos i c := rfl
  have himage (i : Fin n) : AffineIsometryEquiv.constVAdd ℝ Plane (v i) '' square 1 ⊆
      {x | ∀ c, v i c ≤ x c ∧ x c ≤ v i c + 1} := by
    rintro _ ⟨x, hx, rfl⟩ c
    simp only [AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, PiLp.add_apply]
    constructor <;> linarith [hx c]
  refine ⟨fun i => AffineIsometryEquiv.constVAdd ℝ Plane (v i), Nat.cast_nonneg k, ?_, ?_⟩
  · intro i x hx c
    have := himage i hx c
    have hlt : (pos i c : ℝ) + 1 ≤ k := by exact_mod_cast pos_lt i c
    rw [hv] at this
    constructor <;> linarith [this.1, this.2, (pos i c).cast_nonneg (α := ℝ)]
  · intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    apply hij
    have same (c : Fin 2) : pos i c = pos j c := by
      have a := lt_of_mem_interior (himage i) hi c
      have b := lt_of_mem_interior (himage j) hj c
      rw [hv] at a b
      have : (pos i c : ℝ) < pos j c + 1 := by linarith [a.1, b.2]
      have : (pos j c : ℝ) < pos i c + 1 := by linarith [a.2, b.1]
      have : pos i c < pos j c + 1 := by exact_mod_cast ‹(pos i c : ℝ) < pos j c + 1›
      have : pos j c < pos i c + 1 := by exact_mod_cast ‹(pos j c : ℝ) < pos i c + 1›
      omega
    have h0 := same 0
    have h1 := same 1
    simp only [pos, ite_true, one_ne_zero, ite_false] at h0 h1
    ext
    rw [← Nat.div_add_mod i k, ← Nat.div_add_mod j k, h0, h1]

/-- `s(n) ≤ k` for `n ≤ k²`, as `√(k²)`. -/
theorem sqrtUpperBound (n k : ℕ) (h : n ≤ k ^ 2) : SqrtUpperBound n (k ^ 2) := by
  have : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = k := by push_cast; exact Real.sqrt_sq k.cast_nonneg
  rw [SqrtUpperBound, this]
  exact grid n k h

/-! Instances for `n = 1, ..., 100`. -/

theorem lower_1 : SqrtLowerBound 1 1 := sqrtLowerBound 1
theorem lower_2 : SqrtLowerBound 2 2 := sqrtLowerBound 2
theorem lower_3 : SqrtLowerBound 3 3 := sqrtLowerBound 3
theorem lower_4 : SqrtLowerBound 4 4 := sqrtLowerBound 4
theorem lower_5 : SqrtLowerBound 5 5 := sqrtLowerBound 5
theorem lower_6 : SqrtLowerBound 6 6 := sqrtLowerBound 6
theorem lower_7 : SqrtLowerBound 7 7 := sqrtLowerBound 7
theorem lower_8 : SqrtLowerBound 8 8 := sqrtLowerBound 8
theorem lower_9 : SqrtLowerBound 9 9 := sqrtLowerBound 9
theorem lower_10 : SqrtLowerBound 10 10 := sqrtLowerBound 10
theorem lower_11 : SqrtLowerBound 11 11 := sqrtLowerBound 11
theorem lower_12 : SqrtLowerBound 12 12 := sqrtLowerBound 12
theorem lower_13 : SqrtLowerBound 13 13 := sqrtLowerBound 13
theorem lower_14 : SqrtLowerBound 14 14 := sqrtLowerBound 14
theorem lower_15 : SqrtLowerBound 15 15 := sqrtLowerBound 15
theorem lower_16 : SqrtLowerBound 16 16 := sqrtLowerBound 16
theorem lower_17 : SqrtLowerBound 17 17 := sqrtLowerBound 17
theorem lower_18 : SqrtLowerBound 18 18 := sqrtLowerBound 18
theorem lower_19 : SqrtLowerBound 19 19 := sqrtLowerBound 19
theorem lower_20 : SqrtLowerBound 20 20 := sqrtLowerBound 20
theorem lower_21 : SqrtLowerBound 21 21 := sqrtLowerBound 21
theorem lower_22 : SqrtLowerBound 22 22 := sqrtLowerBound 22
theorem lower_23 : SqrtLowerBound 23 23 := sqrtLowerBound 23
theorem lower_24 : SqrtLowerBound 24 24 := sqrtLowerBound 24
theorem lower_25 : SqrtLowerBound 25 25 := sqrtLowerBound 25
theorem lower_26 : SqrtLowerBound 26 26 := sqrtLowerBound 26
theorem lower_27 : SqrtLowerBound 27 27 := sqrtLowerBound 27
theorem lower_28 : SqrtLowerBound 28 28 := sqrtLowerBound 28
theorem lower_29 : SqrtLowerBound 29 29 := sqrtLowerBound 29
theorem lower_30 : SqrtLowerBound 30 30 := sqrtLowerBound 30
theorem lower_31 : SqrtLowerBound 31 31 := sqrtLowerBound 31
theorem lower_32 : SqrtLowerBound 32 32 := sqrtLowerBound 32
theorem lower_33 : SqrtLowerBound 33 33 := sqrtLowerBound 33
theorem lower_34 : SqrtLowerBound 34 34 := sqrtLowerBound 34
theorem lower_35 : SqrtLowerBound 35 35 := sqrtLowerBound 35
theorem lower_36 : SqrtLowerBound 36 36 := sqrtLowerBound 36
theorem lower_37 : SqrtLowerBound 37 37 := sqrtLowerBound 37
theorem lower_38 : SqrtLowerBound 38 38 := sqrtLowerBound 38
theorem lower_39 : SqrtLowerBound 39 39 := sqrtLowerBound 39
theorem lower_40 : SqrtLowerBound 40 40 := sqrtLowerBound 40
theorem lower_41 : SqrtLowerBound 41 41 := sqrtLowerBound 41
theorem lower_42 : SqrtLowerBound 42 42 := sqrtLowerBound 42
theorem lower_43 : SqrtLowerBound 43 43 := sqrtLowerBound 43
theorem lower_44 : SqrtLowerBound 44 44 := sqrtLowerBound 44
theorem lower_45 : SqrtLowerBound 45 45 := sqrtLowerBound 45
theorem lower_46 : SqrtLowerBound 46 46 := sqrtLowerBound 46
theorem lower_47 : SqrtLowerBound 47 47 := sqrtLowerBound 47
theorem lower_48 : SqrtLowerBound 48 48 := sqrtLowerBound 48
theorem lower_49 : SqrtLowerBound 49 49 := sqrtLowerBound 49
theorem lower_50 : SqrtLowerBound 50 50 := sqrtLowerBound 50
theorem lower_51 : SqrtLowerBound 51 51 := sqrtLowerBound 51
theorem lower_52 : SqrtLowerBound 52 52 := sqrtLowerBound 52
theorem lower_53 : SqrtLowerBound 53 53 := sqrtLowerBound 53
theorem lower_54 : SqrtLowerBound 54 54 := sqrtLowerBound 54
theorem lower_55 : SqrtLowerBound 55 55 := sqrtLowerBound 55
theorem lower_56 : SqrtLowerBound 56 56 := sqrtLowerBound 56
theorem lower_57 : SqrtLowerBound 57 57 := sqrtLowerBound 57
theorem lower_58 : SqrtLowerBound 58 58 := sqrtLowerBound 58
theorem lower_59 : SqrtLowerBound 59 59 := sqrtLowerBound 59
theorem lower_60 : SqrtLowerBound 60 60 := sqrtLowerBound 60
theorem lower_61 : SqrtLowerBound 61 61 := sqrtLowerBound 61
theorem lower_62 : SqrtLowerBound 62 62 := sqrtLowerBound 62
theorem lower_63 : SqrtLowerBound 63 63 := sqrtLowerBound 63
theorem lower_64 : SqrtLowerBound 64 64 := sqrtLowerBound 64
theorem lower_65 : SqrtLowerBound 65 65 := sqrtLowerBound 65
theorem lower_66 : SqrtLowerBound 66 66 := sqrtLowerBound 66
theorem lower_67 : SqrtLowerBound 67 67 := sqrtLowerBound 67
theorem lower_68 : SqrtLowerBound 68 68 := sqrtLowerBound 68
theorem lower_69 : SqrtLowerBound 69 69 := sqrtLowerBound 69
theorem lower_70 : SqrtLowerBound 70 70 := sqrtLowerBound 70
theorem lower_71 : SqrtLowerBound 71 71 := sqrtLowerBound 71
theorem lower_72 : SqrtLowerBound 72 72 := sqrtLowerBound 72
theorem lower_73 : SqrtLowerBound 73 73 := sqrtLowerBound 73
theorem lower_74 : SqrtLowerBound 74 74 := sqrtLowerBound 74
theorem lower_75 : SqrtLowerBound 75 75 := sqrtLowerBound 75
theorem lower_76 : SqrtLowerBound 76 76 := sqrtLowerBound 76
theorem lower_77 : SqrtLowerBound 77 77 := sqrtLowerBound 77
theorem lower_78 : SqrtLowerBound 78 78 := sqrtLowerBound 78
theorem lower_79 : SqrtLowerBound 79 79 := sqrtLowerBound 79
theorem lower_80 : SqrtLowerBound 80 80 := sqrtLowerBound 80
theorem lower_81 : SqrtLowerBound 81 81 := sqrtLowerBound 81
theorem lower_82 : SqrtLowerBound 82 82 := sqrtLowerBound 82
theorem lower_83 : SqrtLowerBound 83 83 := sqrtLowerBound 83
theorem lower_84 : SqrtLowerBound 84 84 := sqrtLowerBound 84
theorem lower_85 : SqrtLowerBound 85 85 := sqrtLowerBound 85
theorem lower_86 : SqrtLowerBound 86 86 := sqrtLowerBound 86
theorem lower_87 : SqrtLowerBound 87 87 := sqrtLowerBound 87
theorem lower_88 : SqrtLowerBound 88 88 := sqrtLowerBound 88
theorem lower_89 : SqrtLowerBound 89 89 := sqrtLowerBound 89
theorem lower_90 : SqrtLowerBound 90 90 := sqrtLowerBound 90
theorem lower_91 : SqrtLowerBound 91 91 := sqrtLowerBound 91
theorem lower_92 : SqrtLowerBound 92 92 := sqrtLowerBound 92
theorem lower_93 : SqrtLowerBound 93 93 := sqrtLowerBound 93
theorem lower_94 : SqrtLowerBound 94 94 := sqrtLowerBound 94
theorem lower_95 : SqrtLowerBound 95 95 := sqrtLowerBound 95
theorem lower_96 : SqrtLowerBound 96 96 := sqrtLowerBound 96
theorem lower_97 : SqrtLowerBound 97 97 := sqrtLowerBound 97
theorem lower_98 : SqrtLowerBound 98 98 := sqrtLowerBound 98
theorem lower_99 : SqrtLowerBound 99 99 := sqrtLowerBound 99
theorem lower_100 : SqrtLowerBound 100 100 := sqrtLowerBound 100

theorem upper_1 : SqrtUpperBound 1 1 := sqrtUpperBound 1 1 (by norm_num)
theorem upper_2 : SqrtUpperBound 2 4 := sqrtUpperBound 2 2 (by norm_num)
theorem upper_3 : SqrtUpperBound 3 4 := sqrtUpperBound 3 2 (by norm_num)
theorem upper_4 : SqrtUpperBound 4 4 := sqrtUpperBound 4 2 (by norm_num)
theorem upper_5 : SqrtUpperBound 5 9 := sqrtUpperBound 5 3 (by norm_num)
theorem upper_6 : SqrtUpperBound 6 9 := sqrtUpperBound 6 3 (by norm_num)
theorem upper_7 : SqrtUpperBound 7 9 := sqrtUpperBound 7 3 (by norm_num)
theorem upper_8 : SqrtUpperBound 8 9 := sqrtUpperBound 8 3 (by norm_num)
theorem upper_9 : SqrtUpperBound 9 9 := sqrtUpperBound 9 3 (by norm_num)
theorem upper_10 : SqrtUpperBound 10 16 := sqrtUpperBound 10 4 (by norm_num)
theorem upper_11 : SqrtUpperBound 11 16 := sqrtUpperBound 11 4 (by norm_num)
theorem upper_12 : SqrtUpperBound 12 16 := sqrtUpperBound 12 4 (by norm_num)
theorem upper_13 : SqrtUpperBound 13 16 := sqrtUpperBound 13 4 (by norm_num)
theorem upper_14 : SqrtUpperBound 14 16 := sqrtUpperBound 14 4 (by norm_num)
theorem upper_15 : SqrtUpperBound 15 16 := sqrtUpperBound 15 4 (by norm_num)
theorem upper_16 : SqrtUpperBound 16 16 := sqrtUpperBound 16 4 (by norm_num)
theorem upper_17 : SqrtUpperBound 17 25 := sqrtUpperBound 17 5 (by norm_num)
theorem upper_18 : SqrtUpperBound 18 25 := sqrtUpperBound 18 5 (by norm_num)
theorem upper_19 : SqrtUpperBound 19 25 := sqrtUpperBound 19 5 (by norm_num)
theorem upper_20 : SqrtUpperBound 20 25 := sqrtUpperBound 20 5 (by norm_num)
theorem upper_21 : SqrtUpperBound 21 25 := sqrtUpperBound 21 5 (by norm_num)
theorem upper_22 : SqrtUpperBound 22 25 := sqrtUpperBound 22 5 (by norm_num)
theorem upper_23 : SqrtUpperBound 23 25 := sqrtUpperBound 23 5 (by norm_num)
theorem upper_24 : SqrtUpperBound 24 25 := sqrtUpperBound 24 5 (by norm_num)
theorem upper_25 : SqrtUpperBound 25 25 := sqrtUpperBound 25 5 (by norm_num)
theorem upper_26 : SqrtUpperBound 26 36 := sqrtUpperBound 26 6 (by norm_num)
theorem upper_27 : SqrtUpperBound 27 36 := sqrtUpperBound 27 6 (by norm_num)
theorem upper_28 : SqrtUpperBound 28 36 := sqrtUpperBound 28 6 (by norm_num)
theorem upper_29 : SqrtUpperBound 29 36 := sqrtUpperBound 29 6 (by norm_num)
theorem upper_30 : SqrtUpperBound 30 36 := sqrtUpperBound 30 6 (by norm_num)
theorem upper_31 : SqrtUpperBound 31 36 := sqrtUpperBound 31 6 (by norm_num)
theorem upper_32 : SqrtUpperBound 32 36 := sqrtUpperBound 32 6 (by norm_num)
theorem upper_33 : SqrtUpperBound 33 36 := sqrtUpperBound 33 6 (by norm_num)
theorem upper_34 : SqrtUpperBound 34 36 := sqrtUpperBound 34 6 (by norm_num)
theorem upper_35 : SqrtUpperBound 35 36 := sqrtUpperBound 35 6 (by norm_num)
theorem upper_36 : SqrtUpperBound 36 36 := sqrtUpperBound 36 6 (by norm_num)
theorem upper_37 : SqrtUpperBound 37 49 := sqrtUpperBound 37 7 (by norm_num)
theorem upper_38 : SqrtUpperBound 38 49 := sqrtUpperBound 38 7 (by norm_num)
theorem upper_39 : SqrtUpperBound 39 49 := sqrtUpperBound 39 7 (by norm_num)
theorem upper_40 : SqrtUpperBound 40 49 := sqrtUpperBound 40 7 (by norm_num)
theorem upper_41 : SqrtUpperBound 41 49 := sqrtUpperBound 41 7 (by norm_num)
theorem upper_42 : SqrtUpperBound 42 49 := sqrtUpperBound 42 7 (by norm_num)
theorem upper_43 : SqrtUpperBound 43 49 := sqrtUpperBound 43 7 (by norm_num)
theorem upper_44 : SqrtUpperBound 44 49 := sqrtUpperBound 44 7 (by norm_num)
theorem upper_45 : SqrtUpperBound 45 49 := sqrtUpperBound 45 7 (by norm_num)
theorem upper_46 : SqrtUpperBound 46 49 := sqrtUpperBound 46 7 (by norm_num)
theorem upper_47 : SqrtUpperBound 47 49 := sqrtUpperBound 47 7 (by norm_num)
theorem upper_48 : SqrtUpperBound 48 49 := sqrtUpperBound 48 7 (by norm_num)
theorem upper_49 : SqrtUpperBound 49 49 := sqrtUpperBound 49 7 (by norm_num)
theorem upper_50 : SqrtUpperBound 50 64 := sqrtUpperBound 50 8 (by norm_num)
theorem upper_51 : SqrtUpperBound 51 64 := sqrtUpperBound 51 8 (by norm_num)
theorem upper_52 : SqrtUpperBound 52 64 := sqrtUpperBound 52 8 (by norm_num)
theorem upper_53 : SqrtUpperBound 53 64 := sqrtUpperBound 53 8 (by norm_num)
theorem upper_54 : SqrtUpperBound 54 64 := sqrtUpperBound 54 8 (by norm_num)
theorem upper_55 : SqrtUpperBound 55 64 := sqrtUpperBound 55 8 (by norm_num)
theorem upper_56 : SqrtUpperBound 56 64 := sqrtUpperBound 56 8 (by norm_num)
theorem upper_57 : SqrtUpperBound 57 64 := sqrtUpperBound 57 8 (by norm_num)
theorem upper_58 : SqrtUpperBound 58 64 := sqrtUpperBound 58 8 (by norm_num)
theorem upper_59 : SqrtUpperBound 59 64 := sqrtUpperBound 59 8 (by norm_num)
theorem upper_60 : SqrtUpperBound 60 64 := sqrtUpperBound 60 8 (by norm_num)
theorem upper_61 : SqrtUpperBound 61 64 := sqrtUpperBound 61 8 (by norm_num)
theorem upper_62 : SqrtUpperBound 62 64 := sqrtUpperBound 62 8 (by norm_num)
theorem upper_63 : SqrtUpperBound 63 64 := sqrtUpperBound 63 8 (by norm_num)
theorem upper_64 : SqrtUpperBound 64 64 := sqrtUpperBound 64 8 (by norm_num)
theorem upper_65 : SqrtUpperBound 65 81 := sqrtUpperBound 65 9 (by norm_num)
theorem upper_66 : SqrtUpperBound 66 81 := sqrtUpperBound 66 9 (by norm_num)
theorem upper_67 : SqrtUpperBound 67 81 := sqrtUpperBound 67 9 (by norm_num)
theorem upper_68 : SqrtUpperBound 68 81 := sqrtUpperBound 68 9 (by norm_num)
theorem upper_69 : SqrtUpperBound 69 81 := sqrtUpperBound 69 9 (by norm_num)
theorem upper_70 : SqrtUpperBound 70 81 := sqrtUpperBound 70 9 (by norm_num)
theorem upper_71 : SqrtUpperBound 71 81 := sqrtUpperBound 71 9 (by norm_num)
theorem upper_72 : SqrtUpperBound 72 81 := sqrtUpperBound 72 9 (by norm_num)
theorem upper_73 : SqrtUpperBound 73 81 := sqrtUpperBound 73 9 (by norm_num)
theorem upper_74 : SqrtUpperBound 74 81 := sqrtUpperBound 74 9 (by norm_num)
theorem upper_75 : SqrtUpperBound 75 81 := sqrtUpperBound 75 9 (by norm_num)
theorem upper_76 : SqrtUpperBound 76 81 := sqrtUpperBound 76 9 (by norm_num)
theorem upper_77 : SqrtUpperBound 77 81 := sqrtUpperBound 77 9 (by norm_num)
theorem upper_78 : SqrtUpperBound 78 81 := sqrtUpperBound 78 9 (by norm_num)
theorem upper_79 : SqrtUpperBound 79 81 := sqrtUpperBound 79 9 (by norm_num)
theorem upper_80 : SqrtUpperBound 80 81 := sqrtUpperBound 80 9 (by norm_num)
theorem upper_81 : SqrtUpperBound 81 81 := sqrtUpperBound 81 9 (by norm_num)
theorem upper_82 : SqrtUpperBound 82 100 := sqrtUpperBound 82 10 (by norm_num)
theorem upper_83 : SqrtUpperBound 83 100 := sqrtUpperBound 83 10 (by norm_num)
theorem upper_84 : SqrtUpperBound 84 100 := sqrtUpperBound 84 10 (by norm_num)
theorem upper_85 : SqrtUpperBound 85 100 := sqrtUpperBound 85 10 (by norm_num)
theorem upper_86 : SqrtUpperBound 86 100 := sqrtUpperBound 86 10 (by norm_num)
theorem upper_87 : SqrtUpperBound 87 100 := sqrtUpperBound 87 10 (by norm_num)
theorem upper_88 : SqrtUpperBound 88 100 := sqrtUpperBound 88 10 (by norm_num)
theorem upper_89 : SqrtUpperBound 89 100 := sqrtUpperBound 89 10 (by norm_num)
theorem upper_90 : SqrtUpperBound 90 100 := sqrtUpperBound 90 10 (by norm_num)
theorem upper_91 : SqrtUpperBound 91 100 := sqrtUpperBound 91 10 (by norm_num)
theorem upper_92 : SqrtUpperBound 92 100 := sqrtUpperBound 92 10 (by norm_num)
theorem upper_93 : SqrtUpperBound 93 100 := sqrtUpperBound 93 10 (by norm_num)
theorem upper_94 : SqrtUpperBound 94 100 := sqrtUpperBound 94 10 (by norm_num)
theorem upper_95 : SqrtUpperBound 95 100 := sqrtUpperBound 95 10 (by norm_num)
theorem upper_96 : SqrtUpperBound 96 100 := sqrtUpperBound 96 10 (by norm_num)
theorem upper_97 : SqrtUpperBound 97 100 := sqrtUpperBound 97 10 (by norm_num)
theorem upper_98 : SqrtUpperBound 98 100 := sqrtUpperBound 98 10 (by norm_num)
theorem upper_99 : SqrtUpperBound 99 100 := sqrtUpperBound 99 10 (by norm_num)
theorem upper_100 : SqrtUpperBound 100 100 := sqrtUpperBound 100 10 (by norm_num)

end LeapsInBounds.Proofs.SquarePackingBasic
