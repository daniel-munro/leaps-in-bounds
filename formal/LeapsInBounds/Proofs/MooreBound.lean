module

public import LeapsInBounds.Statements.Cage
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The Moore bound for cages

A `k`-regular graph of girth `g` has at least as many vertices as the Moore
bound:

- `g = 2d + 1`: `1 + k + k(k-1) + ... + k(k-1)^(d-1)`, counting paths of
  length at most `d` into a vertex.
- `g = 2d`: `2(1 + (k-1) + ... + (k-1)^(d-1))`, counting paths of length less
  than `d` into either end of an edge that avoid the other end.

In both cases two of these paths with the same start would form a cycle
shorter than `g`, so their starts are distinct vertices.
-/

public section

namespace LeapsInBounds.Proofs.MooreBound

open SimpleGraph Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Two paths with the same ends and total length less than the girth are equal. -/
lemma eq_of_isPath {n : ℕ} (hg : (n : ℕ∞) < G.egirth) {a b : V} {p q : G.Walk a b}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length ≤ n) : p = q := by
  by_contra h
  obtain ⟨_, -, -, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne hq h
  have : (c.length : ℕ∞) ≤ n := by exact_mod_cast hcl.trans hlen
  exact absurd (hc.egirth_le_length.trans this) (not_le.mpr hg)

variable (G) in
/-- Paths of length `i` into `v` that avoid the vertices `F`, with their starts. -/
noncomputable def paths (v : V) (F : Finset V) (i : ℕ) : Finset (Σ w, G.Walk w v) :=
  univ.sigma fun w => (G.finsetWalkLength i w v).filter fun p => p.IsPath ∧ ∀ u ∈ F, u ∉ p.support

lemma mem_paths {v : V} {F : Finset V} {i : ℕ} {p : Σ w, G.Walk w v} :
    p ∈ paths G v F i ↔ p.2.length = i ∧ p.2.IsPath ∧ ∀ u ∈ F, u ∉ p.2.support := by
  simp [paths, mem_finsetWalkLength_iff]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The only neighbor of the start of a path `P` into `v` that lies on `P` or
in `F` (neighbors of `v` off `P`) is the second vertex of `P`. -/
lemma eq_snd {v w x : V} {F : Finset V} (hF : ∀ u ∈ F, G.Adj u v) {i : ℕ}
    (hg : ((i + 2 : ℕ) : ℕ∞) < G.egirth) (P : G.Walk w v) (hP : P.IsPath) (hlen : P.length = i)
    (hi : 1 ≤ i) (hFP : ∀ u ∈ F, u ∉ P.support) (hx : G.Adj w x) (hxP : x ∈ P.support ∨ x ∈ F) :
    x = P.snd := by
  rcases hxP with hxP | hxF
  · -- `P` up to `x`, and the edge `wx`, are paths from `w` to `x`
    have hxw : x ≠ w := hx.ne.symm
    have heq := eq_of_isPath (n := i + 1) (lt_of_le_of_lt (by norm_cast; omega) hg)
      (hP.takeUntil hxP) (q := Walk.cons hx Walk.nil) (by simpa using hxw.symm)
      (by have := P.length_takeUntil_le_length hxP; simp; omega)
    rw [← P.snd_takeUntil hxw hxP, heq]
    simp
  · -- `xwP` and the edge `xv` are paths from `x` to `v`
    have hxv := hF x hxF
    have heq := eq_of_isPath (n := i + 2) hg (p := Walk.cons hx.symm P)
      (q := Walk.cons hxv Walk.nil) (by simpa using ⟨hP, hFP x hxF⟩) (by simpa using hxv.ne)
      (by simp; omega)
    have := congrArg Walk.length heq
    simp only [Walk.length_cons, Walk.length_nil] at this
    omega


/-- Each path in `paths v F i` extends to at least `k - 1` paths in
`paths v F (i + 1)`. -/
lemma card_paths_succ {k : ℕ} (hreg : ∀ w, G.degree w = k) {v : V} {F : Finset V}
    (hF : ∀ u ∈ F, G.Adj u v) {i : ℕ} (hi : 1 ≤ i) (hg : ((i + 2 : ℕ) : ℕ∞) < G.egirth) :
    (k - 1) * #(paths G v F i) ≤ #(paths G v F (i + 1)) := by
  let ext (P : Σ w, G.Walk w v) : Finset V :=
    (G.neighborFinset P.1).filter fun x => x ∉ P.2.support ∧ x ∉ F
  let f (Px : Σ _ : (Σ w, G.Walk w v), V) : Σ w, G.Walk w v :=
    if h : G.Adj Px.2 Px.1.1 then ⟨Px.2, Walk.cons h Px.1.2⟩ else Px.1
  have hext : ∀ P ∈ paths G v F i, k - 1 ≤ #(ext P) := by
    intro P hP
    change k - 1 ≤ #((G.neighborFinset P.1).filter fun x => x ∉ P.2.support ∧ x ∉ F)
    rw [mem_paths] at hP
    obtain ⟨hlen, hpath, hFP⟩ := hP
    have hsub : (G.neighborFinset P.1).filter (fun x => ¬ (x ∉ P.2.support ∧ x ∉ F)) ⊆
        {P.2.snd} := by
      intro x hx
      simp only [mem_filter, mem_neighborFinset, not_and_or, not_not] at hx
      simpa using eq_snd hF hg P.2 hpath hlen hi hFP hx.1 hx.2
    have := card_le_card hsub
    have := card_filter_add_card_filter_not (s := G.neighborFinset P.1)
      (fun x => x ∉ P.2.support ∧ x ∉ F)
    rw [card_neighborFinset_eq_degree, hreg] at this
    simp only [card_singleton] at *
    omega
  calc (k - 1) * #(paths G v F i)
      = ∑ _P ∈ paths G v F i, (k - 1) := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ P ∈ paths G v F i, #(ext P) := sum_le_sum hext
    _ = #((paths G v F i).sigma ext) := (card_sigma _ _).symm
    _ ≤ #(paths G v F (i + 1)) := by
      apply card_le_card_of_injOn f
      · intro ⟨P, x⟩ hPx
        simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, ext, mem_filter,
          mem_neighborFinset] at hPx
        obtain ⟨hP, hx, hxP, hxF⟩ := hPx
        rw [mem_paths] at hP
        rw [mem_coe, mem_paths]
        simp only [f]
        rw [dite_eq_left hx.symm]
        simp only [Walk.length_cons, cons_isPath_iff, support_cons, List.mem_cons, not_or]
        exact ⟨by omega, ⟨hP.2.1, hxP⟩, fun u hu => ⟨fun h => hxF (h ▸ hu), hP.2.2 u hu⟩⟩
      · intro ⟨P, x⟩ hPx ⟨Q, y⟩ hQy heq
        simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, ext, mem_filter,
          mem_neighborFinset] at hPx hQy
        simp only [f] at heq
        rw [dite_eq_left hPx.2.1.symm, dite_eq_left hQy.2.1.symm, Sigma.mk.injEq] at heq
        obtain ⟨rfl, heq⟩ := heq
        obtain ⟨w, P⟩ := P
        obtain ⟨w', Q⟩ := Q
        simp only [heq_eq_eq, Walk.cons.injEq] at heq
        obtain ⟨rfl, -, heq⟩ := heq
        simp_all

lemma card_paths_one {k : ℕ} (hreg : ∀ w, G.degree w = k) {v : V} {F : Finset V}
    (hF : ∀ u ∈ F, G.Adj u v) : k - #F ≤ #(paths G v F 1) := by
  have hFv : F ⊆ G.neighborFinset v := fun u hu => by simpa using (hF u hu).symm
  have := card_sdiff_add_card_inter (G.neighborFinset v) F
  rw [inter_eq_right.mpr hFv, card_neighborFinset_eq_degree, hreg] at this
  calc k - #F = #(G.neighborFinset v \ F) := by omega
    _ ≤ #(paths G v F 1) := by
      apply card_le_card_of_injOn
        (fun x => if h : G.Adj x v then (⟨x, Walk.cons h Walk.nil⟩ : Σ w, G.Walk w v)
          else ⟨v, Walk.nil⟩)
      · intro x hx
        simp only [coe_sdiff, Set.mem_sdiff, mem_coe, mem_neighborFinset] at hx
        dsimp only
        rw [dite_eq_left hx.1.symm]
        simp only [mem_coe, mem_paths, Walk.length_cons, Walk.length_nil,
          cons_isPath_iff, support_cons, support_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        refine ⟨by simp, ⟨IsPath.nil, by simpa using hx.1.ne.symm⟩, fun u hu => ⟨?_, ?_⟩⟩
        · rintro rfl; exact hx.2 hu
        · rintro rfl; exact (hF u hu).ne rfl
      · intro x hx y hy heq
        simp only [coe_sdiff, Set.mem_sdiff, mem_coe, mem_neighborFinset] at hx hy
        dsimp only at heq
        rw [dite_eq_left hx.1.symm, dite_eq_left hy.1.symm, Sigma.mk.injEq] at heq
        exact heq.1

/-- `1 + (k - |F|)(1 + (k-1) + ... + (k-1)^(D-1))` paths of length at most `D`. -/
lemma sum_card_paths {k : ℕ} (hreg : ∀ w, G.degree w = k) {v : V} {F : Finset V}
    (hF : ∀ u ∈ F, G.Adj u v) (hvF : v ∉ F) {D : ℕ} (hg : ((D + 1 : ℕ) : ℕ∞) < G.egirth) :
    1 + (k - #F) * ∑ j ∈ range D, (k - 1) ^ j ≤ ∑ i ∈ range (D + 1), #(paths G v F i) := by
  have hlevel : ∀ i < D, (k - #F) * (k - 1) ^ i ≤ #(paths G v F (i + 1)) := by
    intro i hi
    induction i with
    | zero => simpa using card_paths_one hreg hF
    | succ i ih =>
      have := card_paths_succ hreg hF (i := i + 1) (by omega)
        (lt_of_le_of_lt (by norm_cast; omega) hg)
      calc (k - #F) * (k - 1) ^ (i + 1) = (k - 1) * ((k - #F) * (k - 1) ^ i) := by
            rw [pow_succ, ← mul_assoc, mul_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ _ := this
  have hzero : 1 ≤ #(paths G v F 0) :=
    card_pos.mpr ⟨⟨v, Walk.nil⟩, by
      simp only [mem_paths, Walk.length_nil, support_nil, List.mem_singleton, true_and]
      exact ⟨IsPath.nil, fun u hu h => hvF (h ▸ hu)⟩⟩
  rw [sum_range_succ', mul_sum, add_comm]
  exact Nat.add_le_add (sum_le_sum fun i hi => hlevel i (mem_range.mp hi)) hzero

/-- Starts of the paths of length at most `D` in `paths v F`. -/
noncomputable def starts (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (F : Finset V)
    (D : ℕ) : Finset V :=
  ((range (D + 1)).biUnion (paths G v F)).image Sigma.fst

/-- Paths of length at most `D` with `2D` less than the girth have distinct starts. -/
lemma card_starts {v : V} {F : Finset V} {D : ℕ} (hg : ((2 * D : ℕ) : ℕ∞) < G.egirth) :
    #(starts G v F D) = ∑ i ∈ range (D + 1), #(paths G v F i) := by
  rw [starts, card_image_of_injOn, card_biUnion]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro P hi hj
    rw [mem_paths] at hi hj
    exact hij (hi.1.symm.trans hj.1)
  · intro ⟨w, P⟩ hP ⟨w', Q⟩ hQ (heq : w = w')
    subst heq
    simp only [coe_biUnion, coe_range, Set.mem_Iio, mem_coe, Set.mem_iUnion, mem_paths,
      exists_prop] at hP hQ
    obtain ⟨i, hi, rfl, hP, -⟩ := hP
    obtain ⟨j, hj, rfl, hQ, -⟩ := hQ
    rw [eq_of_isPath hg hP hQ (by omega)]

/-- Moore bound for odd girth `2d + 1`. -/
theorem odd (k d : ℕ) : Cage.LowerBound k (2 * d + 1) (1 + k * ∑ j ∈ range d, (k - 1) ^ j) := by
  intro m hm G ⟨hreg, hgirth⟩
  classical
  have hdeg (w : Fin m) : G.degree w = k := by
    rw [← hreg w, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  obtain ⟨v⟩ : Nonempty (Fin m) := by
    by_contra h
    have : G.IsAcyclic := fun v => (h ⟨v⟩).elim
    rw [← egirth_eq_top] at this
    rw [this] at hgirth
    exact ENat.top_ne_natCast _ (by rw [hgirth])
  have h3 : 3 ≤ 2 * d + 1 := by
    have := G.three_le_egirth
    rw [hgirth] at this
    exact_mod_cast this
  have h1 := sum_card_paths hdeg (v := v) (F := ∅) (by simp) (by simp) (D := d)
    (by rw [hgirth]; norm_cast; omega)
  rw [← card_starts (by rw [hgirth]; norm_cast; omega)] at h1
  have := card_le_univ (starts G v ∅ d)
  simp only [card_empty, Nat.sub_zero, Fintype.card_fin] at h1 this
  omega

/-- Moore bound for even girth `2d`. -/
theorem even (k d : ℕ) (hk : 0 < k) :
    Cage.LowerBound k (2 * d) (2 * (1 + (k - 1) * ∑ j ∈ range (d - 1), (k - 1) ^ j)) := by
  intro m hm G ⟨hreg, hgirth⟩
  classical
  have hdeg (w : Fin m) : G.degree w = k := by
    rw [← hreg w, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  obtain ⟨v⟩ : Nonempty (Fin m) := by
    by_contra h
    have : G.IsAcyclic := fun v => (h ⟨v⟩).elim
    rw [← egirth_eq_top] at this
    rw [this] at hgirth
    exact ENat.top_ne_natCast _ (by rw [hgirth])
  obtain ⟨u, hu⟩ : ∃ u, G.Adj v u := by
    obtain ⟨u, hu⟩ := card_pos.mp ((hdeg v).symm ▸ hk : 0 < G.degree v)
    exact ⟨u, by simpa using hu⟩
  have h3 : 3 ≤ 2 * d := by
    have := G.three_le_egirth
    rw [hgirth] at this
    exact_mod_cast this
  have hg1 : (((d - 1) + 1 : ℕ) : ℕ∞) < G.egirth := by rw [hgirth]; norm_cast; omega
  have hg2 : ((2 * (d - 1) : ℕ) : ℕ∞) < G.egirth := by rw [hgirth]; norm_cast; omega
  have hv := sum_card_paths hdeg (v := v) (F := {u}) (by simpa using hu.symm) (by simpa using hu.ne)
    hg1
  have hu' := sum_card_paths hdeg (v := u) (F := {v}) (by simpa using hu) (by simpa using hu.ne.symm)
    hg1
  rw [← card_starts hg2] at hv hu'
  -- A path `P` from `w` to `v` avoiding `u`, and a path `Q` from `w` to `u` avoiding `v`,
  -- would give two paths `P` and `Q` then `uv` from `w` to `v`
  have hdisj : Disjoint (starts G v {u} (d - 1)) (starts G u {v} (d - 1)) := by
    rw [Finset.disjoint_left]
    intro w hwv hwu
    simp only [starts, mem_image, mem_biUnion, mem_range, mem_paths] at hwv hwu
    obtain ⟨⟨w, P⟩, ⟨i, hi, hPl, hP, hPu⟩, rfl⟩ := hwv
    obtain ⟨⟨w, Q⟩, ⟨j, hj, hQl, hQ, hQv⟩, heq⟩ := hwu
    dsimp only at hPl hP hPu hQl hQ hQv heq
    subst heq
    have heq := eq_of_isPath (n := 2 * d - 1) (by rw [hgirth]; norm_cast; omega)
      (p := P.reverse) (q := Walk.cons hu Q.reverse) hP.reverse
      (by simpa using ⟨hQ, by simpa using hQv⟩) (by simp; omega)
    have : u ∈ P.reverse.support := by rw [heq]; simp
    exact hPu u (by simp) (by simpa using this)
  have := card_le_univ (starts G v {u} (d - 1) ∪ starts G u {v} (d - 1))
  rw [card_union_of_disjoint hdisj, Fintype.card_fin] at this
  simp only [card_singleton] at hv hu'
  omega

/-! Certificates, one per constant. -/

theorem lower_3_5 : Cage.LowerBound 3 5 10 := by simpa [sum_range_succ] using odd 3 2
theorem lower_4_5 : Cage.LowerBound 4 5 17 := by simpa [sum_range_succ] using odd 4 2
theorem lower_5_5 : Cage.LowerBound 5 5 26 := by simpa [sum_range_succ] using odd 5 2
theorem lower_6_5 : Cage.LowerBound 6 5 37 := by simpa [sum_range_succ] using odd 6 2
theorem lower_7_5 : Cage.LowerBound 7 5 50 := by simpa [sum_range_succ] using odd 7 2
theorem lower_8_5 : Cage.LowerBound 8 5 65 := by simpa [sum_range_succ] using odd 8 2
theorem lower_9_5 : Cage.LowerBound 9 5 82 := by simpa [sum_range_succ] using odd 9 2
theorem lower_10_5 : Cage.LowerBound 10 5 101 := by simpa [sum_range_succ] using odd 10 2
theorem lower_11_5 : Cage.LowerBound 11 5 122 := by simpa [sum_range_succ] using odd 11 2
theorem lower_12_5 : Cage.LowerBound 12 5 145 := by simpa [sum_range_succ] using odd 12 2
theorem lower_13_5 : Cage.LowerBound 13 5 170 := by simpa [sum_range_succ] using odd 13 2
theorem lower_14_5 : Cage.LowerBound 14 5 197 := by simpa [sum_range_succ] using odd 14 2
theorem lower_15_5 : Cage.LowerBound 15 5 226 := by simpa [sum_range_succ] using odd 15 2
theorem lower_16_5 : Cage.LowerBound 16 5 257 := by simpa [sum_range_succ] using odd 16 2
theorem lower_17_5 : Cage.LowerBound 17 5 290 := by simpa [sum_range_succ] using odd 17 2
theorem lower_18_5 : Cage.LowerBound 18 5 325 := by simpa [sum_range_succ] using odd 18 2
theorem lower_19_5 : Cage.LowerBound 19 5 362 := by simpa [sum_range_succ] using odd 19 2
theorem lower_20_5 : Cage.LowerBound 20 5 401 := by simpa [sum_range_succ] using odd 20 2
theorem lower_3_6 : Cage.LowerBound 3 6 14 := by simpa [sum_range_succ] using even 3 3 (by decide)
theorem lower_4_6 : Cage.LowerBound 4 6 26 := by simpa [sum_range_succ] using even 4 3 (by decide)
theorem lower_5_6 : Cage.LowerBound 5 6 42 := by simpa [sum_range_succ] using even 5 3 (by decide)
theorem lower_6_6 : Cage.LowerBound 6 6 62 := by simpa [sum_range_succ] using even 6 3 (by decide)
theorem lower_7_6 : Cage.LowerBound 7 6 86 := by simpa [sum_range_succ] using even 7 3 (by decide)
theorem lower_8_6 : Cage.LowerBound 8 6 114 := by simpa [sum_range_succ] using even 8 3 (by decide)
theorem lower_9_6 : Cage.LowerBound 9 6 146 := by simpa [sum_range_succ] using even 9 3 (by decide)
theorem lower_10_6 : Cage.LowerBound 10 6 182 := by simpa [sum_range_succ] using even 10 3 (by decide)
theorem lower_11_6 : Cage.LowerBound 11 6 222 := by simpa [sum_range_succ] using even 11 3 (by decide)
theorem lower_12_6 : Cage.LowerBound 12 6 266 := by simpa [sum_range_succ] using even 12 3 (by decide)
theorem lower_13_6 : Cage.LowerBound 13 6 314 := by simpa [sum_range_succ] using even 13 3 (by decide)
theorem lower_14_6 : Cage.LowerBound 14 6 366 := by simpa [sum_range_succ] using even 14 3 (by decide)
theorem lower_15_6 : Cage.LowerBound 15 6 422 := by simpa [sum_range_succ] using even 15 3 (by decide)
theorem lower_16_6 : Cage.LowerBound 16 6 482 := by simpa [sum_range_succ] using even 16 3 (by decide)
theorem lower_17_6 : Cage.LowerBound 17 6 546 := by simpa [sum_range_succ] using even 17 3 (by decide)
theorem lower_18_6 : Cage.LowerBound 18 6 614 := by simpa [sum_range_succ] using even 18 3 (by decide)
theorem lower_19_6 : Cage.LowerBound 19 6 686 := by simpa [sum_range_succ] using even 19 3 (by decide)
theorem lower_20_6 : Cage.LowerBound 20 6 762 := by simpa [sum_range_succ] using even 20 3 (by decide)
theorem lower_3_7 : Cage.LowerBound 3 7 22 := by simpa [sum_range_succ] using odd 3 3
theorem lower_4_7 : Cage.LowerBound 4 7 53 := by simpa [sum_range_succ] using odd 4 3
theorem lower_5_7 : Cage.LowerBound 5 7 106 := by simpa [sum_range_succ] using odd 5 3
theorem lower_6_7 : Cage.LowerBound 6 7 187 := by simpa [sum_range_succ] using odd 6 3
theorem lower_7_7 : Cage.LowerBound 7 7 302 := by simpa [sum_range_succ] using odd 7 3
theorem lower_8_7 : Cage.LowerBound 8 7 457 := by simpa [sum_range_succ] using odd 8 3
theorem lower_9_7 : Cage.LowerBound 9 7 658 := by simpa [sum_range_succ] using odd 9 3
theorem lower_10_7 : Cage.LowerBound 10 7 911 := by simpa [sum_range_succ] using odd 10 3
theorem lower_11_7 : Cage.LowerBound 11 7 1222 := by simpa [sum_range_succ] using odd 11 3
theorem lower_12_7 : Cage.LowerBound 12 7 1597 := by simpa [sum_range_succ] using odd 12 3
theorem lower_13_7 : Cage.LowerBound 13 7 2042 := by simpa [sum_range_succ] using odd 13 3
theorem lower_14_7 : Cage.LowerBound 14 7 2563 := by simpa [sum_range_succ] using odd 14 3
theorem lower_15_7 : Cage.LowerBound 15 7 3166 := by simpa [sum_range_succ] using odd 15 3
theorem lower_16_7 : Cage.LowerBound 16 7 3857 := by simpa [sum_range_succ] using odd 16 3
theorem lower_17_7 : Cage.LowerBound 17 7 4642 := by simpa [sum_range_succ] using odd 17 3
theorem lower_18_7 : Cage.LowerBound 18 7 5527 := by simpa [sum_range_succ] using odd 18 3
theorem lower_19_7 : Cage.LowerBound 19 7 6518 := by simpa [sum_range_succ] using odd 19 3
theorem lower_20_7 : Cage.LowerBound 20 7 7621 := by simpa [sum_range_succ] using odd 20 3
theorem lower_3_8 : Cage.LowerBound 3 8 30 := by simpa [sum_range_succ] using even 3 4 (by decide)
theorem lower_4_8 : Cage.LowerBound 4 8 80 := by simpa [sum_range_succ] using even 4 4 (by decide)
theorem lower_5_8 : Cage.LowerBound 5 8 170 := by simpa [sum_range_succ] using even 5 4 (by decide)
theorem lower_6_8 : Cage.LowerBound 6 8 312 := by simpa [sum_range_succ] using even 6 4 (by decide)
theorem lower_7_8 : Cage.LowerBound 7 8 518 := by simpa [sum_range_succ] using even 7 4 (by decide)
theorem lower_8_8 : Cage.LowerBound 8 8 800 := by simpa [sum_range_succ] using even 8 4 (by decide)
theorem lower_9_8 : Cage.LowerBound 9 8 1170 := by simpa [sum_range_succ] using even 9 4 (by decide)
theorem lower_10_8 : Cage.LowerBound 10 8 1640 := by simpa [sum_range_succ] using even 10 4 (by decide)
theorem lower_11_8 : Cage.LowerBound 11 8 2222 := by simpa [sum_range_succ] using even 11 4 (by decide)
theorem lower_12_8 : Cage.LowerBound 12 8 2928 := by simpa [sum_range_succ] using even 12 4 (by decide)
theorem lower_13_8 : Cage.LowerBound 13 8 3770 := by simpa [sum_range_succ] using even 13 4 (by decide)
theorem lower_14_8 : Cage.LowerBound 14 8 4760 := by simpa [sum_range_succ] using even 14 4 (by decide)
theorem lower_15_8 : Cage.LowerBound 15 8 5910 := by simpa [sum_range_succ] using even 15 4 (by decide)
theorem lower_16_8 : Cage.LowerBound 16 8 7232 := by simpa [sum_range_succ] using even 16 4 (by decide)
theorem lower_17_8 : Cage.LowerBound 17 8 8738 := by simpa [sum_range_succ] using even 17 4 (by decide)
theorem lower_18_8 : Cage.LowerBound 18 8 10440 := by simpa [sum_range_succ] using even 18 4 (by decide)
theorem lower_19_8 : Cage.LowerBound 19 8 12350 := by simpa [sum_range_succ] using even 19 4 (by decide)
theorem lower_20_8 : Cage.LowerBound 20 8 14480 := by simpa [sum_range_succ] using even 20 4 (by decide)
theorem lower_3_9 : Cage.LowerBound 3 9 46 := by simpa [sum_range_succ] using odd 3 4
theorem lower_4_9 : Cage.LowerBound 4 9 161 := by simpa [sum_range_succ] using odd 4 4
theorem lower_5_9 : Cage.LowerBound 5 9 426 := by simpa [sum_range_succ] using odd 5 4
theorem lower_6_9 : Cage.LowerBound 6 9 937 := by simpa [sum_range_succ] using odd 6 4
theorem lower_7_9 : Cage.LowerBound 7 9 1814 := by simpa [sum_range_succ] using odd 7 4
theorem lower_8_9 : Cage.LowerBound 8 9 3201 := by simpa [sum_range_succ] using odd 8 4
theorem lower_9_9 : Cage.LowerBound 9 9 5266 := by simpa [sum_range_succ] using odd 9 4
theorem lower_10_9 : Cage.LowerBound 10 9 8201 := by simpa [sum_range_succ] using odd 10 4
theorem lower_11_9 : Cage.LowerBound 11 9 12222 := by simpa [sum_range_succ] using odd 11 4
theorem lower_12_9 : Cage.LowerBound 12 9 17569 := by simpa [sum_range_succ] using odd 12 4
theorem lower_13_9 : Cage.LowerBound 13 9 24506 := by simpa [sum_range_succ] using odd 13 4
theorem lower_14_9 : Cage.LowerBound 14 9 33321 := by simpa [sum_range_succ] using odd 14 4
theorem lower_15_9 : Cage.LowerBound 15 9 44326 := by simpa [sum_range_succ] using odd 15 4
theorem lower_16_9 : Cage.LowerBound 16 9 57857 := by simpa [sum_range_succ] using odd 16 4
theorem lower_17_9 : Cage.LowerBound 17 9 74274 := by simpa [sum_range_succ] using odd 17 4
theorem lower_18_9 : Cage.LowerBound 18 9 93961 := by simpa [sum_range_succ] using odd 18 4
theorem lower_19_9 : Cage.LowerBound 19 9 117326 := by simpa [sum_range_succ] using odd 19 4
theorem lower_20_9 : Cage.LowerBound 20 9 144801 := by simpa [sum_range_succ] using odd 20 4
theorem lower_3_10 : Cage.LowerBound 3 10 62 := by simpa [sum_range_succ] using even 3 5 (by decide)
theorem lower_4_10 : Cage.LowerBound 4 10 242 := by simpa [sum_range_succ] using even 4 5 (by decide)
theorem lower_5_10 : Cage.LowerBound 5 10 682 := by simpa [sum_range_succ] using even 5 5 (by decide)
theorem lower_6_10 : Cage.LowerBound 6 10 1562 := by simpa [sum_range_succ] using even 6 5 (by decide)
theorem lower_7_10 : Cage.LowerBound 7 10 3110 := by simpa [sum_range_succ] using even 7 5 (by decide)
theorem lower_8_10 : Cage.LowerBound 8 10 5602 := by simpa [sum_range_succ] using even 8 5 (by decide)
theorem lower_9_10 : Cage.LowerBound 9 10 9362 := by simpa [sum_range_succ] using even 9 5 (by decide)
theorem lower_10_10 : Cage.LowerBound 10 10 14762 := by simpa [sum_range_succ] using even 10 5 (by decide)
theorem lower_11_10 : Cage.LowerBound 11 10 22222 := by simpa [sum_range_succ] using even 11 5 (by decide)
theorem lower_12_10 : Cage.LowerBound 12 10 32210 := by simpa [sum_range_succ] using even 12 5 (by decide)
theorem lower_13_10 : Cage.LowerBound 13 10 45242 := by simpa [sum_range_succ] using even 13 5 (by decide)
theorem lower_14_10 : Cage.LowerBound 14 10 61882 := by simpa [sum_range_succ] using even 14 5 (by decide)
theorem lower_15_10 : Cage.LowerBound 15 10 82742 := by simpa [sum_range_succ] using even 15 5 (by decide)
theorem lower_16_10 : Cage.LowerBound 16 10 108482 := by simpa [sum_range_succ] using even 16 5 (by decide)
theorem lower_17_10 : Cage.LowerBound 17 10 139810 := by simpa [sum_range_succ] using even 17 5 (by decide)
theorem lower_18_10 : Cage.LowerBound 18 10 177482 := by simpa [sum_range_succ] using even 18 5 (by decide)
theorem lower_19_10 : Cage.LowerBound 19 10 222302 := by simpa [sum_range_succ] using even 19 5 (by decide)
theorem lower_20_10 : Cage.LowerBound 20 10 275122 := by simpa [sum_range_succ] using even 20 5 (by decide)
theorem lower_3_11 : Cage.LowerBound 3 11 94 := by simpa [sum_range_succ] using odd 3 5
theorem lower_4_11 : Cage.LowerBound 4 11 485 := by simpa [sum_range_succ] using odd 4 5
theorem lower_5_11 : Cage.LowerBound 5 11 1706 := by simpa [sum_range_succ] using odd 5 5
theorem lower_6_11 : Cage.LowerBound 6 11 4687 := by simpa [sum_range_succ] using odd 6 5
theorem lower_7_11 : Cage.LowerBound 7 11 10886 := by simpa [sum_range_succ] using odd 7 5
theorem lower_8_11 : Cage.LowerBound 8 11 22409 := by simpa [sum_range_succ] using odd 8 5
theorem lower_9_11 : Cage.LowerBound 9 11 42130 := by simpa [sum_range_succ] using odd 9 5
theorem lower_10_11 : Cage.LowerBound 10 11 73811 := by simpa [sum_range_succ] using odd 10 5
theorem lower_11_11 : Cage.LowerBound 11 11 122222 := by simpa [sum_range_succ] using odd 11 5
theorem lower_12_11 : Cage.LowerBound 12 11 193261 := by simpa [sum_range_succ] using odd 12 5
theorem lower_13_11 : Cage.LowerBound 13 11 294074 := by simpa [sum_range_succ] using odd 13 5
theorem lower_14_11 : Cage.LowerBound 14 11 433175 := by simpa [sum_range_succ] using odd 14 5
theorem lower_15_11 : Cage.LowerBound 15 11 620566 := by simpa [sum_range_succ] using odd 15 5
theorem lower_16_11 : Cage.LowerBound 16 11 867857 := by simpa [sum_range_succ] using odd 16 5
theorem lower_17_11 : Cage.LowerBound 17 11 1188386 := by simpa [sum_range_succ] using odd 17 5
theorem lower_18_11 : Cage.LowerBound 18 11 1597339 := by simpa [sum_range_succ] using odd 18 5
theorem lower_19_11 : Cage.LowerBound 19 11 2111870 := by simpa [sum_range_succ] using odd 19 5
theorem lower_20_11 : Cage.LowerBound 20 11 2751221 := by simpa [sum_range_succ] using odd 20 5
theorem lower_3_12 : Cage.LowerBound 3 12 126 := by simpa [sum_range_succ] using even 3 6 (by decide)
theorem lower_4_12 : Cage.LowerBound 4 12 728 := by simpa [sum_range_succ] using even 4 6 (by decide)
theorem lower_5_12 : Cage.LowerBound 5 12 2730 := by simpa [sum_range_succ] using even 5 6 (by decide)
theorem lower_6_12 : Cage.LowerBound 6 12 7812 := by simpa [sum_range_succ] using even 6 6 (by decide)
theorem lower_7_12 : Cage.LowerBound 7 12 18662 := by simpa [sum_range_succ] using even 7 6 (by decide)
theorem lower_8_12 : Cage.LowerBound 8 12 39216 := by simpa [sum_range_succ] using even 8 6 (by decide)
theorem lower_9_12 : Cage.LowerBound 9 12 74898 := by simpa [sum_range_succ] using even 9 6 (by decide)
theorem lower_10_12 : Cage.LowerBound 10 12 132860 := by simpa [sum_range_succ] using even 10 6 (by decide)
theorem lower_11_12 : Cage.LowerBound 11 12 222222 := by simpa [sum_range_succ] using even 11 6 (by decide)
theorem lower_12_12 : Cage.LowerBound 12 12 354312 := by simpa [sum_range_succ] using even 12 6 (by decide)
theorem lower_13_12 : Cage.LowerBound 13 12 542906 := by simpa [sum_range_succ] using even 13 6 (by decide)
theorem lower_14_12 : Cage.LowerBound 14 12 804468 := by simpa [sum_range_succ] using even 14 6 (by decide)
theorem lower_15_12 : Cage.LowerBound 15 12 1158390 := by simpa [sum_range_succ] using even 15 6 (by decide)
theorem lower_16_12 : Cage.LowerBound 16 12 1627232 := by simpa [sum_range_succ] using even 16 6 (by decide)
theorem lower_17_12 : Cage.LowerBound 17 12 2236962 := by simpa [sum_range_succ] using even 17 6 (by decide)
theorem lower_18_12 : Cage.LowerBound 18 12 3017196 := by simpa [sum_range_succ] using even 18 6 (by decide)
theorem lower_19_12 : Cage.LowerBound 19 12 4001438 := by simpa [sum_range_succ] using even 19 6 (by decide)
theorem lower_20_12 : Cage.LowerBound 20 12 5227320 := by simpa [sum_range_succ] using even 20 6 (by decide)
theorem lower_3_13 : Cage.LowerBound 3 13 190 := by simpa [sum_range_succ] using odd 3 6
theorem lower_4_13 : Cage.LowerBound 4 13 1457 := by simpa [sum_range_succ] using odd 4 6
theorem lower_5_13 : Cage.LowerBound 5 13 6826 := by simpa [sum_range_succ] using odd 5 6
theorem lower_6_13 : Cage.LowerBound 6 13 23437 := by simpa [sum_range_succ] using odd 6 6
theorem lower_7_13 : Cage.LowerBound 7 13 65318 := by simpa [sum_range_succ] using odd 7 6
theorem lower_8_13 : Cage.LowerBound 8 13 156865 := by simpa [sum_range_succ] using odd 8 6
theorem lower_9_13 : Cage.LowerBound 9 13 337042 := by simpa [sum_range_succ] using odd 9 6
theorem lower_10_13 : Cage.LowerBound 10 13 664301 := by simpa [sum_range_succ] using odd 10 6
theorem lower_11_13 : Cage.LowerBound 11 13 1222222 := by simpa [sum_range_succ] using odd 11 6
theorem lower_12_13 : Cage.LowerBound 12 13 2125873 := by simpa [sum_range_succ] using odd 12 6
theorem lower_13_13 : Cage.LowerBound 13 13 3528890 := by simpa [sum_range_succ] using odd 13 6
theorem lower_14_13 : Cage.LowerBound 14 13 5631277 := by simpa [sum_range_succ] using odd 14 6
theorem lower_15_13 : Cage.LowerBound 15 13 8687926 := by simpa [sum_range_succ] using odd 15 6
theorem lower_16_13 : Cage.LowerBound 16 13 13017857 := by simpa [sum_range_succ] using odd 16 6
theorem lower_17_13 : Cage.LowerBound 17 13 19014178 := by simpa [sum_range_succ] using odd 17 6
theorem lower_18_13 : Cage.LowerBound 18 13 27154765 := by simpa [sum_range_succ] using odd 18 6
theorem lower_19_13 : Cage.LowerBound 19 13 38013662 := by simpa [sum_range_succ] using odd 19 6
theorem lower_20_13 : Cage.LowerBound 20 13 52273201 := by simpa [sum_range_succ] using odd 20 6
theorem lower_3_14 : Cage.LowerBound 3 14 254 := by simpa [sum_range_succ] using even 3 7 (by decide)
theorem lower_4_14 : Cage.LowerBound 4 14 2186 := by simpa [sum_range_succ] using even 4 7 (by decide)
theorem lower_5_14 : Cage.LowerBound 5 14 10922 := by simpa [sum_range_succ] using even 5 7 (by decide)
theorem lower_6_14 : Cage.LowerBound 6 14 39062 := by simpa [sum_range_succ] using even 6 7 (by decide)
theorem lower_7_14 : Cage.LowerBound 7 14 111974 := by simpa [sum_range_succ] using even 7 7 (by decide)
theorem lower_8_14 : Cage.LowerBound 8 14 274514 := by simpa [sum_range_succ] using even 8 7 (by decide)
theorem lower_9_14 : Cage.LowerBound 9 14 599186 := by simpa [sum_range_succ] using even 9 7 (by decide)
theorem lower_10_14 : Cage.LowerBound 10 14 1195742 := by simpa [sum_range_succ] using even 10 7 (by decide)
theorem lower_11_14 : Cage.LowerBound 11 14 2222222 := by simpa [sum_range_succ] using even 11 7 (by decide)
theorem lower_12_14 : Cage.LowerBound 12 14 3897434 := by simpa [sum_range_succ] using even 12 7 (by decide)
theorem lower_13_14 : Cage.LowerBound 13 14 6514874 := by simpa [sum_range_succ] using even 13 7 (by decide)
theorem lower_14_14 : Cage.LowerBound 14 14 10458086 := by simpa [sum_range_succ] using even 14 7 (by decide)
theorem lower_15_14 : Cage.LowerBound 15 14 16217462 := by simpa [sum_range_succ] using even 15 7 (by decide)
theorem lower_16_14 : Cage.LowerBound 16 14 24408482 := by simpa [sum_range_succ] using even 16 7 (by decide)
theorem lower_17_14 : Cage.LowerBound 17 14 35791394 := by simpa [sum_range_succ] using even 17 7 (by decide)
theorem lower_18_14 : Cage.LowerBound 18 14 51292334 := by simpa [sum_range_succ] using even 18 7 (by decide)
theorem lower_19_14 : Cage.LowerBound 19 14 72025886 := by simpa [sum_range_succ] using even 19 7 (by decide)
theorem lower_20_14 : Cage.LowerBound 20 14 99319082 := by simpa [sum_range_succ] using even 20 7 (by decide)
theorem lower_3_15 : Cage.LowerBound 3 15 382 := by simpa [sum_range_succ] using odd 3 7
theorem lower_4_15 : Cage.LowerBound 4 15 4373 := by simpa [sum_range_succ] using odd 4 7
theorem lower_5_15 : Cage.LowerBound 5 15 27306 := by simpa [sum_range_succ] using odd 5 7
theorem lower_6_15 : Cage.LowerBound 6 15 117187 := by simpa [sum_range_succ] using odd 6 7
theorem lower_7_15 : Cage.LowerBound 7 15 391910 := by simpa [sum_range_succ] using odd 7 7
theorem lower_8_15 : Cage.LowerBound 8 15 1098057 := by simpa [sum_range_succ] using odd 8 7
theorem lower_9_15 : Cage.LowerBound 9 15 2696338 := by simpa [sum_range_succ] using odd 9 7
theorem lower_10_15 : Cage.LowerBound 10 15 5978711 := by simpa [sum_range_succ] using odd 10 7
theorem lower_11_15 : Cage.LowerBound 11 15 12222222 := by simpa [sum_range_succ] using odd 11 7
theorem lower_12_15 : Cage.LowerBound 12 15 23384605 := by simpa [sum_range_succ] using odd 12 7
theorem lower_13_15 : Cage.LowerBound 13 15 42346682 := by simpa [sum_range_succ] using odd 13 7
theorem lower_14_15 : Cage.LowerBound 14 15 73206603 := by simpa [sum_range_succ] using odd 14 7
theorem lower_15_15 : Cage.LowerBound 15 15 121630966 := by simpa [sum_range_succ] using odd 15 7
theorem lower_16_15 : Cage.LowerBound 16 15 195267857 := by simpa [sum_range_succ] using odd 16 7
theorem lower_17_15 : Cage.LowerBound 17 15 304226850 := by simpa [sum_range_succ] using odd 17 7
theorem lower_18_15 : Cage.LowerBound 18 15 461631007 := by simpa [sum_range_succ] using odd 18 7
theorem lower_19_15 : Cage.LowerBound 19 15 684245918 := by simpa [sum_range_succ] using odd 19 7
theorem lower_20_15 : Cage.LowerBound 20 15 993190821 := by simpa [sum_range_succ] using odd 20 7
theorem lower_3_16 : Cage.LowerBound 3 16 510 := by simpa [sum_range_succ] using even 3 8 (by decide)
theorem lower_4_16 : Cage.LowerBound 4 16 6560 := by simpa [sum_range_succ] using even 4 8 (by decide)
theorem lower_5_16 : Cage.LowerBound 5 16 43690 := by simpa [sum_range_succ] using even 5 8 (by decide)
theorem lower_6_16 : Cage.LowerBound 6 16 195312 := by simpa [sum_range_succ] using even 6 8 (by decide)
theorem lower_7_16 : Cage.LowerBound 7 16 671846 := by simpa [sum_range_succ] using even 7 8 (by decide)
theorem lower_8_16 : Cage.LowerBound 8 16 1921600 := by simpa [sum_range_succ] using even 8 8 (by decide)
theorem lower_9_16 : Cage.LowerBound 9 16 4793490 := by simpa [sum_range_succ] using even 9 8 (by decide)
theorem lower_10_16 : Cage.LowerBound 10 16 10761680 := by simpa [sum_range_succ] using even 10 8 (by decide)
theorem lower_11_16 : Cage.LowerBound 11 16 22222222 := by simpa [sum_range_succ] using even 11 8 (by decide)
theorem lower_12_16 : Cage.LowerBound 12 16 42871776 := by simpa [sum_range_succ] using even 12 8 (by decide)
theorem lower_13_16 : Cage.LowerBound 13 16 78178490 := by simpa [sum_range_succ] using even 13 8 (by decide)
theorem lower_14_16 : Cage.LowerBound 14 16 135955120 := by simpa [sum_range_succ] using even 14 8 (by decide)
theorem lower_15_16 : Cage.LowerBound 15 16 227044470 := by simpa [sum_range_succ] using even 15 8 (by decide)
theorem lower_16_16 : Cage.LowerBound 16 16 366127232 := by simpa [sum_range_succ] using even 16 8 (by decide)
theorem lower_17_16 : Cage.LowerBound 17 16 572662306 := by simpa [sum_range_succ] using even 17 8 (by decide)
theorem lower_18_16 : Cage.LowerBound 18 16 871969680 := by simpa [sum_range_succ] using even 18 8 (by decide)
theorem lower_19_16 : Cage.LowerBound 19 16 1296465950 := by simpa [sum_range_succ] using even 19 8 (by decide)
theorem lower_20_16 : Cage.LowerBound 20 16 1887062560 := by simpa [sum_range_succ] using even 20 8 (by decide)

end LeapsInBounds.Proofs.MooreBound
