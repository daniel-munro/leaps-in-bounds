module

public import LeapsInBounds.Statements.MulticolorRamsey
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort

/-!
# Upper bounds on multicolor Ramsey numbers from the Greenwood–Gleason recurrence

`R_{r+1}(3) ≤ (r + 1) * (R_r(3) - 1) + 2` for `r ≥ 1` (Greenwood and Gleason,
1955): color the edges of the complete graph on that many vertices with `r + 1`
colors, and pick a vertex `v`. It has `(r + 1) * (R_r(3) - 1) + 1` neighbors, so
some color `d` joins it to at least `R_r(3)` of them. If two of these are joined
by an edge of color `d`, they form a monochromatic triangle with `v`. Otherwise
the edges between them use only the `r` other colors, so they contain a
monochromatic triangle.

Starting from `R_1(3) ≤ 3`, this gives `R_2(3) ≤ 6`, `R_3(3) ≤ 17`,
`R_4(3) ≤ 66`, `R_5(3) ≤ 327`, `R_6(3) ≤ 1958`, `R_7(3) ≤ 13701`,
`R_8(3) ≤ 109602` and `R_9(3) ≤ 986411`.

`MulticolorRamsey.UpperBound` only looks at the colors `c a b` with `a < b`. So
`v` is the first vertex, and the points of a subset are taken in increasing
order (`exists_triangle_of_avoid`, which `SchurFromRamsey` uses too).
-/

@[expose] public section

namespace LeapsInBounds.Proofs.MulticolorRamseyRecurrence

/-- Renumber the colors other than `c`: `d ↦ d` if `d < c`, and `d ↦ d - 1`
otherwise. This is injective on the colors other than `c` (`dropColor_inj`). -/
def dropColor {k : ℕ} (hk : 1 ≤ k) (c d : Fin (k + 1)) : Fin k :=
  ⟨if d.val < c.val then d.val else d.val - 1, by
    have := d.isLt
    have := c.isLt
    split <;> omega⟩

theorem dropColor_inj {k : ℕ} (hk : 1 ≤ k) (c : Fin (k + 1)) {d e : Fin (k + 1)} (hd : d ≠ c)
    (he : e ≠ c) (h : dropColor hk c d = dropColor hk c e) : d = e := by
  have hd' : d.val ≠ c.val := fun h => hd (Fin.ext h)
  have he' : e.val ≠ c.val := fun h => he (Fin.ext h)
  have h' := congrArg Fin.val h
  simp only [dropColor] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- If `R_k(3) ≤ n` with `k ≥ 1`, and the coloring `col` with `k + 1` colors never
gives the color `c` to a pair `a < b` of points of `s`, where `s` has at least
`n` points, then `s` contains a monochromatic triangle `a < b < d`. -/
theorem exists_triangle_of_avoid {k n : ℕ} (hk : 1 ≤ k) (h : MulticolorRamsey.UpperBound k n)
    {α : Type*} [LinearOrder α] (s : Finset α) (hs : n ≤ s.card) (col : α → α → Fin (k + 1))
    (c : Fin (k + 1)) (hc : ∀ a ∈ s, ∀ b ∈ s, a < b → col a b ≠ c) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ d ∈ s, a < b ∧ b < d ∧ col a b = col a d ∧ col a b = col b d := by
  -- `n` points of `s`, in increasing order
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  obtain ⟨a, b, d, hab, hbd, h1, h2⟩ :=
    h fun i j => dropColor hk c (col (t.orderEmbOfFin ht i) (t.orderEmbOfFin ht j))
  have ha := hts (t.orderEmbOfFin_mem ht a)
  have hb := hts (t.orderEmbOfFin_mem ht b)
  have hd := hts (t.orderEmbOfFin_mem ht d)
  have hab' := (t.orderEmbOfFin ht).lt_iff_lt.2 hab
  have hbd' := (t.orderEmbOfFin ht).lt_iff_lt.2 hbd
  have nab := hc _ ha _ hb hab'
  have nad := hc _ ha _ hd (hab'.trans hbd')
  have nbd := hc _ hb _ hd hbd'
  exact ⟨_, ha, _, hb, _, hd, hab', hbd', dropColor_inj hk c nab nad h1,
    dropColor_inj hk c nab nbd h2⟩

/-- The Greenwood–Gleason recurrence, with room to spare: if `R_r(3) ≤ n` with
`r ≥ 1`, and `(r + 1) * (n - 1) + 2 ≤ m`, then `R_{r+1}(3) ≤ m`.

It needs a color: with `r = 0` and `n = 1` the hypothesis holds, for want of a
coloring of the complete graph on one vertex with no colors, and the
conclusion would be `R_1(3) ≤ 2`. -/
theorem step {r n m : ℕ} (hr : 1 ≤ r) (h : MulticolorRamsey.UpperBound r n)
    (hm : (r + 1) * (n - 1) + 2 ≤ m) : MulticolorRamsey.UpperBound (r + 1) m := by
  intro c
  -- the first vertex
  obtain ⟨v, hv⟩ : ∃ v : Fin m, ∀ u, u ≠ v → v < u :=
    ⟨⟨0, by omega⟩, fun u hu => Fin.lt_def.2 (Nat.pos_of_ne_zero fun h0 => hu (Fin.ext h0))⟩
  -- pigeonhole on its `m - 1` neighbors: some color `d` joins it to at least `n` of them
  have hcard : (Finset.univ : Finset (Fin (r + 1))).card * (n - 1) <
      ((Finset.univ : Finset (Fin m)).erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun u => c v u) (fun _ _ => Finset.mem_univ _) hcard
  -- `S`: the neighbors of `v` in the color `d`
  set S : Finset (Fin m) := ((Finset.univ : Finset (Fin m)).erase v).filter (fun u => c v u = d)
    with hS
  have hmem : ∀ u ∈ S, v < u ∧ c v u = d := by
    intro u hu
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hu
    exact ⟨hv u hu.1.1, hu.2⟩
  by_cases hcase : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ c a b = d
  · -- two of them joined by the color `d`: a triangle with `v`
    obtain ⟨a, ha, b, hb, hab, habd⟩ := hcase
    obtain ⟨hva, hca⟩ := hmem a ha
    obtain ⟨-, hcb⟩ := hmem b hb
    exact ⟨v, a, b, hva, hab, hca.trans hcb.symm, hca.trans habd.symm⟩
  · -- otherwise `S` only uses the `r` other colors
    obtain ⟨a, -, b, -, e, -, hab, hbe, h1, h2⟩ :=
      exists_triangle_of_avoid hr h S (by omega) c d
        fun a ha b hb hab habd => hcase ⟨a, ha, b, hb, hab, habd⟩
    exact ⟨a, b, e, hab, hbe, h1, h2⟩

/-- **The Greenwood–Gleason recurrence.** If `R_r(3) ≤ n` with `r ≥ 1`, then
`R_{r+1}(3) ≤ (r + 1) * (n - 1) + 2`. -/
theorem greenwood_gleason {r n : ℕ} (hr : 1 ≤ r) (h : MulticolorRamsey.UpperBound r n) :
    MulticolorRamsey.UpperBound (r + 1) ((r + 1) * (n - 1) + 2) :=
  step hr h (Nat.le_refl _)

/-- `R_1(3) ≤ 3`: with one color, three vertices form a monochromatic triangle. -/
theorem upper_1_3 : MulticolorRamsey.UpperBound 1 3 := fun _ =>
  ⟨0, 1, 2, by decide, by decide, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- `R_2(3) ≤ 6`. -/
theorem upper_2_6 : MulticolorRamsey.UpperBound 2 6 :=
  step (r := 1) (by decide) upper_1_3 (by decide)

/-- `R_3(3) ≤ 17`. -/
theorem upper_3_17 : MulticolorRamsey.UpperBound 3 17 :=
  step (r := 2) (by decide) upper_2_6 (by decide)

/-- `R_4(3) ≤ 66`. -/
theorem upper_4_66 : MulticolorRamsey.UpperBound 4 66 :=
  step (r := 3) (by decide) upper_3_17 (by decide)

/-- `R_5(3) ≤ 327`. -/
theorem upper_5_327 : MulticolorRamsey.UpperBound 5 327 :=
  step (r := 4) (by decide) upper_4_66 (by decide)

/-- `R_6(3) ≤ 1958`. -/
theorem upper_6_1958 : MulticolorRamsey.UpperBound 6 1958 :=
  step (r := 5) (by decide) upper_5_327 (by decide)

/-- `R_7(3) ≤ 13701`. -/
theorem upper_7_13701 : MulticolorRamsey.UpperBound 7 13701 :=
  step (r := 6) (by decide) upper_6_1958 (by decide)

/-- `R_8(3) ≤ 109602`. -/
theorem upper_8_109602 : MulticolorRamsey.UpperBound 8 109602 :=
  step (r := 7) (by decide) upper_7_13701 (by decide)

/-- `R_9(3) ≤ 986411`. -/
theorem upper_9_986411 : MulticolorRamsey.UpperBound 9 986411 :=
  step (r := 8) (by decide) upper_8_109602 (by decide)

end LeapsInBounds.Proofs.MulticolorRamseyRecurrence
