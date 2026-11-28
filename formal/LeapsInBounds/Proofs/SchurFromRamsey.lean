module

public import LeapsInBounds.Statements.Schur
public import LeapsInBounds.Proofs.MulticolorRamseyRecurrence
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Upper bounds on Schur numbers from multicolor Ramsey numbers

**The last section of this file is conditional.** Its theorems, named
`…_of_ramsey_4_62`, take `R_4(3) ≤ 62` as an explicit hypothesis
`h : MulticolorRamsey.UpperBound 4 62`. That bound is a published result which
is not formalized here:

> S. Fettes, R. L. Kramer and S. P. Radziszowski, An Upper Bound of 62 on the
> Classical Ramsey Number R(3,3,3,3), Ars Combinatoria 72 (2004) 41–63,
> <https://www.cs.rit.edu/~spr/PUBL/paper43.pdf>
> (the source `fettes-kramer-radziszowski-2004` of this site).

Lean checks that the bounds follow from `R_4(3) ≤ 62`, not that `R_4(3) ≤ 62`
holds. So these theorems are not certificates in the sense of this site: their
types are implications, not `Schur.UpperBound k n`. The bounds before the last
section, `upper_2_4`, …, `upper_9_986401`, have no hypothesis.

## The argument

Let `χ` be a coloring of `1, …, N` with `k + 1` colors and no monochromatic
solution to `x + y = z`. Give the edge between two vertices `a < b` of the
complete graph on `0, …, N` the color of `b - a`. A monochromatic triangle
`a < b < d` would be a monochromatic solution `(b - a) + (d - b) = d - a`, so
there is none (`no_triangle`). As in the Greenwood–Gleason recurrence, the
neighbors of a vertex `v` along the edges of one color `c` then use only the
`k` other colors among themselves, so there are at most `R_k(3) - 1` of them
(`card_lt_of_neighbors`).

* **First vertex** (`upperBound_of_ramsey`). The neighbors of `0` in the color
  `c` are the numbers of color `c`, and summing over the colors gives
  `S(k + 1) ≤ (k + 1) * (R_k(3) - 1)`. This is the classical bound: it is what
  `S(k + 1) ≤ R_{k+1}(3) - 2` gives with the Greenwood–Gleason recurrence.
* **Central vertex** (`upperBound_of_ramsey_even`). Let `m = ⌊N / 2⌋`. For each
  `x ≤ m` of color `c`, both `m - x` and `m + x` are neighbors of `m` in the
  color `c`. Their number is even: twice the number of `x ≤ m` of color `c`. If
  `R_k(3) ≤ n` with `n` even, an even number below `n` is at most `n - 2`.
  Summing over the colors gives `m ≤ (k + 1) * (n - 2) / 2`, and `N ≤ 2 * m + 1`,
  so `S(k + 1) ≤ (k + 1) * (n - 2) + 1`: this is `k` less than the classical
  bound.

Both need `k ≥ 1`, as `MulticolorRamseyRecurrence.step` does.

The parity argument is close to the one that refines the Greenwood–Gleason
recurrence for the Ramsey numbers `R_k(3)`. Compare H. Wan, Upper bounds for
Ramsey numbers R(3,3,…,3) and Schur numbers, Journal of Graph Theory 26 (1997)
119–122: its abstract also gives a bound on Schur numbers for an even number of
colors. We have read only the abstract of that paper, not its proofs.

## The values

Without hypothesis, from the bounds of `MulticolorRamseyRecurrence`: `S(2) ≤ 4`
and `S(3) ≤ 13` (the exact values), `S(4) ≤ 64`, `S(5) ≤ 321`, `S(6) ≤ 1956`,
`S(7) ≤ 13693`, `S(8) ≤ 109600` and `S(9) ≤ 986401`.

Under the hypothesis `R_4(3) ≤ 62`: `R_5(3) ≤ 307`, `R_6(3) ≤ 1838`,
`R_7(3) ≤ 12861`, `R_8(3) ≤ 102882` and `R_9(3) ≤ 925931` by the
Greenwood–Gleason recurrence, then `S(5) ≤ 301`, `S(6) ≤ 1836`, `S(7) ≤ 12853`,
`S(8) ≤ 102880` and `S(9) ≤ 925921`. The bounds on `R_4(3)`, `R_6(3)` and
`R_8(3)` are even, so the central vertex gives the bounds for 5, 7 and 9 colors;
the classical bound gives `12859` and `925929` for 7 and 9 colors.
-/

@[expose] public section

namespace LeapsInBounds.Proofs.SchurFromRamsey

/-! ### No monochromatic triangle -/

/-- With no monochromatic solution in `1, …, N`, the three differences of
`a < b < d ≤ N` don't all have the same color, since
`(b - a) + (d - b) = d - a`. -/
theorem no_triangle {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ Schur.HasMonoSum k N χ) {a b d : ℕ}
    (hab : a < b) (hbd : b < d) (hd : d ≤ N) {c : Fin k} (h1 : χ (b - a) = c)
    (h2 : χ (d - b) = c) (h3 : χ (d - a) = c) : False := by
  refine H ⟨b - a, d - b, by omega, by omega, by omega, h1.trans h2.symm, ?_⟩
  rw [show b - a + (d - b) = d - a by omega]
  exact h3.trans h1.symm

/-- **The degree bound.** Suppose that `R_k(3) ≤ n` with `k ≥ 1`, and that the
coloring `χ` with `k + 1` colors has no monochromatic solution in `1, …, N`. Let
`v ≤ N`, and let `s` be a set of numbers `u ≤ N` other than `v` such that
`|u - v|` has the color `c`. Then `s` has fewer than `n` elements. -/
theorem card_lt_of_neighbors {k n N : ℕ} (hk : 1 ≤ k) (h : MulticolorRamsey.UpperBound k n)
    {χ : ℕ → Fin (k + 1)} (H : ¬ Schur.HasMonoSum (k + 1) N χ) {v : ℕ} (hv : v ≤ N)
    {c : Fin (k + 1)} (s : Finset ℕ)
    (hs : ∀ u ∈ s, u ≤ N ∧ (u < v ∧ χ (v - u) = c ∨ v < u ∧ χ (u - v) = c)) : s.card < n := by
  by_contra hcon
  -- two neighbors `p < q` of `v` are not joined by the color `c`: a triangle with `v`
  have key : ∀ p ∈ s, ∀ q ∈ s, p < q → χ (q - p) ≠ c := by
    intro p hp q hq hpq hc
    obtain ⟨-, hp' | hp'⟩ := hs p hp <;> obtain ⟨hqN, hq' | hq'⟩ := hs q hq
    · exact no_triangle H hpq hq'.1 hv hc hq'.2 hp'.2
    · exact no_triangle H hp'.1 hq'.1 hqN hp'.2 hq'.2 hc
    · omega
    · exact no_triangle H hp'.1 hpq hqN hp'.2 hc hq'.2
  -- so `s` only uses the `k` other colors, and contains a monochromatic triangle
  obtain ⟨a, -, b, -, d, hd, hab, hbd, h1, h2⟩ :=
    MulticolorRamseyRecurrence.exists_triangle_of_avoid hk h s (by omega)
      (fun a b => χ (b - a)) c key
  exact no_triangle H hab hbd (hs d hd).1 (c := χ (b - a)) rfl h2.symm h1.symm

/-! ### Counting the numbers of each color -/

/-- The numbers of `1, …, t` with the color `c`. -/
def colorClass {k : ℕ} (χ : ℕ → Fin k) (c : Fin k) (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter fun x => χ x = c

theorem mem_colorClass {k : ℕ} {χ : ℕ → Fin k} {c : Fin k} {t x : ℕ} :
    x ∈ colorClass χ c t ↔ (1 ≤ x ∧ x ≤ t) ∧ χ x = c := by
  rw [colorClass, Finset.mem_filter, Finset.mem_Icc]

/-- Each number of `1, …, t` has exactly one color. -/
theorem sum_card_colorClass {k : ℕ} (χ : ℕ → Fin k) (t : ℕ) :
    ∑ c : Fin k, (colorClass χ c t).card = t := by
  unfold colorClass
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _)),
    Nat.card_Icc, Nat.add_sub_cancel]

/-- If each color has at most `B` numbers in `1, …, t`, then `t ≤ k * B`. -/
theorem le_mul_of_card_colorClass_le {k : ℕ} (χ : ℕ → Fin k) {t B : ℕ}
    (h : ∀ c, (colorClass χ c t).card ≤ B) : t ≤ k * B :=
  calc t = ∑ c : Fin k, (colorClass χ c t).card := (sum_card_colorClass χ t).symm
    _ ≤ ∑ _c : Fin k, B := Finset.sum_le_sum fun c _ => h c
    _ = k * B := by
      rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-! ### The first vertex -/

/-- If `R_k(3) ≤ n` with `k ≥ 1`, and the coloring `χ` with `k + 1` colors has no
monochromatic solution in `1, …, N`, then `N ≤ (k + 1) * (n - 1)`: the
neighbors of `0` in the color `c` are the numbers of color `c`. -/
theorem le_of_not_hasMonoSum {k n N : ℕ} (hk : 1 ≤ k) (h : MulticolorRamsey.UpperBound k n)
    {χ : ℕ → Fin (k + 1)} (H : ¬ Schur.HasMonoSum (k + 1) N χ) : N ≤ (k + 1) * (n - 1) := by
  refine le_mul_of_card_colorClass_le χ fun c => ?_
  have hlt : (colorClass χ c N).card < n :=
    card_lt_of_neighbors hk h H (Nat.zero_le N) (c := c) (colorClass χ c N) fun u hu => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := mem_colorClass.1 hu
      exact ⟨h2, Or.inr ⟨h1, by rwa [Nat.sub_zero]⟩⟩
  omega

/-- If `R_k(3) ≤ n` with `k ≥ 1` and `(k + 1) * (n - 1) ≤ m`, then
`S(k + 1) ≤ m`. -/
theorem upperBound_of_ramsey {k n m : ℕ} (hk : 1 ≤ k) (h : MulticolorRamsey.UpperBound k n)
    (hm : (k + 1) * (n - 1) ≤ m) : Schur.UpperBound (k + 1) m := by
  intro χ
  by_contra H
  have := le_of_not_hasMonoSum hk h H
  omega

/-! ### The central vertex -/

/-- If `R_k(3) ≤ n` with `k ≥ 1` and `n` even, and the coloring `χ` with `k + 1`
colors has no monochromatic solution in `1, …, N`, then
`N ≤ (k + 1) * (n - 2) + 1`: the vertex `m = ⌊N / 2⌋` has an even number of
neighbors `m - x` and `m + x` in each color. -/
theorem le_of_not_hasMonoSum_of_even {k n N : ℕ} (hk : 1 ≤ k)
    (h : MulticolorRamsey.UpperBound k n) (hn : n % 2 = 0) {χ : ℕ → Fin (k + 1)}
    (H : ¬ Schur.HasMonoSum (k + 1) N χ) : N ≤ (k + 1) * (n - 2) + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, m = N / 2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, n - 2 = 2 * t := ⟨(n - 2) / 2, by omega⟩
  -- each color has at most `t` numbers in `1, …, m`
  have hclass : ∀ c, (colorClass χ c m).card ≤ t := by
    intro c
    have hinj1 : Set.InjOn (fun x => m - x) (colorClass χ c m : Set ℕ) := by
      intro x hx y hy hxy
      have hx' := (mem_colorClass.1 (Finset.mem_coe.1 hx)).1
      have hy' := (mem_colorClass.1 (Finset.mem_coe.1 hy)).1
      have hxy' : m - x = m - y := hxy
      omega
    have hinj2 : Set.InjOn (fun x => m + x) (colorClass χ c m : Set ℕ) := by
      intro x _ y _ hxy
      have hxy' : m + x = m + y := hxy
      omega
    have hdisj : Disjoint ((colorClass χ c m).image fun x => m - x)
        ((colorClass χ c m).image fun x => m + x) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hu'
      have hx' := (mem_colorClass.1 hx).1
      have hy' := (mem_colorClass.1 hy).1
      have hxy' : m + y = m - x := hxy
      omega
    -- the neighbors `m - x` and `m + x` of `m`, for the `x ≤ m` of color `c`
    have hcard : (((colorClass χ c m).image fun x => m - x) ∪
        ((colorClass χ c m).image fun x => m + x)).card = 2 * (colorClass χ c m).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
        Finset.card_image_of_injOn hinj2]
      omega
    have hlt := card_lt_of_neighbors hk h H (v := m) (by omega) (c := c)
      (((colorClass χ c m).image fun x => m - x) ∪ ((colorClass χ c m).image fun x => m + x))
      (by
        intro u hu
        rcases Finset.mem_union.1 hu with hu | hu
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨⟨h1, h2⟩, h3⟩ := mem_colorClass.1 hx
          exact ⟨by omega, Or.inl ⟨by omega, by rwa [show m - (m - x) = x by omega]⟩⟩
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨⟨h1, h2⟩, h3⟩ := mem_colorClass.1 hx
          exact ⟨by omega, Or.inr ⟨by omega, by rwa [show m + x - m = x by omega]⟩⟩)
    omega
  have hm' := le_mul_of_card_colorClass_le χ hclass
  rw [ht, Nat.mul_left_comm]
  omega

/-- **The central vertex theorem.** If `R_k(3) ≤ n` with `k ≥ 1` and `n` even,
and `(k + 1) * (n - 2) + 1 ≤ m`, then `S(k + 1) ≤ m`. -/
theorem upperBound_of_ramsey_even {k n m : ℕ} (hk : 1 ≤ k)
    (h : MulticolorRamsey.UpperBound k n) (hn : n % 2 = 0) (hm : (k + 1) * (n - 2) + 1 ≤ m) :
    Schur.UpperBound (k + 1) m := by
  intro χ
  by_contra H
  have := le_of_not_hasMonoSum_of_even hk h hn H
  omega

/-! ### Without hypothesis: from the Greenwood–Gleason bounds

`R_1(3) ≤ 3`, `R_2(3) ≤ 6`, `R_3(3) ≤ 17`, `R_4(3) ≤ 66`, `R_5(3) ≤ 327`,
`R_6(3) ≤ 1958`, `R_7(3) ≤ 13701` and `R_8(3) ≤ 109602`. For 2 and 3 colors the
bounds are the exact values `S(2) = 4` and `S(3) = 13`. -/

/-- `S(2) ≤ 4`, from `R_1(3) ≤ 3`: `2 * 2`. -/
theorem upper_2_4 : Schur.UpperBound 2 4 :=
  upperBound_of_ramsey (k := 1) (by decide) MulticolorRamseyRecurrence.upper_1_3 (by decide)

/-- `S(3) ≤ 13`, from `R_2(3) ≤ 6`, which is even: `3 * 4 + 1`. -/
theorem upper_3_13 : Schur.UpperBound 3 13 :=
  upperBound_of_ramsey_even (k := 2) (by decide) MulticolorRamseyRecurrence.upper_2_6
    (by decide) (by decide)

/-- `S(4) ≤ 64`, from `R_3(3) ≤ 17`: `4 * 16`. -/
theorem upper_4_64 : Schur.UpperBound 4 64 :=
  upperBound_of_ramsey (k := 3) (by decide) MulticolorRamseyRecurrence.upper_3_17 (by decide)

/-- `S(5) ≤ 321`, from `R_4(3) ≤ 66`, which is even: `5 * 64 + 1`. -/
theorem upper_5_321 : Schur.UpperBound 5 321 :=
  upperBound_of_ramsey_even (k := 4) (by decide) MulticolorRamseyRecurrence.upper_4_66
    (by decide) (by decide)

/-- `S(6) ≤ 1956`, from `R_5(3) ≤ 327`: `6 * 326`. -/
theorem upper_6_1956 : Schur.UpperBound 6 1956 :=
  upperBound_of_ramsey (k := 5) (by decide) MulticolorRamseyRecurrence.upper_5_327 (by decide)

/-- `S(7) ≤ 13693`, from `R_6(3) ≤ 1958`, which is even: `7 * 1956 + 1`. -/
theorem upper_7_13693 : Schur.UpperBound 7 13693 :=
  upperBound_of_ramsey_even (k := 6) (by decide) MulticolorRamseyRecurrence.upper_6_1958
    (by decide) (by decide)

/-- `S(8) ≤ 109600`, from `R_7(3) ≤ 13701`: `8 * 13700`. -/
theorem upper_8_109600 : Schur.UpperBound 8 109600 :=
  upperBound_of_ramsey (k := 7) (by decide) MulticolorRamseyRecurrence.upper_7_13701 (by decide)

/-- `S(9) ≤ 986401`, from `R_8(3) ≤ 109602`, which is even: `9 * 109600 + 1`. -/
theorem upper_9_986401 : Schur.UpperBound 9 986401 :=
  upperBound_of_ramsey_even (k := 8) (by decide) MulticolorRamseyRecurrence.upper_8_109602
    (by decide) (by decide)

/-! ## Conditional on `R_4(3) ≤ 62`

Every theorem of this section takes `R_4(3) ≤ 62` as the hypothesis `h`. That
bound is due to Fettes, Kramer and Radziszowski (Ars Combinatoria 72 (2004)
41–63, <https://www.cs.rit.edu/~spr/PUBL/paper43.pdf>) and is not formalized
here. These theorems are implications, not certificates. -/

/-- If `R_4(3) ≤ 62`, then `R_5(3) ≤ 307`: `5 * 61 + 2`. -/
theorem ramsey_5_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    MulticolorRamsey.UpperBound 5 307 :=
  MulticolorRamseyRecurrence.step (r := 4) (by decide) h (by decide)

/-- If `R_4(3) ≤ 62`, then `R_6(3) ≤ 1838`: `6 * 306 + 2`. -/
theorem ramsey_6_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    MulticolorRamsey.UpperBound 6 1838 :=
  MulticolorRamseyRecurrence.step (r := 5) (by decide) (ramsey_5_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `R_7(3) ≤ 12861`: `7 * 1837 + 2`. -/
theorem ramsey_7_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    MulticolorRamsey.UpperBound 7 12861 :=
  MulticolorRamseyRecurrence.step (r := 6) (by decide) (ramsey_6_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `R_8(3) ≤ 102882`: `8 * 12860 + 2`. -/
theorem ramsey_8_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    MulticolorRamsey.UpperBound 8 102882 :=
  MulticolorRamseyRecurrence.step (r := 7) (by decide) (ramsey_7_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `R_9(3) ≤ 925931`: `9 * 102881 + 2`. -/
theorem ramsey_9_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    MulticolorRamsey.UpperBound 9 925931 :=
  MulticolorRamseyRecurrence.step (r := 8) (by decide) (ramsey_8_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `S(5) ≤ 301`: `62` is even, `5 * 60 + 1`. -/
theorem schur_5_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    Schur.UpperBound 5 301 :=
  upperBound_of_ramsey_even (k := 4) (by decide) h (by decide) (by decide)

/-- If `R_4(3) ≤ 62`, then `S(6) ≤ 1836`: `6 * 306`. -/
theorem schur_6_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    Schur.UpperBound 6 1836 :=
  upperBound_of_ramsey (k := 5) (by decide) (ramsey_5_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `S(7) ≤ 12853`: `1838` is even, `7 * 1836 + 1`. -/
theorem schur_7_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    Schur.UpperBound 7 12853 :=
  upperBound_of_ramsey_even (k := 6) (by decide) (ramsey_6_of_ramsey_4_62 h) (by decide)
    (by decide)

/-- If `R_4(3) ≤ 62`, then `S(8) ≤ 102880`: `8 * 12860`. -/
theorem schur_8_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    Schur.UpperBound 8 102880 :=
  upperBound_of_ramsey (k := 7) (by decide) (ramsey_7_of_ramsey_4_62 h) (by decide)

/-- If `R_4(3) ≤ 62`, then `S(9) ≤ 925921`: `102882` is even, `9 * 102880 + 1`. -/
theorem schur_9_of_ramsey_4_62 (h : MulticolorRamsey.UpperBound 4 62) :
    Schur.UpperBound 9 925921 :=
  upperBound_of_ramsey_even (k := 8) (by decide) (ramsey_8_of_ramsey_4_62 h) (by decide)
    (by decide)

end LeapsInBounds.Proofs.SchurFromRamsey
