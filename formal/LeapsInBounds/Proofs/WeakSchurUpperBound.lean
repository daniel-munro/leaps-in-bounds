module

public import LeapsInBounds.Statements.Schur
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat

/-!
# An upper bound on weak Schur numbers

Let `B 0 = 2` and `B (f + 1) = (f + 1) * B f + 2` (values: 2, 4, 10, 32, 130,
652, 3914, …). For every `k`, `WS(k) ≤ k * B (k - 1)`: this is
`weakUpperBound_B`, and `weakUpper_5_650`, …, `weakUpper_14_473950329608` are
its values for `5 ≤ k ≤ 14`. (For `k = 1, 2` the bound is `2` and `8`, the exact
values; for `k = 3, 4` it is `30` and `128`, above the exact values `23` and
`66`.)

## The proof

Fix a coloring `χ : ℕ → Fin k` and an `N` such that `χ` has no monochromatic
solution to `x + y = z` with `0 < x < y` and `x + y ≤ N`
(`H : ¬ HasWeakMonoSum k N χ`).

A *configuration* is a nonempty set `U` of colors, a function `piv : Fin k → ℕ`
(the pivots) and a finite set `S` of numbers such that

* (a) for `c ∈ U` and `s ∈ S`: `piv c < s`, `s ≤ N` and `χ (s - piv c) = c`;
* (c) for `c, c' ∈ U` with `piv c' < piv c`: `χ (piv c - piv c') = c'`.

The main lemma (`main_lemma`) says that every configuration has
`S.card ≤ B (k - U.card)`. It is proved by induction on `k - U.card`. Let `p` be
the least element of `S`. Each other `s ∈ S` has a difference `s - p` whose
color is either in `U` or not.

* At most one `s` has `χ (s - p) ∈ U` (`lemmaC`): for such an `s`, with
  `c = χ (s - p)`, the numbers `p - piv c`, `s - p` and their sum `s - piv c` all
  have the color `c`, so `s - p = p - piv c` (`lemmaA`); and two such `s` would
  give a monochromatic solution with distinct summands. This is the one
  exceptional element of each stage.
* For each color `c ∉ U`, the `s` with `χ (s - p) = c` form the set of a
  configuration with the colors `U ∪ {c}`, where `p` is the pivot of `c`
  (`lemmaD`), so there are at most `B (k - U.card - 1)` of them.

So `S.card ≤ 1 + 1 + (k - U.card) * B (k - U.card - 1)`.

A color class of `1, …, N` is the set of the configuration with `U = {c}` and
pivot `0`, so it has at most `B (k - 1)` elements (`card_class_le`), and
`N ≤ k * B (k - 1)` (`weakSchur_le`).

Only tactics from core Lean are used (`omega`, `rw`, `rcases`, `decide`, …).
-/

@[expose] public section

namespace LeapsInBounds.Proofs.WeakSchurUpperBound

open Schur

/-- The sequence `B`: `B 0 = 2`, `B (f + 1) = (f + 1) * B f + 2`.
Values: 2, 4, 10, 32, 130, 652, 3914, 27400, 219202, … -/
def B : ℕ → ℕ
  | 0 => 2
  | f + 1 => (f + 1) * B f + 2

theorem B_zero : B 0 = 2 := rfl

theorem B_succ (f : ℕ) : B (f + 1) = (f + 1) * B f + 2 := rfl

/-! ### The hypothesis, in the form used below -/

/-- With no weak solution in `1, …, N`: if `x`, `y` and `x + y` have the same
color `c`, with `x, y > 0` and `x + y ≤ N`, then `x = y`. -/
theorem eq_of_same_color {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ)
    {x y : ℕ} {c : Fin k} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ N)
    (cx : χ x = c) (cy : χ y = c) (cxy : χ (x + y) = c) : x = y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · exact absurd ⟨x, y, hx, h, hxy, cx.trans cy.symm, cxy.trans cx.symm⟩ H
  · exact h
  · refine absurd ⟨y, x, hy, h, by omega, cy.trans cx.symm, ?_⟩ H
    rw [Nat.add_comm]
    exact cxy.trans cy.symm

/-! ### Lemma A -/

/-- **Lemma A.** In a configuration (only condition (a) is used), let `p, s ∈ S`
with `p < s` and `c ∈ U`. If `χ (s - p) = c`, then `s - p = p - piv c`.

Proof: `x = p - piv c` and `y = s - p` have the color `c`, and so does
`x + y = s - piv c ≤ N`; the hypothesis forces `x = y`. -/
theorem lemmaA {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ)
    {U : Finset (Fin k)} {piv : Fin k → ℕ} {S : Finset ℕ}
    (ha : ∀ c ∈ U, ∀ s ∈ S, piv c < s ∧ s ≤ N ∧ χ (s - piv c) = c)
    {p s : ℕ} (hp : p ∈ S) (hs : s ∈ S) (hps : p < s) {c : Fin k} (hcU : c ∈ U)
    (hcol : χ (s - p) = c) : s - p = p - piv c := by
  obtain ⟨hp1, -, hp3⟩ := ha c hcU p hp
  obtain ⟨-, hs2, hs3⟩ := ha c hcU s hs
  have e : (p - piv c) + (s - p) = s - piv c := by omega
  have h := eq_of_same_color H (x := p - piv c) (y := s - p) (by omega) (by omega)
    (by omega) hp3 hcol (by rw [e]; exact hs3)
  exact h.symm

/-! ### Lemma C -/

/-- The heart of Lemma C: two elements `s, s' > p` of `S` whose colors
`c = χ (s - p)` and `c' = χ (s' - p)` are in `U` can't have `piv c' < piv c`.

Proof: by Lemma A, `s = 2 * p - piv c` and `s' = 2 * p - piv c'`. Then
`y = s' - s = piv c - piv c'` has the color `c'` by (c), `x = s - piv c'` has the
color `c'` by (a), and so does `x + y = s' - piv c' ≤ N`. So `x = y`, that is
`s = piv c`: impossible, since `piv c < s`. -/
theorem lemmaC_ordered {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ)
    {U : Finset (Fin k)} {piv : Fin k → ℕ} {S : Finset ℕ}
    (ha : ∀ c ∈ U, ∀ s ∈ S, piv c < s ∧ s ≤ N ∧ χ (s - piv c) = c)
    (hc : ∀ c ∈ U, ∀ c' ∈ U, piv c' < piv c → χ (piv c - piv c') = c')
    {p s s' : ℕ} (hp : p ∈ S) (hs : s ∈ S) (hs' : s' ∈ S) (hps : p < s) (hps' : p < s')
    {c c' : Fin k} (hcU : c ∈ U) (hcU' : c' ∈ U)
    (hcol : χ (s - p) = c) (hcol' : χ (s' - p) = c') (hlt : piv c' < piv c) : False := by
  have eA := lemmaA H ha hp hs hps hcU hcol
  have eA' := lemmaA H ha hp hs' hps' hcU' hcol'
  obtain ⟨hpc, -, -⟩ := ha c hcU p hp
  obtain ⟨hpc', -, -⟩ := ha c' hcU' p hp
  obtain ⟨g1, -, -⟩ := ha c hcU s hs
  obtain ⟨h1, -, h3⟩ := ha c' hcU' s hs
  obtain ⟨h1', h2', h3'⟩ := ha c' hcU' s' hs'
  have hy := hc c hcU c' hcU' hlt
  have e : (s - piv c') + (piv c - piv c') = s' - piv c' := by omega
  have h := eq_of_same_color H (x := s - piv c') (y := piv c - piv c') (by omega) (by omega)
    (by omega) h3 hy (by rw [e]; exact h3')
  omega

/-- **Lemma C.** In a configuration, at most one `s ∈ S` with `s > p` has
`χ (s - p) ∈ U` (for any `p` in `S`; it is used with `p` the least element). -/
theorem lemmaC {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ)
    {U : Finset (Fin k)} {piv : Fin k → ℕ} {S : Finset ℕ}
    (ha : ∀ c ∈ U, ∀ s ∈ S, piv c < s ∧ s ≤ N ∧ χ (s - piv c) = c)
    (hc : ∀ c ∈ U, ∀ c' ∈ U, piv c' < piv c → χ (piv c - piv c') = c')
    {p : ℕ} (hp : p ∈ S) :
    (S.filter (fun s => p < s ∧ χ (s - p) ∈ U)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s hs s' hs'
  rw [Finset.mem_filter] at hs hs'
  obtain ⟨hsS, hps, hsU⟩ := hs
  obtain ⟨hsS', hps', hsU'⟩ := hs'
  have eA := lemmaA H ha hp hsS hps hsU rfl
  have eA' := lemmaA H ha hp hsS' hps' hsU' rfl
  rcases Nat.lt_trichotomy (piv (χ (s' - p))) (piv (χ (s - p))) with h | h | h
  · exact (lemmaC_ordered H ha hc hp hsS hsS' hps hps' hsU hsU' rfl rfl h).elim
  · omega
  · exact (lemmaC_ordered H ha hc hp hsS' hsS hps' hps hsU' hsU rfl rfl h).elim

/-! ### Lemma D (descent) -/

/-- **Lemma D.** In a configuration `(U, piv, S)`, let `p ∈ S` and `c ∉ U`. Then
`U ∪ {c}`, `piv` extended by `piv c = p`, and `{s ∈ S : p < s, χ (s - p) = c}`
form a configuration again: the two parts of the conclusion are its conditions
(a) and (c).

`U` is nonempty so that one of its colors gives `s ≤ N`. -/
theorem lemmaD {k N : ℕ} {χ : ℕ → Fin k}
    {U : Finset (Fin k)} {piv : Fin k → ℕ} {S : Finset ℕ} (hU : U.Nonempty)
    (ha : ∀ c ∈ U, ∀ s ∈ S, piv c < s ∧ s ≤ N ∧ χ (s - piv c) = c)
    (hc : ∀ c ∈ U, ∀ c' ∈ U, piv c' < piv c → χ (piv c - piv c') = c')
    {p : ℕ} (hp : p ∈ S) {c : Fin k} (hcU : c ∉ U) :
    (∀ d ∈ insert c U, ∀ s ∈ S.filter (fun s => p < s ∧ χ (s - p) = c),
        Function.update piv c p d < s ∧ s ≤ N ∧ χ (s - Function.update piv c p d) = d) ∧
      (∀ d ∈ insert c U, ∀ d' ∈ insert c U,
        Function.update piv c p d' < Function.update piv c p d →
          χ (Function.update piv c p d - Function.update piv c p d') = d') := by
  have hupd : ∀ d ∈ U, Function.update piv c p d = piv d := fun d hd =>
    Function.update_of_ne (fun (e : d = c) => hcU (e ▸ hd)) _ _
  have hupc : Function.update piv c p c = p := Function.update_self _ _ _
  obtain ⟨c0, hc0⟩ := hU
  constructor
  · intro d hd s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hsS, hps, hcol⟩ := hs
    rcases Finset.mem_insert.1 hd with hdc | hdU
    · rw [hdc, hupc]
      exact ⟨hps, (ha c0 hc0 s hsS).2.1, hcol⟩
    · rw [hupd d hdU]
      exact ha d hdU s hsS
  · intro d hd d' hd' hlt
    rcases Finset.mem_insert.1 hd with hdc | hdU
    · rcases Finset.mem_insert.1 hd' with hdc' | hdU'
      · -- `d = d' = c`: `p < p` is absurd
        rw [hdc, hdc'] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      · -- `d = c`, `d' ∈ U`: this is (a) for `p`
        rw [hdc, hupc, hupd d' hdU']
        exact (ha d' hdU' p hp).2.2
    · rcases Finset.mem_insert.1 hd' with hdc' | hdU'
      · -- `d ∈ U`, `d' = c`: `p < piv d` contradicts (a) for `p`
        rw [hdc', hupc, hupd d hdU] at hlt
        have := (ha d hdU p hp).1
        omega
      · -- `d, d' ∈ U`: this is the old condition (c)
        rw [hupd d hdU, hupd d' hdU'] at hlt ⊢
        exact hc d hdU d' hdU' hlt

/-! ### Splitting `S` -/

/-- If `p` is a lower bound of `S`, every element `s` of `S` is `p`, or has
`s > p` and `χ (s - p) ∈ U`, or has `s > p` and `χ (s - p) = c` for a color
`c ∉ U`. This bounds the number of elements. -/
theorem card_le_split {k : ℕ} (χ : ℕ → Fin k) (U : Finset (Fin k)) (S : Finset ℕ) (p : ℕ)
    (hmin : ∀ s ∈ S, p ≤ s) :
    S.card ≤ 1 + (S.filter (fun s => p < s ∧ χ (s - p) ∈ U)).card +
      ∑ c ∈ Uᶜ, (S.filter (fun s => p < s ∧ χ (s - p) = c)).card := by
  have hsub : S ⊆ ({p} ∪ S.filter (fun s => p < s ∧ χ (s - p) ∈ U)) ∪
      Uᶜ.biUnion (fun c => S.filter (fun s => p < s ∧ χ (s - p) = c)) := by
    intro s hs
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_biUnion]
    rcases Nat.eq_or_lt_of_le (hmin s hs) with h | h
    · exact Or.inl (Or.inl h.symm)
    · by_cases hU : χ (s - p) ∈ U
      · exact Or.inl (Or.inr ⟨hs, h, hU⟩)
      · exact Or.inr ⟨χ (s - p), Finset.mem_compl.2 hU, Finset.mem_filter.2 ⟨hs, h, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) Finset.card_biUnion_le
  rw [Finset.card_singleton]

/-! ### The main lemma -/

/-- **Main lemma.** With no weak solution in `1, …, N`, every configuration
`(U, piv, S)` with `U.card + f = k` has `S.card ≤ B f`.

By induction on `f`. If `S` is empty there is nothing to prove. Otherwise, with
`p` the least element of `S`: `S` is covered by `{p}`, the set `E` of the `s`
with `χ (s - p) ∈ U`, and the sets `S_c` of the `s` with `χ (s - p) = c`, for
`c ∉ U` (`card_le_split`); `E.card ≤ 1` (`lemmaC`); each `S_c.card ≤ B (f - 1)`
by induction (`lemmaD`); and there are `f` colors outside `U`. -/
theorem main_lemma {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ) :
    ∀ (f : ℕ) (U : Finset (Fin k)) (piv : Fin k → ℕ) (S : Finset ℕ), U.Nonempty →
      U.card + f = k →
      (∀ c ∈ U, ∀ s ∈ S, piv c < s ∧ s ≤ N ∧ χ (s - piv c) = c) →
      (∀ c ∈ U, ∀ c' ∈ U, piv c' < piv c → χ (piv c - piv c') = c') →
      S.card ≤ B f := by
  intro f
  induction f with
  | zero =>
    intro U piv S _ hcard ha hc
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [Finset.card_empty]
      exact Nat.zero_le _
    have hd := card_le_split χ U S (S.min' hS) (fun s hs => S.min'_le s hs)
    have hC := lemmaC H ha hc (S.min'_mem hS)
    have hUc : Uᶜ = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_compl, Fintype.card_fin]
      omega
    rw [hUc, Finset.sum_empty] at hd
    rw [B_zero]
    omega
  | succ f ih =>
    intro U piv S hU hcard ha hc
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [Finset.card_empty]
      exact Nat.zero_le _
    have hp := S.min'_mem hS
    have hd := card_le_split χ U S (S.min' hS) (fun s hs => S.min'_le s hs)
    have hC := lemmaC H ha hc hp
    have hUc : Uᶜ.card = f + 1 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    -- each `S_c`, for `c ∉ U`, is the set of a configuration with `U.card + 1` colors
    have hterm : ∀ c ∈ Uᶜ,
        (S.filter (fun s => S.min' hS < s ∧ χ (s - S.min' hS) = c)).card ≤ B f := by
      intro c hcU
      rw [Finset.mem_compl] at hcU
      obtain ⟨ha', hc'⟩ := lemmaD hU ha hc hp hcU
      exact ih (insert c U) (Function.update piv c (S.min' hS)) _ (Finset.insert_nonempty _ _)
        (by rw [Finset.card_insert_of_notMem hcU]; omega) ha' hc'
    have hsum : ∑ c ∈ Uᶜ, (S.filter (fun s => S.min' hS < s ∧ χ (s - S.min' hS) = c)).card
        ≤ (f + 1) * B f :=
      calc ∑ c ∈ Uᶜ, (S.filter (fun s => S.min' hS < s ∧ χ (s - S.min' hS) = c)).card
          ≤ ∑ _c ∈ Uᶜ, B f := Finset.sum_le_sum hterm
        _ = Uᶜ.card * B f := Finset.sum_const_nat (fun _ _ => rfl)
        _ = (f + 1) * B f := by rw [hUc]
    rw [B_succ]
    omega

/-! ### The theorem -/

/-- With no weak solution in `1, …, N`, each color class of `1, …, N` has at
most `B (k - 1)` elements: it is the set of the configuration with `U = {c}` and
`piv = 0`. -/
theorem card_class_le {k N : ℕ} {χ : ℕ → Fin k} (H : ¬ HasWeakMonoSum k N χ) (c : Fin k) :
    ((Finset.Icc 1 N).filter (fun s => χ s = c)).card ≤ B (k - 1) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) c.isLt
  refine main_lemma H (k - 1) {c} (fun _ => 0) _ (Finset.singleton_nonempty c)
    (by rw [Finset.card_singleton]; omega) ?_ ?_
  · intro d hd s hs
    rw [Finset.mem_singleton] at hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    rw [hd, Nat.sub_zero]
    exact ⟨by omega, hs.1.2, hs.2⟩
  · intro d _ d' _ hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- If the coloring `χ` of `1, …, N` with `k` colors has no monochromatic
solution to `x + y = z` with `0 < x < y`, then `N ≤ k * B (k - 1)`. -/
theorem weakSchur_le {k N : ℕ} (χ : ℕ → Fin k) (H : ¬ HasWeakMonoSum k N χ) :
    N ≤ k * B (k - 1) := by
  -- each number of `1, …, N` has exactly one color
  have hsum : ∑ c : Fin k, ((Finset.Icc 1 N).filter (fun s => χ s = c)).card = N := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _)),
      Nat.card_Icc, Nat.add_sub_cancel]
  calc N = ∑ c : Fin k, ((Finset.Icc 1 N).filter (fun s => χ s = c)).card := hsum.symm
    _ ≤ ∑ _c : Fin k, B (k - 1) := Finset.sum_le_sum (fun c _ => card_class_le H c)
    _ = k * B (k - 1) := by
      rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]

/-- **`WS(k) ≤ k * B (k - 1)` for every `k`.** (For `k = 0` the statement holds
for an empty reason: there is no coloring.) -/
theorem weakUpperBound_B (k : ℕ) : Schur.WeakUpperBound k (k * B (k - 1)) := by
  intro χ
  by_cases h : HasWeakMonoSum k (k * B (k - 1) + 1) χ
  · exact h
  · exact absurd (weakSchur_le χ h) (Nat.not_succ_le_self _)

/-- The bound, from the value of `k * B (k - 1)`. -/
theorem weakUpperBound_of_eq {k n : ℕ} (h : k * B (k - 1) = n) : Schur.WeakUpperBound k n :=
  h ▸ weakUpperBound_B k

/-! ### The values

`B`: 2, 4, 10, 32, 130, 652, 3914, 27400, 219202, 1972820, 19728202, 217010224,
2604122690, 33853594972; the bound for `k` colors is `k * B (k - 1)`. Each
equality `k * B (k - 1) = n` is checked by `decide`. -/

/-- The first fourteen values of `B`. -/
theorem B_values :
    B 0 = 2 ∧ B 1 = 4 ∧ B 2 = 10 ∧ B 3 = 32 ∧ B 4 = 130 ∧ B 5 = 652 ∧ B 6 = 3914 ∧
      B 7 = 27400 ∧ B 8 = 219202 ∧ B 9 = 1972820 ∧ B 10 = 19728202 ∧ B 11 = 217010224 ∧
      B 12 = 2604122690 ∧ B 13 = 33853594972 := by
  decide

/-- `WS(5) ≤ 650`. -/
theorem weakUpper_5_650 : Schur.WeakUpperBound 5 650 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(6) ≤ 3912`. -/
theorem weakUpper_6_3912 : Schur.WeakUpperBound 6 3912 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(7) ≤ 27398`. -/
theorem weakUpper_7_27398 : Schur.WeakUpperBound 7 27398 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(8) ≤ 219200`. -/
theorem weakUpper_8_219200 : Schur.WeakUpperBound 8 219200 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(9) ≤ 1972818`. -/
theorem weakUpper_9_1972818 : Schur.WeakUpperBound 9 1972818 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(10) ≤ 19728200`. -/
theorem weakUpper_10_19728200 : Schur.WeakUpperBound 10 19728200 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(11) ≤ 217010222`. -/
theorem weakUpper_11_217010222 : Schur.WeakUpperBound 11 217010222 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(12) ≤ 2604122688`. -/
theorem weakUpper_12_2604122688 : Schur.WeakUpperBound 12 2604122688 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(13) ≤ 33853594970`. -/
theorem weakUpper_13_33853594970 : Schur.WeakUpperBound 13 33853594970 :=
  weakUpperBound_of_eq (by decide)

/-- `WS(14) ≤ 473950329608`. -/
theorem weakUpper_14_473950329608 : Schur.WeakUpperBound 14 473950329608 :=
  weakUpperBound_of_eq (by decide)

end LeapsInBounds.Proofs.WeakSchurUpperBound
