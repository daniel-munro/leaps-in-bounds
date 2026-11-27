module

public import LeapsInBounds.Statements.BookRamsey
public import Mathlib

@[expose] public section

/-
Book Ramsey B5/B9: original formal proof and adapter to the
Leaps in Bounds graph-based upper-bound statement.
Source: https://doi.org/10.5281/zenodo.24559340
-/

namespace BookRamseyUpper

open scoped BigOperators

theorem degree_square_identity (d : ℤ) :
    (3*d - 40)^2 = 9*d^2 - 240*d + 1600 := by
  ring

theorem deficit_identity (D S Q : ℤ)
    (h : 6*D = -46284 + 240*S - 9*Q) :
    6*D = 116 - (9*Q - 240*S + 46400) := by
  linarith

theorem nonnegative_budget (D Q : ℤ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (h : 6*D = 116 - Q) :
    Q ≤ 116 ∧ D ≤ 19 := by
  constructor <;> omega


theorem individual_square_bound (d : ℤ) :
    1 ≤ (3*d - 40)^2 := by
  have h : d ≤ 13 ∨ 14 ≤ d := by omega
  rcases h with h | h
  · have h₁ : 3*d - 40 ≤ -1 := by omega
    nlinarith [sq_nonneg (3*d - 39)]
  · have h₁ : 2 ≤ 3*d - 40 := by omega
    nlinarith [sq_nonneg (3*d - 42)]

theorem total_square_bound (d : Fin 29 → ℤ) :
    29 ≤ ∑ i, (3 * d i - 40)^2 := by
  calc
    (29 : ℤ) = ∑ _i : Fin 29, (1 : ℤ) := by simp
    _ ≤ ∑ i, (3 * d i - 40)^2 := by
      exact Finset.sum_le_sum
        (fun i _ => individual_square_bound (d i))

theorem strong_deficit_bound
    (d : Fin 29 → ℤ) (D : ℤ)
    (h : 6*D = 116 - ∑ i, (3*d i - 40)^2) :
    D ≤ 14 := by
  have hb := total_square_bound d
  omega



-- Graph-counting definitions and identities.
abbrev V := Fin 29

def deg (A : V → V → ℤ) (i : V) : ℤ :=
  ∑ j, A i j

def common (A : V → V → ℤ) (i j : V) : ℤ :=
  ∑ k, A i k * A k j

def deficit (A : V → V → ℤ) (i j : V) : ℤ :=
  deg A i + deg A j - 19 +
    A i j * (23 - deg A i - deg A j) - common A i j +
    (if i = j then 19 - deg A i else 0)

theorem common_row_sum (A : V → V → ℤ) (i : V) :
    (∑ j, common A i j) = ∑ k, A i k * deg A k := by
  unfold common deg
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem deficit_row_sum (A : V → V → ℤ) (i : V) :
    (∑ j, deficit A i j) =
      51 * deg A i + (∑ j, deg A j) - 532 -
      (deg A i)^2 - 2 * (∑ j, A i j * deg A j) := by
  have hs : (∑ j, A i j) = deg A i := rfl
  have hc := common_row_sum A i
  unfold deficit
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [hs, hc]
  simp
  <;> ring


-- Step 4: sum the row identity over every vertex.
theorem weighted_degree_sum (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, A i j * deg A j) =
      ∑ j, (deg A j)^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  have hc : (∑ i, A i j) = deg A j := by
    unfold deg
    apply Finset.sum_congr rfl
    intro i hi
    exact hsym i j
  rw [hc, pow_two]

theorem global_deficit_sum (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) :
    3 * (∑ i, ∑ j, deficit A i j) =
      116 - ∑ i, (3 * deg A i - 40)^2 := by
  have hr : (∑ i, ∑ j, deficit A i j) =
      ∑ i, (51 * deg A i + (∑ j, deg A j) - 532 -
        (deg A i)^2 - 2 * (∑ j, A i j * deg A j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact deficit_row_sum A i
  have hw := weighted_degree_sum A hsym
  have hq : (∑ i, (3 * deg A i - 40)^2) =
      ∑ i, (9 * (deg A i)^2 - 240 * deg A i + 1600) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact degree_square_identity (deg A i)
  rw [hr, hq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [hw]
  <;> ring

-- Ordered-pair budget; no division or parity assumption required.
theorem ordered_deficit_budget (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, deficit A i j) ≤ 29 := by
  have h := global_deficit_sum A hsym
  have hb := total_square_bound (deg A)
  linarith only [h, hb]


-- Step 5: connect the deficit to the red and blue book counts.
set_option maxHeartbeats 0

def blueAdj (A : V → V → ℤ) (i j : V) : ℤ :=
  if i = j then 0 else 1 - A i j

theorem common_symmetric (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) (i j : V) :
    common A i j = common A j i := by
  unfold common
  apply Finset.sum_congr rfl
  intro k hk
  rw [hsym i k, hsym k j]
  ring

theorem deficit_symmetric (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) (i j : V) :
    deficit A i j = deficit A j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    unfold deficit
    rw [if_neg h, if_neg h', hsym i j, common_symmetric A hsym i j]
    ring

theorem deficit_diagonal (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i)
    (hloop : ∀ i, A i i = 0)
    (hbin : ∀ i j, A i j = 0 ∨ A i j = 1) (i : V) :
    deficit A i i = 0 := by
  have hc : common A i i = deg A i := by
    unfold common deg
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k i]
    rcases hbin i k with h | h <;> rw [h] <;> norm_num
  unfold deficit
  rw [hloop i, hc, if_pos rfl]
  ring

theorem blue_common_on_nonedge (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i)
    (hloop : ∀ i, A i i = 0)
    (i j : V) (hne : i ≠ j) (hzero : A i j = 0) :
    common (blueAdj A) i j = 27 - deg A i - deg A j + common A i j := by
  have hz : A j i = 0 := (hsym j i).trans hzero
  have hterm (k : V) : blueAdj A i k * blueAdj A k j =
      1 - A i k - A j k + A i k * A k j -
        (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
    by_cases hi : k = i
    · subst k
      simp [blueAdj, hne, hzero, hz, hloop]
    · by_cases hj : k = j
      · subst k
        simp [blueAdj, hne, Ne.symm hne, hzero, hz, hloop]
      · simp only [blueAdj, if_neg (Ne.symm hi), if_neg hj, if_neg hi]
        rw [hsym k j]
        ring
  unfold common deg
  rw [show (∑ k, blueAdj A i k * blueAdj A k j) =
      ∑ k, (1 - A i k - A j k + A i k * A k j -
        (if k = i then 1 else 0) - (if k = j then 1 else 0)) from
      Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp <;> ring

theorem deficit_nonnegative (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i)
    (hloop : ∀ i, A i i = 0)
    (hbin : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hred : ∀ i j, A i j = 1 → common A i j ≤ 4)
    (hblue : ∀ i j, i ≠ j → A i j = 0 → common (blueAdj A) i j ≤ 8)
    (i j : V) : 0 ≤ deficit A i j := by
  by_cases h : i = j
  · subst j
    rw [deficit_diagonal A hsym hloop hbin i]
  · rcases hbin i j with hz | ho
    · have hb := hblue i j h hz
      rw [blue_common_on_nonedge A hsym hloop i j h hz] at hb
      unfold deficit
      simp only [hz, zero_mul, if_neg h, add_zero]
      linarith
    · have hr := hred i j ho
      unfold deficit
      simp only [ho, one_mul, if_neg h, add_zero]
      linarith


-- Step 6: shifted degrees and vertex deficit identity.
def shifted (A : V → V → ℤ) (i : V) : ℤ := deg A i - 13

def rowDeficit (A : V → V → ℤ) (i : V) : ℤ :=
  ∑ j, deficit A i j

theorem shifted_sum (A : V → V → ℤ) :
    (∑ j, shifted A j) = (∑ j, deg A j) - 377 := by
  unfold shifted
  rw [Finset.sum_sub_distrib]
  norm_num

theorem shifted_weighted_sum (A : V → V → ℤ) (i : V) :
    (∑ j, A i j * shifted A j) =
      (∑ j, A i j * deg A j) - 13 * deg A i := by
  unfold shifted
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ j, A i j * deg A j) - deg A i * 13 = _
  ring

theorem shifted_row_identity (A : V → V → ℤ) (i : V) :
    rowDeficit A i = 1 + (∑ j, shifted A j) -
      shifted A i * (shifted A i + 1) -
      2 * (∑ j, A i j * shifted A j) := by
  unfold rowDeficit
  rw [deficit_row_sum, shifted_sum, shifted_weighted_sum]
  unfold shifted
  ring

theorem row_deficit_nonnegative (A : V → V → ℤ)
    (h : ∀ i j, 0 ≤ deficit A i j) (i : V) :
    0 ≤ rowDeficit A i := by
  unfold rowDeficit
  exact Finset.sum_nonneg (fun j _ => h i j)



-- Step 7: matrix commutator, written as finite sums.
def weighted (A : V → V → ℤ) (i : V) : ℤ :=
  ∑ k, A i k * deg A k

def AE (A : V → V → ℤ) (i j : V) : ℤ :=
  ∑ k, A i k * deficit A k j

def EA (A : V → V → ℤ) (i j : V) : ℤ :=
  ∑ k, deficit A i k * A k j

theorem common_assoc (A : V → V → ℤ) (i j : V) :
    (∑ k, A i k * common A k j) =
      ∑ k, common A i k * A k j := by
  unfold common
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem common_expand (A : V → V → ℤ) (i j : V) :
    common A i j = deg A i + deg A j - 19 +
      A i j * (23 - deg A i - deg A j) - deficit A i j +
      (if i = j then 19 - deg A i else 0) := by
  unfold deficit
  ring

theorem left_common_expand (A : V → V → ℤ) (i j : V) :
    (∑ k, A i k * common A k j) =
      weighted A i + deg A i * (deg A j - 19) +
      (23 - deg A j) * common A i j -
      (∑ k, A i k * A k j * deg A k) - AE A i j +
      A i j * (19 - deg A j) := by
  have ht (k : V) : A i k * common A k j =
      A i k * deg A k + A i k * (deg A j - 19) +
      (23 - deg A j) * (A i k * A k j) -
      A i k * A k j * deg A k - A i k * deficit A k j +
      (if k = j then A i k * (19 - deg A k) else 0) := by
    rw [common_expand A k j]
    split_ifs <;> ring
  rw [show (∑ k, A i k * common A k j) = _ from
    Finset.sum_congr rfl (fun k _ => ht k)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp [weighted, deg, common, AE]

theorem right_common_expand (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) (i j : V) :
    (∑ k, common A i k * A k j) =
      weighted A j + deg A j * (deg A i - 19) +
      (23 - deg A i) * common A i j -
      (∑ k, A i k * A k j * deg A k) - EA A i j +
      A i j * (19 - deg A i) := by
  have hl := left_common_expand A j i
  have hleft : (∑ k, common A i k * A k j) =
      ∑ k, A j k * common A k i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [common_symmetric A hsym i k, hsym k j]
    ring
  have htriple : (∑ k, A j k * A k i * deg A k) =
      ∑ k, A i k * A k j * deg A k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym j k, hsym k i]
    ring
  have he : AE A j i = EA A i j := by
    unfold AE EA
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym j k, deficit_symmetric A hsym k i]
    ring
  rw [hleft, hl, htriple, he, common_symmetric A hsym j i, hsym j i]

theorem commutator_identity (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i) (i j : V) :
    0 = (deg A i - deg A j) *
      (13 - deg A i - deg A j + 2 * (common A i j + A i j)) -
      rowDeficit A i + rowDeficit A j + 2 * (EA A i j - AE A i j) := by
  have h := common_assoc A i j
  rw [left_common_expand A i j, right_common_expand A hsym i j] at h
  have hi := deficit_row_sum A i
  have hj := deficit_row_sum A j
  change rowDeficit A i = 51 * deg A i + (∑ k, deg A k) - 532 -
    (deg A i)^2 - 2 * weighted A i at hi
  change rowDeficit A j = 51 * deg A j + (∑ k, deg A k) - 532 -
    (deg A j)^2 - 2 * weighted A j at hj
  linear_combination -2 * h + hi - hj

theorem clean_deficit_zero (A : V → V → ℤ)
    (hn : ∀ i j, 0 ≤ deficit A i j) (i : V)
    (hc : rowDeficit A i = 0) (j : V) : deficit A i j = 0 := by
  have hb : deficit A i j ≤ rowDeficit A i := by
    unfold rowDeficit
    exact Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j)
  linarith [hn i j]

theorem AE_bounds (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i)
    (hbin : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j) (i j : V) :
    0 ≤ AE A i j ∧ AE A i j ≤ rowDeficit A j := by
  unfold AE rowDeficit
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    rcases hbin i k with h | h <;> simp [h, hn k j]
  · apply Finset.sum_le_sum
    intro k hk
    rw [deficit_symmetric A hsym j k]
    rcases hbin i k with h | h <;> simp [h, hn k j]

theorem clean_commutator (A : V → V → ℤ)
    (hsym : ∀ i j, A i j = A j i)
    (hbin : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (i j : V) (hne : i ≠ j) (hc : rowDeficit A i = 0) :
    2 * AE A i j = rowDeficit A j + (deg A i - deg A j) *
      (if A i j = 1 then 23 - deg A i - deg A j
       else deg A i + deg A j - 25) := by
  have h := commutator_identity A hsym i j
  have he : EA A i j = 0 := by
    unfold EA
    simp [clean_deficit_zero A hn i hc]
  have hz := clean_deficit_zero A hn i hc j
  have hr := common_expand A i j
  rw [if_neg hne, hz] at hr
  rw [hc, he, hr] at h
  rcases hbin i j with ha | ha
  · rw [ha] at h ⊢
    simp at h ⊢
    nlinarith only [h]
  · rw [ha] at h ⊢
    simp at h ⊢
    nlinarith only [h]


-- Step 8: prerequisites for the finite degree classification.
-- Every symmetric loopless integer matrix has even ordered sum.
theorem symmetric_sum_even (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i)
    (hz : ∀ i, A i i = 0) (s : Finset V) :
    ∃ z : ℤ, (∑ i ∈ s, ∑ j ∈ s, A i j) = 2*z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨z, hz'⟩ := ih
    have hcol : (∑ i ∈ s, A i a) = ∑ i ∈ s, A a i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hs i a
    refine ⟨z + ∑ i ∈ s, A a i, ?_⟩
    simp only [Finset.sum_insert ha, hz a, zero_add, Finset.sum_add_distrib]
    rw [hcol, hz']
    ring

theorem degree_sum_even (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0) :
    ∃ z : ℤ, (∑ i, deg A i) = 2*z := by
  exact symmetric_sum_even A hs hz Finset.univ

theorem consecutive_product_even (x : ℤ) : ∃ z : ℤ, x*(x+1) = 2*z := by
  by_cases h : x % 2 = 0
  · have hx : x = 2*(x/2) := by omega
    refine ⟨(x/2)*(x+1), ?_⟩
    calc
      x*(x+1) = (2*(x/2))*(x+1) := congrArg (fun y : ℤ => y*(x+1)) hx
      _ = _ := by ring
  · have hx : x+1 = 2*(x/2+1) := by omega
    refine ⟨x*(x/2+1), ?_⟩
    calc
      x*(x+1) = x*(2*(x/2+1)) := congrArg (fun y : ℤ => x*y) hx
      _ = _ := by ring

theorem row_deficit_even (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0) (i : V) :
    ∃ z : ℤ, rowDeficit A i = 2*z := by
  obtain ⟨z, hsum⟩ := degree_sum_even A hs hz
  obtain ⟨w, hw⟩ := consecutive_product_even (shifted A i)
  refine ⟨z-188-w-(∑ j, A i j * shifted A j), ?_⟩
  rw [shifted_row_identity, shifted_sum, hsum, hw]
  ring

theorem dirty_minimum (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hn : ∀ i j, 0 ≤ deficit A i j) (i : V)
    (hd : rowDeficit A i ≠ 0) : 2 ≤ rowDeficit A i := by
  obtain ⟨z, h⟩ := row_deficit_even A hs hz i
  have hnon := row_deficit_nonnegative A hn i
  omega

theorem dirty_count_bound (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hn : ∀ i j, 0 ≤ deficit A i j) :
    (Finset.univ.filter (fun i : V => rowDeficit A i ≠ 0)).card ≤ 14 := by
  classical
  let s := Finset.univ.filter (fun i : V => rowDeficit A i ≠ 0)
  have hlow : (2 : ℤ) * (s.card : ℤ) ≤ ∑ i ∈ s, rowDeficit A i := by
    calc
      (2 : ℤ) * (s.card : ℤ) = ∑ _i ∈ s, (2 : ℤ) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact dirty_minimum A hs hz hn i (Finset.mem_filter.mp hi).2
  have hsub : (∑ i ∈ s, rowDeficit A i) ≤ ∑ i : V, rowDeficit A i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i hi hnot
    exact row_deficit_nonnegative A hn i
  have hbudget := ordered_deficit_budget A hs
  change (∑ i, rowDeficit A i) ≤ 29 at hbudget
  change s.card ≤ 14
  omega

theorem degree_range (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i)
    (hn : ∀ i j, 0 ≤ deficit A i j) (i : V) :
    10 ≤ deg A i ∧ deg A i ≤ 16 := by
  have hnon : 0 ≤ ∑ j : V, rowDeficit A j :=
    Finset.sum_nonneg (fun j _ => row_deficit_nonnegative A hn j)
  have h := global_deficit_sum A hs
  change 3*(∑ j : V, rowDeficit A j) = _ at h
  have htotal : (∑ j : V, (3*deg A j-40)^2) ≤ 116 := by linarith
  have hsingle : (3*deg A i-40)^2 ≤ ∑ j : V, (3*deg A j-40)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (3*deg A j-40)) (Finset.mem_univ i)
  have hb : (3*deg A i-40)^2 ≤ 116 := hsingle.trans htotal
  constructor
  · by_contra! hd
    have hx : 3*deg A i-40 ≤ -13 := by omega
    nlinarith [sq_nonneg (3*deg A i-27)]
  · by_contra! hd
    have hx : 11 ≤ 3*deg A i-40 := by omega
    nlinarith [sq_nonneg (3*deg A i-51)]

theorem clean_pair_restriction (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (i j : V) (hne : i ≠ j)
    (hi : rowDeficit A i = 0) (hj : rowDeficit A j = 0) :
    deg A i = deg A j ∨
      (A i j = 1 ∧ deg A i + deg A j = 23) ∨
      (A i j = 0 ∧ deg A i + deg A j = 25) := by
  have h := clean_commutator A hs hb hn i j hne hi
  obtain ⟨hl, hu⟩ := AE_bounds A hs hb hn i j
  have he : AE A i j = 0 := by omega
  rw [he, hj] at h
  rcases hb i j with ha | ha
  · simp [ha] at h
    have hm : (deg A i-deg A j)*(deg A i+deg A j-25) = 0 := by
      rcases h with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    rcases mul_eq_zero.mp hm with hm | hm
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ⟨ha, by omega⟩)
  · simp [ha] at h
    have hm : (deg A i-deg A j)*(23-deg A i-deg A j) = 0 := by
      rcases h with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    rcases mul_eq_zero.mp hm with hm | hm
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨ha, by omega⟩)


end BookRamseyUpper


/- Standalone finite arithmetic certificate for the degree classification.
   This file checks the enumeration, not the as-yet-unformalized theorem
   that every hypothetical avoiding graph satisfies all its filters. -/
namespace Book59DegreeClassification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Hist := List Nat
abbrev Row := Hist × Hist × Nat

def degrees : List Nat := [10, 11, 12, 13, 14, 15, 16]

def squareCost (d : Nat) : Nat := ((3 * (d : ℤ) - 40)^2).natAbs

def histAux : List Nat → Nat → Nat → List Hist
  | [], r, _ => if r = 0 then [[]] else []
  | d :: ds, r, b =>
      (List.range (min r (b / squareCost d) + 1)).flatMap fun n =>
        (histAux ds (r - n) (b - n * squareCost d)).map fun h => n :: h

def totalDegree (h : Hist) : Nat :=
  ((degrees.zip h).map fun p => p.1 * p.2).sum

def totalCost (h : Hist) : Nat :=
  ((degrees.zip h).map fun p => squareCost p.1 * p.2).sum

def histograms : List Hist :=
  (histAux degrees 29 116).filter fun h => decide (totalDegree h % 2 = 0)

def subHist : Hist → List Hist
  | [] => [[]]
  | n :: ns =>
      (List.range (n + 1)).flatMap fun c => (subHist ns).map fun cs => c :: cs

structure DegreeClass where
  d : Nat
  n : Nat
  c : Nat
  deriving DecidableEq, Repr

def classes (h c : Hist) : List DegreeClass :=
  ((degrees.zip h).zip c).map fun p => ⟨p.1.1, p.1.2, p.2⟩

def x (d : Nat) : ℤ := (d : ℤ) - 13

def redOK (d e t : Nat) : Bool :=
  decide ((((d : ℤ) - (e : ℤ)) * (23 - (d : ℤ) - (e : ℤ))).natAbs ≤ t)

def blueOK (d e t : Nat) : Bool :=
  decide ((((d : ℤ) - (e : ℤ)) * ((d : ℤ) + (e : ℤ) - 25)).natAbs ≤ t)

def cleanPairOK (cs : List DegreeClass) : Bool :=
  cs.all fun r =>
    cs.all fun q =>
      decide (r.c = 0 ∨ q.c = 0 ∨ r.d = q.d ∨ r.d + q.d = 23 ∨ r.d + q.d = 25)

def cleanCapacityOK (cs : List DegreeClass) : Bool :=
  cs.all fun r =>
    let forcedR := (cs.map fun q => if q.d ≠ r.d ∧ q.d + r.d = 23 then q.c else 0).sum
    let forcedB := (cs.map fun q => if q.d ≠ r.d ∧ q.d + r.d = 25 then q.c else 0).sum
    decide (r.c = 0 ∨ (forcedR ≤ r.d ∧ forcedB ≤ 28 - r.d))

def feasibleT (cs : List DegreeClass) (e C t : Nat) : Bool :=
  let forcedR := (cs.map fun q => if !blueOK q.d e t then q.c else 0).sum
  let possibleR := (cs.map fun q => if redOK q.d e t then q.c else 0).sum
  (cs.all fun q => decide (q.c = 0) || redOK q.d e t || blueOK q.d e t) &&
    decide (forcedR ≤ e ∧ e ≤ possibleR + (28 - C))

def rowBounds (cs : List DegreeClass) (r : DegreeClass)
    (D C : Nat) (X : ℤ) : Option (ℤ × ℤ) :=
  if r.n = 0 then some (0, 0) else
    let vals := cs.flatMap fun q => List.replicate (q.n - (if q.d = r.d then 1 else 0)) (x q.d)
    let base := 1 + X - x r.d * (x r.d + 1)
    let hi := base - 2 * (vals.take r.d).sum
    let lo := base - 2 * (vals.reverse.take r.d).sum
    if r.c ≠ 0 ∧ ¬ (lo ≤ 0 ∧ 0 ≤ hi) then none else
    if r.n = r.c then some (0, hi) else
      let ts := (List.range (2*D+1)).filter fun (t : Nat) =>
        decide (2 ≤ t ∧ t % 2 = 0 ∧ (Int.ofNat t) ≤ hi) && feasibleT cs r.d C t
      match ts with
      | [] => none
      | t :: _ => some (Int.ofNat t, hi)

def budgetBounds (cs : List DegreeClass) (D C : Nat) (X : ℤ) :
    List DegreeClass → Option (ℤ × ℤ)
  | [] => some (0, 0)
  | r :: rs => do
      let (lo, hi) ← rowBounds cs r D C X
      let (L, H) ← budgetBounds cs D C X rs
      let w : ℤ := (r.n - r.c : Nat)
      return (L + w * lo, H + w * hi)

def aggregateOK (cs : List DegreeClass) (X : ℤ) : Bool :=
  cs.all fun r =>
    let target := (r.c : ℤ) * (1 + X - x r.d * (x r.d + 1))
    let lo := 2 * (cs.map fun q => min 0 (x q.d) * (min r.c q.d : ℤ) * (q.n : ℤ)).sum
    let hi := 2 * (cs.map fun q => max 0 (x q.d) * (min r.c q.d : ℤ) * (q.n : ℤ)).sum
    decide (r.c = 0 ∨ (lo ≤ target ∧ target ≤ hi))

def pairBudget (h : Hist) : Nat := (116 - totalCost h) / 6

def admissible (h c : Hist) : Bool :=
  let D := pairBudget h
  let C := c.sum
  let X := (totalDegree h : ℤ) - 377
  let cs := classes h c
  if C < 29 - D then false else
  if !cleanPairOK cs then false else
  if !cleanCapacityOK cs then false else
  match budgetBounds cs D C X cs with
  | none => false
  | some (lo, hi) =>
      decide (lo ≤ 2 * Int.ofNat D ∧ 2 * Int.ofNat D ≤ hi) && aggregateOK cs X

def survivorsFor (h : Hist) : List Row :=
  ((subHist h).filter (admissible h)).map fun c => (h, c, pairBudget h)

def survivors : List Row := histograms.flatMap survivorsFor

-- Explicit finite computation, split into small kernel-reducible checks.
theorem histograms_eq : histograms = [
  [0, 0, 0, 0, 29, 0, 0],
  [0, 0, 0, 2, 27, 0, 0],
  [0, 0, 0, 4, 25, 0, 0],
  [0, 0, 0, 6, 23, 0, 0],
  [0, 0, 0, 7, 21, 1, 0],
  [0, 0, 0, 8, 21, 0, 0],
  [0, 0, 0, 9, 19, 1, 0],
  [0, 0, 0, 10, 19, 0, 0],
  [0, 0, 0, 11, 17, 1, 0],
  [0, 0, 0, 12, 17, 0, 0],
  [0, 0, 0, 13, 15, 1, 0],
  [0, 0, 0, 14, 13, 2, 0],
  [0, 0, 0, 14, 15, 0, 0],
  [0, 0, 0, 15, 13, 1, 0],
  [0, 0, 0, 16, 11, 2, 0],
  [0, 0, 0, 16, 13, 0, 0],
  [0, 0, 0, 17, 11, 1, 0],
  [0, 0, 0, 18, 9, 2, 0],
  [0, 0, 0, 18, 11, 0, 0],
  [0, 0, 0, 19, 9, 1, 0],
  [0, 0, 0, 20, 7, 2, 0],
  [0, 0, 0, 20, 8, 0, 1],
  [0, 0, 0, 20, 9, 0, 0],
  [0, 0, 0, 21, 5, 3, 0],
  [0, 0, 0, 21, 7, 1, 0],
  [0, 0, 0, 22, 5, 2, 0],
  [0, 0, 0, 22, 6, 0, 1],
  [0, 0, 0, 22, 7, 0, 0],
  [0, 0, 0, 23, 3, 3, 0],
  [0, 0, 0, 23, 5, 1, 0],
  [0, 0, 0, 24, 3, 2, 0],
  [0, 0, 0, 24, 4, 0, 1],
  [0, 0, 0, 24, 5, 0, 0],
  [0, 0, 0, 25, 1, 3, 0],
  [0, 0, 0, 25, 3, 1, 0],
  [0, 0, 0, 26, 1, 2, 0],
  [0, 0, 0, 26, 2, 0, 1],
  [0, 0, 0, 26, 3, 0, 0],
  [0, 0, 0, 27, 0, 1, 1],
  [0, 0, 0, 27, 1, 1, 0],
  [0, 0, 0, 28, 0, 0, 1],
  [0, 0, 0, 28, 1, 0, 0],
  [0, 0, 1, 4, 24, 0, 0],
  [0, 0, 1, 6, 22, 0, 0],
  [0, 0, 1, 8, 20, 0, 0],
  [0, 0, 1, 10, 18, 0, 0],
  [0, 0, 1, 11, 16, 1, 0],
  [0, 0, 1, 12, 16, 0, 0],
  [0, 0, 1, 13, 14, 1, 0],
  [0, 0, 1, 14, 14, 0, 0],
  [0, 0, 1, 15, 12, 1, 0],
  [0, 0, 1, 16, 12, 0, 0],
  [0, 0, 1, 17, 10, 1, 0],
  [0, 0, 1, 18, 8, 2, 0],
  [0, 0, 1, 18, 10, 0, 0],
  [0, 0, 1, 19, 8, 1, 0],
  [0, 0, 1, 20, 6, 2, 0],
  [0, 0, 1, 20, 8, 0, 0],
  [0, 0, 1, 21, 6, 1, 0],
  [0, 0, 1, 22, 4, 2, 0],
  [0, 0, 1, 22, 6, 0, 0],
  [0, 0, 1, 23, 4, 1, 0],
  [0, 0, 1, 24, 2, 2, 0],
  [0, 0, 1, 24, 3, 0, 1],
  [0, 0, 1, 24, 4, 0, 0],
  [0, 0, 1, 25, 0, 3, 0],
  [0, 0, 1, 25, 2, 1, 0],
  [0, 0, 1, 26, 0, 2, 0],
  [0, 0, 1, 26, 1, 0, 1],
  [0, 0, 1, 26, 2, 0, 0],
  [0, 0, 1, 27, 0, 1, 0],
  [0, 0, 1, 28, 0, 0, 0],
  [0, 0, 2, 8, 19, 0, 0],
  [0, 0, 2, 10, 17, 0, 0],
  [0, 0, 2, 12, 15, 0, 0],
  [0, 0, 2, 14, 13, 0, 0],
  [0, 0, 2, 15, 11, 1, 0],
  [0, 0, 2, 16, 11, 0, 0],
  [0, 0, 2, 17, 9, 1, 0],
  [0, 0, 2, 18, 9, 0, 0],
  [0, 0, 2, 19, 7, 1, 0],
  [0, 0, 2, 20, 7, 0, 0],
  [0, 0, 2, 21, 5, 1, 0],
  [0, 0, 2, 22, 3, 2, 0],
  [0, 0, 2, 22, 5, 0, 0],
  [0, 0, 2, 23, 3, 1, 0],
  [0, 0, 2, 24, 1, 2, 0],
  [0, 0, 2, 24, 3, 0, 0],
  [0, 0, 2, 25, 1, 1, 0],
  [0, 0, 2, 26, 1, 0, 0],
  [0, 0, 3, 12, 14, 0, 0],
  [0, 0, 3, 14, 12, 0, 0],
  [0, 0, 3, 16, 10, 0, 0],
  [0, 0, 3, 18, 8, 0, 0],
  [0, 0, 3, 19, 6, 1, 0],
  [0, 0, 3, 20, 6, 0, 0],
  [0, 0, 3, 21, 4, 1, 0],
  [0, 0, 3, 22, 4, 0, 0],
  [0, 0, 3, 23, 2, 1, 0],
  [0, 0, 3, 24, 2, 0, 0],
  [0, 0, 3, 25, 0, 1, 0],
  [0, 0, 3, 26, 0, 0, 0],
  [0, 0, 4, 16, 9, 0, 0],
  [0, 0, 4, 18, 7, 0, 0],
  [0, 0, 4, 20, 5, 0, 0],
  [0, 0, 4, 22, 3, 0, 0],
  [0, 0, 4, 23, 1, 1, 0],
  [0, 0, 4, 24, 1, 0, 0],
  [0, 0, 5, 20, 4, 0, 0],
  [0, 0, 5, 22, 2, 0, 0],
  [0, 0, 5, 24, 0, 0, 0],
  [0, 1, 0, 15, 13, 0, 0],
  [0, 1, 0, 17, 11, 0, 0],
  [0, 1, 0, 19, 9, 0, 0],
  [0, 1, 0, 21, 7, 0, 0],
  [0, 1, 0, 22, 5, 1, 0],
  [0, 1, 0, 23, 5, 0, 0],
  [0, 1, 0, 24, 3, 1, 0],
  [0, 1, 0, 25, 3, 0, 0],
  [0, 1, 0, 26, 1, 1, 0],
  [0, 1, 0, 27, 1, 0, 0],
  [0, 1, 1, 19, 8, 0, 0],
  [0, 1, 1, 21, 6, 0, 0],
  [0, 1, 1, 23, 4, 0, 0],
  [0, 1, 1, 25, 2, 0, 0],
  [0, 1, 1, 26, 0, 1, 0],
  [0, 1, 1, 27, 0, 0, 0],
  [0, 1, 2, 23, 3, 0, 0],
  [0, 1, 2, 25, 1, 0, 0]
  ] := by
  decide


def cost (ds h : List Nat) : Nat :=
  ((ds.zip h).map fun p => squareCost p.1 * p.2).sum

-- Completeness of the histogram generator: no budget-feasible histogram is lost.
theorem histAux_complete (ds h : List Nat) (r b : Nat)
    (hlen : h.length = ds.length) (hsum : h.sum = r)
    (hcost : cost ds h ≤ b)
    (hpos : ∀ d ∈ ds, 0 < squareCost d) :
    h ∈ histAux ds r b := by
  induction ds generalizing h r b with
  | nil =>
    cases h with
    | nil =>
      have hr : r = 0 := by simpa using hsum.symm
      simp [histAux, hr]
    | cons n ns => simp at hlen
  | cons d ds ih =>
    cases h with
    | nil => simp at hlen
    | cons n ns =>
      have hl : ns.length = ds.length := by simpa using hlen
      have hs : n + ns.sum = r := by simpa using hsum
      have hc : squareCost d * n + cost ds ns ≤ b := by
        simpa [cost] using hcost
      have hp : 0 < squareCost d := hpos d (by simp)
      have hn : n ≤ r := by omega
      have hm : n * squareCost d ≤ b := by
        rw [mul_comm]
        omega
      have hdiv : n ≤ b / squareCost d :=
        (Nat.le_div_iff_mul_le hp).2 hm
      have hrange : n ∈ List.range (min r (b / squareCost d) + 1) := by
        apply List.mem_range.mpr
        have hmin : n ≤ min r (b / squareCost d) := le_min hn hdiv
        omega
      have htail : cost ds ns ≤ b - n * squareCost d := by
        rw [mul_comm n (squareCost d)]
        omega
      have ht : ns ∈ histAux ds (r - n) (b - n * squareCost d) :=
        ih ns (r - n) (b - n * squareCost d) hl (by omega) htail
          (fun e he => hpos e (by simp [he]))
      simp only [histAux, List.mem_flatMap, List.mem_map]
      exact ⟨n, hrange, ns, ht, rfl⟩

def componentLE : List Nat → List Nat → Prop
  | [], [] => True
  | c :: cs, n :: ns => c ≤ n ∧ componentLE cs ns
  | _, _ => False

-- Every componentwise sub-histogram is enumerated.
theorem subHist_complete (h c : List Nat) (hc : componentLE c h) :
    c ∈ subHist h := by
  induction h generalizing c with
  | nil => cases c <;> simp_all [componentLE, subHist]
  | cons n ns ih =>
    cases c with
    | nil => simp [componentLE] at hc
    | cons k ks =>
      have hk : k ≤ n := hc.1
      have ht : ks ∈ subHist ns := ih ks hc.2
      simp only [subHist, List.mem_flatMap, List.mem_map]
      exact ⟨k, List.mem_range.mpr (by omega), ks, ht, rfl⟩


end Book59DegreeClassification

/- New soundness section: a weaker but equivalent-on-this-instance classifier.
   No graph-realizability assumptions are inserted into the certificate.
   All graph-side conditions are derived below from the actual matrix hypotheses. -/
namespace Book59Soundness

open scoped BigOperators
open BookRamseyUpper
open Book59DegreeClassification
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev K := Fin 7

def degree (k : K) : ℤ := 10 + (k.val : ℤ)
def sh (k : K) : ℤ := degree k - 13

def pack (h : K → ℕ) : Hist := [h 0, h 1, h 2, h 3, h 4, h 5, h 6]
def unpack (h : Hist) (k : K) : ℕ := (h[k.val]?).getD 0

theorem unpack_pack (h : K → ℕ) : unpack (pack h) = h := by
  funext k
  fin_cases k <;> rfl

theorem packed_sum (h : K → ℕ) : (pack h).sum = ∑ k, h k := by
  simp [pack, Fin.sum_univ_succ]
  <;> omega

theorem packed_cost (h : K → ℕ) :
    (totalCost (pack h) : ℤ) = ∑ k, (h k : ℤ) * (3 * degree k - 40)^2 := by
  norm_num [totalCost, degrees, pack, squareCost, degree, Fin.sum_univ_succ]
  <;> push_cast <;> ring

theorem packed_degree (h : K → ℕ) :
    (totalDegree (pack h) : ℤ) = ∑ k, (h k : ℤ) * degree k := by
  norm_num [totalDegree, degrees, pack, degree, Fin.sum_univ_succ]
  <;> push_cast <;> ring

theorem packed_component (h c : K → ℕ) (hc : ∀ k, c k ≤ h k) :
    componentLE (pack c) (pack h) := by
  exact ⟨hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6, trivial⟩

def redAllowed (k e : K) (t : ℤ) : Prop :=
  |(degree k - degree e) * (23 - degree k - degree e)| ≤ t

def blueAllowed (k e : K) (t : ℤ) : Prop :=
  |(degree k - degree e) * (degree k + degree e - 25)| ≤ t

instance (k e : K) (t : ℤ) : Decidable (redAllowed k e t) := by
  unfold redAllowed
  infer_instance
instance (k e : K) (t : ℤ) : Decidable (blueAllowed k e t) := by
  unfold blueAllowed
  infer_instance

-- Unified clean/dirty relation test: counts of forced red and forced blue
-- neighbors must fit within the two respective degrees.
def feasible (c : K → ℕ) (e : K) (t : ℤ) : Prop :=
  (∀ k : K, c k = 0 ∨ redAllowed k e t ∨ blueAllowed k e t) ∧
  (∑ k : K, if blueAllowed k e t then (0 : ℤ) else (c k : ℤ)) ≤ degree e ∧
  (∑ k : K, if redAllowed k e t then (0 : ℤ) else (c k : ℤ)) ≤ 28 - degree e

instance (c : K → ℕ) (e : K) (t : ℤ) : Decidable (feasible c e t) := by
  unfold feasible
  infer_instance

def base (h : K → ℕ) (e : K) : ℤ :=
  1 + (∑ k : K, (h k : ℤ) * sh k) - sh e * (sh e + 1)

def lowerRow (h : K → ℕ) (e : K) : ℤ :=
  base h e - 2 * ((∑ k : K, (h k : ℤ) * max 0 (sh k)) - max 0 (sh e))

def upperRow (h : K → ℕ) (e : K) : ℤ :=
  base h e - 2 * ((∑ k : K, (h k : ℤ) * min 0 (sh k)) - min 0 (sh e))

-- Every dirty row has a deficit between 2 and 28. Odd values are allowed
-- here deliberately: this is a relaxation, not an extra assumption.
def allowedTs (h c : K → ℕ) (e : K) : List ℕ :=
  (List.range 29).filter fun t =>
    decide (2 ≤ t ∧ (t : ℤ) ≤ upperRow h e ∧ feasible c e (t : ℤ))

def minDirty (h c : K → ℕ) (e : K) : ℕ :=
  (allowedTs h c e).foldr min 29

theorem foldr_min_le_of_mem (l : List ℕ) (z t : ℕ) (ht : t ∈ l) :
    l.foldr min z ≤ t := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    simp only [List.mem_cons] at ht
    change min a (l.foldr min z) ≤ t
    rcases ht with ht | ht
    · rw [ht]
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ht)

theorem minDirty_le (h c : K → ℕ) (e : K) (t : ℤ)
    (h2 : 2 ≤ t) (h28 : t ≤ 28) (hhi : t ≤ upperRow h e)
    (hf : feasible c e t) : (minDirty h c e : ℤ) ≤ t := by
  have hcast : (t.toNat : ℤ) = t := by omega
  have hm : t.toNat ∈ allowedTs h c e := by
    unfold allowedTs
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      omega
    · apply decide_eq_true
      rw [hcast]
      exact ⟨by omega, hhi, hf⟩
  have hh := foldr_min_le_of_mem (allowedTs h c e) 29 t.toNat hm
  change minDirty h c e ≤ t.toNat at hh
  omega

def relaxedOK (h c : K → ℕ) (D : ℕ) : Prop :=
  (∑ k : K, (h k - c k)) ≤ D ∧
  (∀ e : K, c e ≠ 0 → lowerRow h e ≤ 0 ∧ 0 ≤ upperRow h e ∧ feasible c e 0) ∧
  (∑ e : K, ((h e - c e : ℕ) : ℤ) * (minDirty h c e : ℤ)) ≤ 2 * (D : ℤ) ∧
  2 * (D : ℤ) ≤ ∑ e : K, ((h e - c e : ℕ) : ℤ) * upperRow h e

instance (h c : K → ℕ) (D : ℕ) : Decidable (relaxedOK h c D) := by
  unfold relaxedOK
  infer_instance

def relaxedFor (h : Hist) : List Row :=
  ((subHist h).filter fun c => decide (relaxedOK (unpack h) (unpack c) (pairBudget h))).map
    fun c => (h, c, pairBudget h)

def relaxedSurvivors : List Row := histograms.flatMap relaxedFor

-- From here on all soundness arguments use the graph matrix, not enumerated
-- assumptions about the graph. The only graph assumptions are symmetry,
-- zero diagonal, binary entries, and the two forbidden-book inequalities.

def cleanSet (A : V → V → ℤ) : Finset V :=
  Finset.univ.filter fun i => rowDeficit A i = 0

def dirtySet (A : V → V → ℤ) : Finset V :=
  Finset.univ.filter fun i => rowDeficit A i ≠ 0

def classSet (s : Finset V) (A : V → V → ℤ) (k : K) : Finset V :=
  s.filter fun i => deg A i = degree k

def count (s : Finset V) (A : V → V → ℤ) (k : K) : ℕ :=
  (classSet s A k).card

def allCount (A : V → V → ℤ) := count Finset.univ A
def cleanCount (A : V → V → ℤ) := count (cleanSet A) A

theorem degree_injective : Function.Injective degree := by
  intro a b h
  apply Fin.ext
  unfold degree at h
  omega

theorem degree_index (z : ℤ) (hl : 10 ≤ z) (hu : z ≤ 16) :
    ∃ k : K, z = degree k := by
  let n := (z - 10).toNat
  have hn : (n : ℤ) = z - 10 := by dsimp [n]; omega
  have hn' : n < 7 := by omega
  refine ⟨⟨n, hn'⟩, ?_⟩
  change z = 10 + (n : ℤ)
  omega

-- Partition an arbitrary subset of vertices into its seven degree classes.
theorem group_sum (A : V → V → ℤ)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (s : Finset V) (f : V → ℤ) :
    (∑ i ∈ s, f i) = ∑ k : K, ∑ i ∈ classSet s A k, f i := by
  classical
  symm
  simp only [classSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨k, hk⟩ := degree_index (deg A i) (hd i).1 (hd i).2
  have hp : ∀ q : K, (deg A i = degree q) ↔ q = k := by
    intro q
    constructor
    · intro hq
      exact degree_injective (hq.symm.trans hk)
    · intro hq
      simpa [hq] using hk
  simp [hp]

theorem group_weighted (A : V → V → ℤ)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (s : Finset V) (f : V → ℤ) (g : K → ℤ)
    (hg : ∀ k i, i ∈ s → deg A i = degree k → f i = g k) :
    (∑ i ∈ s, f i) = ∑ k : K, (count s A k : ℤ) * g k := by
  classical
  rw [group_sum A hd s f]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ i ∈ classSet s A k, f i) = ∑ _i ∈ classSet s A k, g k := by
      apply Finset.sum_congr rfl
      intro i hi
      have hmem : i ∈ s ∧ deg A i = degree k := Finset.mem_filter.mp hi
      exact hg k i hmem.1 hmem.2
    _ = _ := by simp [count, nsmul_eq_mul]

theorem count_total (A : V → V → ℤ)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16) (s : Finset V) :
    (∑ k : K, count s A k) = s.card := by
  have h := group_weighted A hd s (fun _ => (1 : ℤ)) (fun _ => (1 : ℤ))
    (by intros; rfl)
  have h' : (s.card : ℤ) = ∑ k : K, (count s A k : ℤ) := by
    simpa [nsmul_eq_mul] using h
  exact_mod_cast h'.symm

theorem clean_dirty_counts (A : V → V → ℤ) (k : K) :
    cleanCount A k + count (dirtySet A) A k = allCount A k := by
  classical
  have hu : classSet (cleanSet A) A k ∪ classSet (dirtySet A) A k =
      classSet Finset.univ A k := by
    ext i
    simp [classSet, cleanSet, dirtySet] <;> tauto
  have hd : Disjoint (classSet (cleanSet A) A k) (classSet (dirtySet A) A k) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hc : rowDeficit A i = 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hn : rowDeficit A i ≠ 0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    exact hn hc
  have h := Finset.card_union_of_disjoint hd
  rw [hu] at h
  exact h.symm

theorem clean_count_le (A : V → V → ℤ) (k : K) : cleanCount A k ≤ allCount A k := by
  have h := clean_dirty_counts A k
  omega

theorem dirty_count_eq (A : V → V → ℤ) (k : K) :
    count (dirtySet A) A k = allCount A k - cleanCount A k := by
  have h := clean_dirty_counts A k
  omega

theorem clean_count_vertex (A : V → V → ℤ) (k : K) (h : cleanCount A k ≠ 0) :
    ∃ i : V, rowDeficit A i = 0 ∧ deg A i = degree k := by
  have hp : 0 < (classSet (cleanSet A) A k).card := by
    change 0 < cleanCount A k
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  refine ⟨i, ?_, (Finset.mem_filter.mp hi).2⟩
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2

-- Local color thresholds, including the trivial diagonal case.
theorem edge_thresholds (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j) (i j : V) (hi : rowDeficit A i = 0) :
    (A i j = 1 → |(deg A i - deg A j) * (23 - deg A i - deg A j)| ≤ rowDeficit A j) ∧
    (A i j = 0 → |(deg A i - deg A j) * (deg A i + deg A j - 25)| ≤ rowDeficit A j) := by
  by_cases h : i = j
  · subst j
    simp [row_deficit_nonnegative A hn i]
  · have hc := clean_commutator A hs hb hn i j h hi
    obtain ⟨hlo, hhi⟩ := AE_bounds A hs hb hn i j
    constructor <;> intro ha
    · rw [ha, if_pos rfl] at hc
      apply abs_le.mpr
      constructor <;> linarith only [hc, hlo, hhi]
    · rw [ha, if_neg (by decide : (0 : ℤ) ≠ 1)] at hc
      apply abs_le.mpr
      constructor <;> linarith only [hc, hlo, hhi]

-- The blue row sum is the complementary degree.
theorem blue_row_degree (A : V → V → ℤ) (hz : ∀ i, A i i = 0) (i : V) :
    (∑ j, blueAdj A i j) = 28 - deg A i := by
  have hterm : ∀ j, blueAdj A i j = 1 - A i j - (if i = j then 1 else 0) := by
    intro j
    by_cases hij : i = j
    · subst j
      simp [blueAdj, hz]
    · simp [blueAdj, hij]
  unfold deg
  rw [show (∑ j, blueAdj A i j) =
    ∑ j, (1 - A i j - (if i = j then 1 else 0)) from
      Finset.sum_congr rfl (fun j _ => hterm j)]
  simp [Finset.sum_sub_distrib]
  <;> ring

theorem blue_nonnegative (A : V → V → ℤ)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1) (i j : V) : 0 ≤ blueAdj A i j := by
  unfold blueAdj
  split
  · norm_num
  · rcases hb i j with h | h <;> simp [h]

-- Prove the unified clean-neighbor feasibility filter for each actual vertex.
theorem vertex_feasible (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (j : V) (e : K) (he : deg A j = degree e) :
    feasible (cleanCount A) e (rowDeficit A j) := by
  classical
  let t := rowDeficit A j
  have hred : ∀ i, i ∈ cleanSet A →
      (if |(deg A i - degree e) * (deg A i + degree e - 25)| ≤ t
       then (0 : ℤ) else 1) ≤ A j i := by
    intro i hi
    have hc : rowDeficit A i = 0 := (Finset.mem_filter.mp hi).2
    have hh := edge_thresholds A hs hb hn i j hc
    rw [he] at hh
    rw [hs j i]
    split
    · rcases hb i j with h | h <;> omega
    · rename_i hnot
      rcases hb i j with h | h
      · exact (hnot (hh.2 h)).elim
      · omega
  have hblue : ∀ i, i ∈ cleanSet A →
      (if |(deg A i - degree e) * (23 - deg A i - degree e)| ≤ t
       then (0 : ℤ) else 1) ≤ blueAdj A j i := by
    intro i hi
    have hc : rowDeficit A i = 0 := (Finset.mem_filter.mp hi).2
    have hh := edge_thresholds A hs hb hn i j hc
    rw [he] at hh
    split
    · exact blue_nonnegative A hb j i
    · rename_i hnot
      have hne : j ≠ i := by
        intro hij
        subst i
        apply hnot
        rw [he, sub_self, zero_mul, abs_zero]
        exact row_deficit_nonnegative A hn j
      rcases hb i j with h | h
      · simp [blueAdj, hne, hs j i, h]
      · exact (hnot (hh.1 h)).elim
  unfold feasible
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hk : cleanCount A k = 0
    · exact Or.inl hk
    · obtain ⟨i, hi, hik⟩ := clean_count_vertex A k hk
      have hh := edge_thresholds A hs hb hn i j hi
      rw [he, hik] at hh
      rcases hb i j with h | h
      · exact Or.inr (Or.inr (hh.2 h))
      · exact Or.inr (Or.inl (hh.1 h))
  · have hg := group_weighted A hd (cleanSet A)
        (fun i => if |(deg A i - degree e) * (deg A i + degree e - 25)| ≤ t
          then (0 : ℤ) else 1)
        (fun k => if blueAllowed k e t then (0 : ℤ) else 1)
        (by intro k i hi hik; simp [hik, blueAllowed])
    have hform : (∑ k : K, if blueAllowed k e t then (0 : ℤ) else (cleanCount A k : ℤ)) =
        ∑ i ∈ cleanSet A, (if |(deg A i - degree e) * (deg A i + degree e - 25)| ≤ t
          then (0 : ℤ) else 1) := by
      rw [hg]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : blueAllowed k e t <;> simp [h, cleanCount]
    rw [hform]
    calc
      _ ≤ ∑ i ∈ cleanSet A, A j i := Finset.sum_le_sum (fun i hi => hred i hi)
      _ ≤ ∑ i : V, A j i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i hi hni
        rcases hb j i with h | h <;> omega
      _ = degree e := he
  · have hg := group_weighted A hd (cleanSet A)
        (fun i => if |(deg A i - degree e) * (23 - deg A i - degree e)| ≤ t
          then (0 : ℤ) else 1)
        (fun k => if redAllowed k e t then (0 : ℤ) else 1)
        (by intro k i hi hik; simp [hik, redAllowed])
    have hform : (∑ k : K, if redAllowed k e t then (0 : ℤ) else (cleanCount A k : ℤ)) =
        ∑ i ∈ cleanSet A, (if |(deg A i - degree e) * (23 - deg A i - degree e)| ≤ t
          then (0 : ℤ) else 1) := by
      rw [hg]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : redAllowed k e t <;> simp [h, cleanCount]
    rw [hform]
    calc
      _ ≤ ∑ i ∈ cleanSet A, blueAdj A j i := Finset.sum_le_sum (fun i hi => hblue i hi)
      _ ≤ ∑ i : V, blueAdj A j i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i hi hni
        exact blue_nonnegative A hb j i
      _ = 28 - degree e := by rw [blue_row_degree A hz, he]

-- Replace sorted-neighbor estimates by simple positive/negative bounds,
-- excluding the vertex itself. These weaker inequalities suffice.
theorem actual_row_bounds (A : V → V → ℤ)
    (hz : ∀ i, A i i = 0) (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (j : V) (e : K) (he : deg A j = degree e) :
    lowerRow (allCount A) e ≤ rowDeficit A j ∧
      rowDeficit A j ≤ upperRow (allCount A) e := by
  classical
  have hmin : ∀ i : V,
      min 0 (shifted A i) - (if i = j then min 0 (shifted A j) else 0) ≤
        A j i * shifted A i := by
    intro i
    by_cases h : i = j
    · subst i
      simp [hz]
    · rw [if_neg h, sub_zero]
      rcases hb j i with h0 | h1
      · rw [h0, zero_mul]
        exact min_le_left _ _
      · rw [h1, one_mul]
        exact min_le_right _ _
  have hmax : ∀ i : V,
      A j i * shifted A i ≤
        max 0 (shifted A i) - (if i = j then max 0 (shifted A j) else 0) := by
    intro i
    by_cases h : i = j
    · subst i
      simp [hz]
    · rw [if_neg h, sub_zero]
      rcases hb j i with h0 | h1
      · rw [h0, zero_mul]
        exact le_max_left _ _
      · rw [h1, one_mul]
        exact le_max_right _ _
  have hlo := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => hmin i)
  have hhi := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => hmax i)
  have hmi : (∑ i : V, if i = j then min 0 (shifted A j) else 0) = min 0 (shifted A j) := by simp
  have hma : (∑ i : V, if i = j then max 0 (shifted A j) else 0) = max 0 (shifted A j) := by simp
  rw [Finset.sum_sub_distrib, hmi] at hlo
  rw [Finset.sum_sub_distrib, hma] at hhi
  have hsum := group_weighted A hd Finset.univ (shifted A) sh
    (by intro k i hi hik; simp [shifted, sh, hik])
  have hsumMin := group_weighted A hd Finset.univ (fun i => min 0 (shifted A i))
    (fun k => min 0 (sh k)) (by intro k i hi hik; simp [shifted, sh, hik])
  have hsumMax := group_weighted A hd Finset.univ (fun i => max 0 (shifted A i))
    (fun k => max 0 (sh k)) (by intro k i hi hik; simp [shifted, sh, hik])
  have hsh : shifted A j = sh e := by simp [shifted, sh, he]
  have hr := shifted_row_identity A j
  rw [hsum, hsh] at hr
  rw [hsumMin, hsh] at hlo
  rw [hsumMax, hsh] at hhi
  unfold lowerRow upperRow base allCount
  constructor
  · linarith only [hr, hhi]
  · linarith only [hr, hlo]

-- The ordered deficit is even and equals twice the computed pair budget.
theorem graph_pair_budget (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16) :
    (∑ i : V, rowDeficit A i) = 2 * (pairBudget (pack (allCount A)) : ℤ) ∧
      pairBudget (pack (allCount A)) ≤ 14 := by
  obtain ⟨z, hz'⟩ := symmetric_sum_even (deficit A)
    (deficit_symmetric A hs) (deficit_diagonal A hs hz hb) Finset.univ
  change (∑ i : V, rowDeficit A i) = 2*z at hz'
  have hnon : 0 ≤ ∑ i : V, rowDeficit A i :=
    Finset.sum_nonneg (fun i _ => row_deficit_nonnegative A hn i)
  have hsq := group_weighted A hd Finset.univ (fun i => (3*deg A i-40)^2)
    (fun k => (3*degree k-40)^2) (by intro k i hi hik; rw [hik])
  change (∑ i : V, (3*deg A i-40)^2) =
    ∑ k : K, (allCount A k : ℤ) * (3*degree k-40)^2 at hsq
  rw [← packed_cost] at hsq
  have hglobal := global_deficit_sum A hs
  change 3*(∑ i : V, rowDeficit A i) = 116 - ∑ i, (3*deg A i-40)^2 at hglobal
  rw [hsq, hz'] at hglobal
  have hcap := ordered_deficit_budget A hs
  change (∑ i : V, rowDeficit A i) ≤ 29 at hcap
  have hpair : (pairBudget (pack (allCount A)) : ℤ) = z := by
    unfold pairBudget
    omega
  constructor <;> omega

-- Actual degree histograms are in the finite histogram generator.
theorem actual_histogram (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16) :
    pack (allCount A) ∈ histograms := by
  have hsum := count_total A hd Finset.univ
  change (∑ k : K, allCount A k) = (Finset.univ : Finset V).card at hsum
  rw [← packed_sum] at hsum
  have hsum' : (pack (allCount A)).sum = 29 := by simpa using hsum
  have hsq := group_weighted A hd Finset.univ (fun i => (3*deg A i-40)^2)
    (fun k => (3*degree k-40)^2) (by intro k i hi hik; rw [hik])
  change (∑ i : V, (3*deg A i-40)^2) =
    ∑ k : K, (allCount A k : ℤ) * (3*degree k-40)^2 at hsq
  rw [← packed_cost] at hsq
  have hnon : 0 ≤ ∑ i : V, rowDeficit A i :=
    Finset.sum_nonneg (fun i _ => row_deficit_nonnegative A hn i)
  have hg := global_deficit_sum A hs
  change 3*(∑ i : V, rowDeficit A i) = 116 - ∑ i, (3*deg A i-40)^2 at hg
  rw [hsq] at hg
  have hcost : totalCost (pack (allCount A)) ≤ 116 := by omega
  have hdeg := group_weighted A hd Finset.univ (deg A) degree
    (by intro k i hi hik; exact hik)
  change (∑ i : V, deg A i) = ∑ k : K, (allCount A k : ℤ) * degree k at hdeg
  rw [← packed_degree] at hdeg
  obtain ⟨z, hpar⟩ := degree_sum_even A hs hz
  rw [hdeg] at hpar
  have hmod : totalDegree (pack (allCount A)) % 2 = 0 := by omega
  have hpos : ∀ d ∈ degrees, 0 < squareCost d := by
    intro d hd'
    simp [degrees] at hd'
    rcases hd' with h | h | h | h | h | h | h <;> subst d <;> decide
  unfold histograms
  apply List.mem_filter.mpr
  constructor
  · apply histAux_complete degrees (pack (allCount A)) 29 116
    · rfl
    · exact hsum'
    · exact hcost
    · exact hpos
  · exact decide_eq_true hmod

theorem actual_clean_histogram (A : V → V → ℤ) :
    pack (cleanCount A) ∈ subHist (pack (allCount A)) := by
  apply subHist_complete
  exact packed_component (allCount A) (cleanCount A) (clean_count_le A)

-- Restricting the sum to dirty vertices does not change the total.
theorem dirty_total (A : V → V → ℤ) :
    (∑ i ∈ dirtySet A, rowDeficit A i) = ∑ i : V, rowDeficit A i := by
  classical
  simp only [dirtySet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : rowDeficit A i = 0 <;> simp [h]

theorem actual_dirty_count_bound (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (D : ℕ) (hD : (∑ i : V, rowDeficit A i) = 2*(D : ℤ)) :
    (∑ k : K, (allCount A k - cleanCount A k)) ≤ D := by
  have hcount : (∑ k : K, (allCount A k - cleanCount A k)) = (dirtySet A).card := by
    calc
      _ = ∑ k : K, count (dirtySet A) A k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (dirty_count_eq A k).symm
      _ = _ := count_total A hd _
  have hlow : (2 : ℤ)*(dirtySet A).card ≤ ∑ i ∈ dirtySet A, rowDeficit A i := by
    calc
      _ = ∑ _i ∈ dirtySet A, (2 : ℤ) := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact dirty_minimum A hs hz hn i (Finset.mem_filter.mp hi).2
  rw [dirty_total A, hD] at hlow
  omega

-- The two total-budget filters follow by summing the actual per-vertex
-- inequalities over the dirty vertices, partitioned by degree.
theorem actual_row_budget (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (D : ℕ) (hD : (∑ i : V, rowDeficit A i) = 2*(D : ℤ)) (hD14 : D ≤ 14) :
    (∑ e : K, ((allCount A e - cleanCount A e : ℕ) : ℤ) *
      (minDirty (allCount A) (cleanCount A) e : ℤ)) ≤ 2*(D : ℤ) ∧
    2*(D : ℤ) ≤ ∑ e : K, ((allCount A e - cleanCount A e : ℕ) : ℤ) * upperRow (allCount A) e := by
  have htmax : ∀ i : V, rowDeficit A i ≤ 28 := by
    intro i
    have h := Finset.single_le_sum (s := (Finset.univ : Finset V))
      (fun j _ => row_deficit_nonnegative A hn j) (Finset.mem_univ i)
    change rowDeficit A i ≤ ∑ j : V, rowDeficit A j at h
    omega
  have hgroups := group_sum A hd (dirtySet A) (rowDeficit A)
  rw [dirty_total A, hD] at hgroups
  constructor
  · rw [hgroups]
    apply Finset.sum_le_sum
    intro e he
    rw [← dirty_count_eq A e]
    calc
      _ = ∑ _i ∈ classSet (dirtySet A) A e,
        (minDirty (allCount A) (cleanCount A) e : ℤ) := by simp [count, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hmem : i ∈ dirtySet A ∧ deg A i = degree e := Finset.mem_filter.mp hi
        have hdirty : rowDeficit A i ≠ 0 := (Finset.mem_filter.mp hmem.1).2
        have h2 := dirty_minimum A hs hz hn i hdirty
        have hhi := (actual_row_bounds A hz hb hd i e hmem.2).2
        have hf := vertex_feasible A hs hz hb hn hd i e hmem.2
        exact minDirty_le (allCount A) (cleanCount A) e (rowDeficit A i) h2 (htmax i) hhi hf
  · rw [hgroups]
    apply Finset.sum_le_sum
    intro e he
    rw [← dirty_count_eq A e]
    calc
      _ ≤ ∑ _i ∈ classSet (dirtySet A) A e, upperRow (allCount A) e := by
        apply Finset.sum_le_sum
        intro i hi
        exact (actual_row_bounds A hz hb hd i e (Finset.mem_filter.mp hi).2).2
      _ = _ := by simp [count, nsmul_eq_mul]

-- This proves EVERY filter of the relaxed finite classifier from the graph.
theorem relaxed_graph_ok (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, 10 ≤ deg A i ∧ deg A i ≤ 16)
    (D : ℕ) (hD : (∑ i : V, rowDeficit A i) = 2*(D : ℤ)) (hD14 : D ≤ 14) :
    relaxedOK (allCount A) (cleanCount A) D := by
  unfold relaxedOK
  refine ⟨actual_dirty_count_bound A hs hz hn hd D hD, ?_,
    (actual_row_budget A hs hz hb hn hd D hD hD14).1,
    (actual_row_budget A hs hz hb hn hd D hD hD14).2⟩
  intro e he
  obtain ⟨i, hi, hdeg⟩ := clean_count_vertex A e he
  have hrow := actual_row_bounds A hz hb hd i e hdeg
  have hfeas := vertex_feasible A hs hz hb hn hd i e hdeg
  rw [hi] at hrow hfeas
  exact ⟨hrow.1, hrow.2, hfeas⟩

-- No assumptions about histograms, filter satisfaction or case membership.
-- The only assumptions below define a graph avoiding red B5 and blue B9.
theorem graph_survives (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hred : ∀ i j, A i j = 1 → common A i j ≤ 4)
    (hblue : ∀ i j, i ≠ j → A i j = 0 → common (blueAdj A) i j ≤ 8) :
    (pack (allCount A), pack (cleanCount A), pairBudget (pack (allCount A))) ∈ relaxedSurvivors := by
  have hn := deficit_nonnegative A hs hz hb hred hblue
  have hd := degree_range A hs hn
  obtain ⟨hD, hD14⟩ := graph_pair_budget A hs hz hb hn hd
  have hok := relaxed_graph_ok A hs hz hb hn hd _ hD hD14
  unfold relaxedSurvivors
  apply List.mem_flatMap.mpr
  refine ⟨pack (allCount A), actual_histogram A hs hz hn hd, ?_⟩
  unfold relaxedFor
  apply List.mem_map.mpr
  refine ⟨pack (cleanCount A), ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨actual_clean_histogram A, ?_⟩
  apply decide_eq_true
  rw [unpack_pack, unpack_pack]
  exact hok


-- The list computation below has the same ten rows as the old certificate.
-- Each intermediate equality is checked by the Lean kernel using decide.
theorem relaxed_check_000 : relaxedFor [0, 0, 0, 0, 29, 0, 0] = [([0, 0, 0, 0, 29, 0, 0], [0, 0, 0, 0, 29, 0, 0], 0)] := by
  decide

theorem relaxed_check_001 : relaxedFor [0, 0, 0, 2, 27, 0, 0] = [] := by
  decide

theorem relaxed_check_002 : relaxedFor [0, 0, 0, 4, 25, 0, 0] = [] := by
  decide

theorem relaxed_check_003 : relaxedFor [0, 0, 0, 6, 23, 0, 0] = [] := by
  decide

theorem relaxed_check_004 : relaxedFor [0, 0, 0, 7, 21, 1, 0] = [] := by
  decide

theorem relaxed_check_005 : relaxedFor [0, 0, 0, 8, 21, 0, 0] = [] := by
  decide

theorem relaxed_check_006 : relaxedFor [0, 0, 0, 9, 19, 1, 0] = [] := by
  decide

theorem relaxed_check_007 : relaxedFor [0, 0, 0, 10, 19, 0, 0] = [] := by
  decide

theorem relaxed_check_008 : relaxedFor [0, 0, 0, 11, 17, 1, 0] = [] := by
  decide

theorem relaxed_check_009 : relaxedFor [0, 0, 0, 12, 17, 0, 0] = [] := by
  decide

theorem relaxed_check_010 : relaxedFor [0, 0, 0, 13, 15, 1, 0] = [] := by
  decide

theorem relaxed_check_011 : relaxedFor [0, 0, 0, 14, 13, 2, 0] = [] := by
  decide

theorem relaxed_check_012 : relaxedFor [0, 0, 0, 14, 15, 0, 0] = [] := by
  decide

theorem relaxed_check_013 : relaxedFor [0, 0, 0, 15, 13, 1, 0] = [] := by
  decide

theorem relaxed_check_014 : relaxedFor [0, 0, 0, 16, 11, 2, 0] = [] := by
  decide

theorem relaxed_check_015 : relaxedFor [0, 0, 0, 16, 13, 0, 0] = [] := by
  decide

theorem relaxed_check_016 : relaxedFor [0, 0, 0, 17, 11, 1, 0] = [] := by
  decide

theorem relaxed_check_017 : relaxedFor [0, 0, 0, 18, 9, 2, 0] = [] := by
  decide

theorem relaxed_check_018 : relaxedFor [0, 0, 0, 18, 11, 0, 0] = [] := by
  decide

theorem relaxed_check_019 : relaxedFor [0, 0, 0, 19, 9, 1, 0] = [] := by
  decide

theorem relaxed_check_020 : relaxedFor [0, 0, 0, 20, 7, 2, 0] = [] := by
  decide

theorem relaxed_check_021 : relaxedFor [0, 0, 0, 20, 8, 0, 1] = [] := by
  decide

theorem relaxed_check_022 : relaxedFor [0, 0, 0, 20, 9, 0, 0] = [] := by
  decide

theorem relaxed_check_023 : relaxedFor [0, 0, 0, 21, 5, 3, 0] = [] := by
  decide

theorem relaxed_check_024 : relaxedFor [0, 0, 0, 21, 7, 1, 0] = [] := by
  decide

theorem relaxed_check_025 : relaxedFor [0, 0, 0, 22, 5, 2, 0] = [] := by
  decide

theorem relaxed_check_026 : relaxedFor [0, 0, 0, 22, 6, 0, 1] = [] := by
  decide

theorem relaxed_check_027 : relaxedFor [0, 0, 0, 22, 7, 0, 0] = [] := by
  decide

theorem relaxed_check_028 : relaxedFor [0, 0, 0, 23, 3, 3, 0] = [] := by
  decide

theorem relaxed_check_029 : relaxedFor [0, 0, 0, 23, 5, 1, 0] = [] := by
  decide

theorem relaxed_check_030 : relaxedFor [0, 0, 0, 24, 3, 2, 0] = [] := by
  decide

theorem relaxed_check_031 : relaxedFor [0, 0, 0, 24, 4, 0, 1] = [] := by
  decide

theorem relaxed_check_032 : relaxedFor [0, 0, 0, 24, 5, 0, 0] = [([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 22, 0, 0, 0], 12),
  ([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 23, 0, 0, 0], 12)] := by
  decide

theorem relaxed_check_033 : relaxedFor [0, 0, 0, 25, 1, 3, 0] = [] := by
  decide

theorem relaxed_check_034 : relaxedFor [0, 0, 0, 25, 3, 1, 0] = [] := by
  decide

theorem relaxed_check_035 : relaxedFor [0, 0, 0, 26, 1, 2, 0] = [] := by
  decide

theorem relaxed_check_036 : relaxedFor [0, 0, 0, 26, 2, 0, 1] = [] := by
  decide

theorem relaxed_check_037 : relaxedFor [0, 0, 0, 26, 3, 0, 0] = [] := by
  decide

theorem relaxed_check_038 : relaxedFor [0, 0, 0, 27, 0, 1, 1] = [] := by
  decide

theorem relaxed_check_039 : relaxedFor [0, 0, 0, 27, 1, 1, 0] = [] := by
  decide

theorem relaxed_check_040 : relaxedFor [0, 0, 0, 28, 0, 0, 1] = [] := by
  decide

theorem relaxed_check_041 : relaxedFor [0, 0, 0, 28, 1, 0, 0] = [] := by
  decide

theorem relaxed_check_042 : relaxedFor [0, 0, 1, 4, 24, 0, 0] = [] := by
  decide

theorem relaxed_check_043 : relaxedFor [0, 0, 1, 6, 22, 0, 0] = [] := by
  decide

theorem relaxed_check_044 : relaxedFor [0, 0, 1, 8, 20, 0, 0] = [] := by
  decide

theorem relaxed_check_045 : relaxedFor [0, 0, 1, 10, 18, 0, 0] = [] := by
  decide

theorem relaxed_check_046 : relaxedFor [0, 0, 1, 11, 16, 1, 0] = [] := by
  decide

theorem relaxed_check_047 : relaxedFor [0, 0, 1, 12, 16, 0, 0] = [] := by
  decide

theorem relaxed_check_048 : relaxedFor [0, 0, 1, 13, 14, 1, 0] = [] := by
  decide

theorem relaxed_check_049 : relaxedFor [0, 0, 1, 14, 14, 0, 0] = [] := by
  decide

theorem relaxed_check_050 : relaxedFor [0, 0, 1, 15, 12, 1, 0] = [] := by
  decide

theorem relaxed_check_051 : relaxedFor [0, 0, 1, 16, 12, 0, 0] = [] := by
  decide

theorem relaxed_check_052 : relaxedFor [0, 0, 1, 17, 10, 1, 0] = [] := by
  decide

theorem relaxed_check_053 : relaxedFor [0, 0, 1, 18, 8, 2, 0] = [] := by
  decide

theorem relaxed_check_054 : relaxedFor [0, 0, 1, 18, 10, 0, 0] = [] := by
  decide

theorem relaxed_check_055 : relaxedFor [0, 0, 1, 19, 8, 1, 0] = [] := by
  decide

theorem relaxed_check_056 : relaxedFor [0, 0, 1, 20, 6, 2, 0] = [] := by
  decide

theorem relaxed_check_057 : relaxedFor [0, 0, 1, 20, 8, 0, 0] = [] := by
  decide

theorem relaxed_check_058 : relaxedFor [0, 0, 1, 21, 6, 1, 0] = [] := by
  decide

theorem relaxed_check_059 : relaxedFor [0, 0, 1, 22, 4, 2, 0] = [] := by
  decide

theorem relaxed_check_060 : relaxedFor [0, 0, 1, 22, 6, 0, 0] = [] := by
  decide

theorem relaxed_check_061 : relaxedFor [0, 0, 1, 23, 4, 1, 0] = [] := by
  decide

theorem relaxed_check_062 : relaxedFor [0, 0, 1, 24, 2, 2, 0] = [] := by
  decide

theorem relaxed_check_063 : relaxedFor [0, 0, 1, 24, 3, 0, 1] = [] := by
  decide

theorem relaxed_check_064 : relaxedFor [0, 0, 1, 24, 4, 0, 0] = [([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 23, 0, 0, 0], 10),
  ([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 24, 0, 0, 0], 10)] := by
  decide

theorem relaxed_check_065 : relaxedFor [0, 0, 1, 25, 0, 3, 0] = [] := by
  decide

theorem relaxed_check_066 : relaxedFor [0, 0, 1, 25, 2, 1, 0] = [] := by
  decide

theorem relaxed_check_067 : relaxedFor [0, 0, 1, 26, 0, 2, 0] = [] := by
  decide

theorem relaxed_check_068 : relaxedFor [0, 0, 1, 26, 1, 0, 1] = [] := by
  decide

theorem relaxed_check_069 : relaxedFor [0, 0, 1, 26, 2, 0, 0] = [] := by
  decide

theorem relaxed_check_070 : relaxedFor [0, 0, 1, 27, 0, 1, 0] = [] := by
  decide

theorem relaxed_check_071 : relaxedFor [0, 0, 1, 28, 0, 0, 0] = [([0, 0, 1, 28, 0, 0, 0], [0, 0, 1, 16, 0, 0, 0], 12)] := by
  decide

theorem relaxed_check_072 : relaxedFor [0, 0, 2, 8, 19, 0, 0] = [] := by
  decide

theorem relaxed_check_073 : relaxedFor [0, 0, 2, 10, 17, 0, 0] = [] := by
  decide

theorem relaxed_check_074 : relaxedFor [0, 0, 2, 12, 15, 0, 0] = [] := by
  decide

theorem relaxed_check_075 : relaxedFor [0, 0, 2, 14, 13, 0, 0] = [] := by
  decide

theorem relaxed_check_076 : relaxedFor [0, 0, 2, 15, 11, 1, 0] = [] := by
  decide

theorem relaxed_check_077 : relaxedFor [0, 0, 2, 16, 11, 0, 0] = [] := by
  decide

theorem relaxed_check_078 : relaxedFor [0, 0, 2, 17, 9, 1, 0] = [] := by
  decide

theorem relaxed_check_079 : relaxedFor [0, 0, 2, 18, 9, 0, 0] = [] := by
  decide

theorem relaxed_check_080 : relaxedFor [0, 0, 2, 19, 7, 1, 0] = [] := by
  decide

theorem relaxed_check_081 : relaxedFor [0, 0, 2, 20, 7, 0, 0] = [] := by
  decide

theorem relaxed_check_082 : relaxedFor [0, 0, 2, 21, 5, 1, 0] = [] := by
  decide

theorem relaxed_check_083 : relaxedFor [0, 0, 2, 22, 3, 2, 0] = [] := by
  decide

theorem relaxed_check_084 : relaxedFor [0, 0, 2, 22, 5, 0, 0] = [] := by
  decide

theorem relaxed_check_085 : relaxedFor [0, 0, 2, 23, 3, 1, 0] = [] := by
  decide

theorem relaxed_check_086 : relaxedFor [0, 0, 2, 24, 1, 2, 0] = [] := by
  decide

theorem relaxed_check_087 : relaxedFor [0, 0, 2, 24, 3, 0, 0] = [([0, 0, 2, 24, 3, 0, 0], [0, 0, 0, 24, 0, 0, 0], 8)] := by
  decide

theorem relaxed_check_088 : relaxedFor [0, 0, 2, 25, 1, 1, 0] = [] := by
  decide

theorem relaxed_check_089 : relaxedFor [0, 0, 2, 26, 1, 0, 0] = [] := by
  decide

theorem relaxed_check_090 : relaxedFor [0, 0, 3, 12, 14, 0, 0] = [] := by
  decide

theorem relaxed_check_091 : relaxedFor [0, 0, 3, 14, 12, 0, 0] = [] := by
  decide

theorem relaxed_check_092 : relaxedFor [0, 0, 3, 16, 10, 0, 0] = [] := by
  decide

theorem relaxed_check_093 : relaxedFor [0, 0, 3, 18, 8, 0, 0] = [] := by
  decide

theorem relaxed_check_094 : relaxedFor [0, 0, 3, 19, 6, 1, 0] = [] := by
  decide

theorem relaxed_check_095 : relaxedFor [0, 0, 3, 20, 6, 0, 0] = [] := by
  decide

theorem relaxed_check_096 : relaxedFor [0, 0, 3, 21, 4, 1, 0] = [] := by
  decide

theorem relaxed_check_097 : relaxedFor [0, 0, 3, 22, 4, 0, 0] = [] := by
  decide

theorem relaxed_check_098 : relaxedFor [0, 0, 3, 23, 2, 1, 0] = [] := by
  decide

theorem relaxed_check_099 : relaxedFor [0, 0, 3, 24, 2, 0, 0] = [] := by
  decide

theorem relaxed_check_100 : relaxedFor [0, 0, 3, 25, 0, 1, 0] = [] := by
  decide

theorem relaxed_check_101 : relaxedFor [0, 0, 3, 26, 0, 0, 0] = [([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 22, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 23, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 24, 0, 0, 0], 7)] := by
  decide

theorem relaxed_check_102 : relaxedFor [0, 0, 4, 16, 9, 0, 0] = [] := by
  decide

theorem relaxed_check_103 : relaxedFor [0, 0, 4, 18, 7, 0, 0] = [] := by
  decide

theorem relaxed_check_104 : relaxedFor [0, 0, 4, 20, 5, 0, 0] = [] := by
  decide

theorem relaxed_check_105 : relaxedFor [0, 0, 4, 22, 3, 0, 0] = [] := by
  decide

theorem relaxed_check_106 : relaxedFor [0, 0, 4, 23, 1, 1, 0] = [] := by
  decide

theorem relaxed_check_107 : relaxedFor [0, 0, 4, 24, 1, 0, 0] = [] := by
  decide

theorem relaxed_check_108 : relaxedFor [0, 0, 5, 20, 4, 0, 0] = [] := by
  decide

theorem relaxed_check_109 : relaxedFor [0, 0, 5, 22, 2, 0, 0] = [] := by
  decide

theorem relaxed_check_110 : relaxedFor [0, 0, 5, 24, 0, 0, 0] = [] := by
  decide

theorem relaxed_check_111 : relaxedFor [0, 1, 0, 15, 13, 0, 0] = [] := by
  decide

theorem relaxed_check_112 : relaxedFor [0, 1, 0, 17, 11, 0, 0] = [] := by
  decide

theorem relaxed_check_113 : relaxedFor [0, 1, 0, 19, 9, 0, 0] = [] := by
  decide

theorem relaxed_check_114 : relaxedFor [0, 1, 0, 21, 7, 0, 0] = [] := by
  decide

theorem relaxed_check_115 : relaxedFor [0, 1, 0, 22, 5, 1, 0] = [] := by
  decide

theorem relaxed_check_116 : relaxedFor [0, 1, 0, 23, 5, 0, 0] = [] := by
  decide

theorem relaxed_check_117 : relaxedFor [0, 1, 0, 24, 3, 1, 0] = [] := by
  decide

theorem relaxed_check_118 : relaxedFor [0, 1, 0, 25, 3, 0, 0] = [] := by
  decide

theorem relaxed_check_119 : relaxedFor [0, 1, 0, 26, 1, 1, 0] = [] := by
  decide

theorem relaxed_check_120 : relaxedFor [0, 1, 0, 27, 1, 0, 0] = [] := by
  decide

theorem relaxed_check_121 : relaxedFor [0, 1, 1, 19, 8, 0, 0] = [] := by
  decide

theorem relaxed_check_122 : relaxedFor [0, 1, 1, 21, 6, 0, 0] = [] := by
  decide

theorem relaxed_check_123 : relaxedFor [0, 1, 1, 23, 4, 0, 0] = [] := by
  decide

theorem relaxed_check_124 : relaxedFor [0, 1, 1, 25, 2, 0, 0] = [] := by
  decide

theorem relaxed_check_125 : relaxedFor [0, 1, 1, 26, 0, 1, 0] = [] := by
  decide

theorem relaxed_check_126 : relaxedFor [0, 1, 1, 27, 0, 0, 0] = [] := by
  decide

theorem relaxed_check_127 : relaxedFor [0, 1, 2, 23, 3, 0, 0] = [] := by
  decide

theorem relaxed_check_128 : relaxedFor [0, 1, 2, 25, 1, 0, 0] = [] := by
  decide

theorem relaxed_classification_computation : relaxedSurvivors = [([0, 0, 0, 0, 29, 0, 0], [0, 0, 0, 0, 29, 0, 0], 0),
  ([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 22, 0, 0, 0], 12),
  ([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 23, 0, 0, 0], 12),
  ([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 23, 0, 0, 0], 10),
  ([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 24, 0, 0, 0], 10),
  ([0, 0, 1, 28, 0, 0, 0], [0, 0, 1, 16, 0, 0, 0], 12),
  ([0, 0, 2, 24, 3, 0, 0], [0, 0, 0, 24, 0, 0, 0], 8),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 22, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 23, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 24, 0, 0, 0], 7)] := by
  simp only [relaxedSurvivors, histograms_eq, List.flatMap_cons, List.flatMap_nil,
    relaxed_check_000, relaxed_check_001, relaxed_check_002, relaxed_check_003, relaxed_check_004,
    relaxed_check_005, relaxed_check_006, relaxed_check_007, relaxed_check_008, relaxed_check_009,
    relaxed_check_010, relaxed_check_011, relaxed_check_012, relaxed_check_013, relaxed_check_014,
    relaxed_check_015, relaxed_check_016, relaxed_check_017, relaxed_check_018, relaxed_check_019,
    relaxed_check_020, relaxed_check_021, relaxed_check_022, relaxed_check_023, relaxed_check_024,
    relaxed_check_025, relaxed_check_026, relaxed_check_027, relaxed_check_028, relaxed_check_029,
    relaxed_check_030, relaxed_check_031, relaxed_check_032, relaxed_check_033, relaxed_check_034,
    relaxed_check_035, relaxed_check_036, relaxed_check_037, relaxed_check_038, relaxed_check_039,
    relaxed_check_040, relaxed_check_041, relaxed_check_042, relaxed_check_043, relaxed_check_044,
    relaxed_check_045, relaxed_check_046, relaxed_check_047, relaxed_check_048, relaxed_check_049,
    relaxed_check_050, relaxed_check_051, relaxed_check_052, relaxed_check_053, relaxed_check_054,
    relaxed_check_055, relaxed_check_056, relaxed_check_057, relaxed_check_058, relaxed_check_059,
    relaxed_check_060, relaxed_check_061, relaxed_check_062, relaxed_check_063, relaxed_check_064,
    relaxed_check_065, relaxed_check_066, relaxed_check_067, relaxed_check_068, relaxed_check_069,
    relaxed_check_070, relaxed_check_071, relaxed_check_072, relaxed_check_073, relaxed_check_074,
    relaxed_check_075, relaxed_check_076, relaxed_check_077, relaxed_check_078, relaxed_check_079,
    relaxed_check_080, relaxed_check_081, relaxed_check_082, relaxed_check_083, relaxed_check_084,
    relaxed_check_085, relaxed_check_086, relaxed_check_087, relaxed_check_088, relaxed_check_089,
    relaxed_check_090, relaxed_check_091, relaxed_check_092, relaxed_check_093, relaxed_check_094,
    relaxed_check_095, relaxed_check_096, relaxed_check_097, relaxed_check_098, relaxed_check_099,
    relaxed_check_100, relaxed_check_101, relaxed_check_102, relaxed_check_103, relaxed_check_104,
    relaxed_check_105, relaxed_check_106, relaxed_check_107, relaxed_check_108, relaxed_check_109,
    relaxed_check_110, relaxed_check_111, relaxed_check_112, relaxed_check_113, relaxed_check_114,
    relaxed_check_115, relaxed_check_116, relaxed_check_117, relaxed_check_118, relaxed_check_119,
    relaxed_check_120, relaxed_check_121, relaxed_check_122, relaxed_check_123, relaxed_check_124,
    relaxed_check_125, relaxed_check_126, relaxed_check_127, relaxed_check_128, List.nil_append, List.cons_append, List.append_nil]

-- Main enumeration soundness theorem: hypotheses are only those of an
-- actual 29-vertex avoiding graph. There are no assumed filter conditions.
theorem graph_classification (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hred : ∀ i j, A i j = 1 → common A i j ≤ 4)
    (hblue : ∀ i j, i ≠ j → A i j = 0 → common (blueAdj A) i j ≤ 8) :
    (pack (allCount A), pack (cleanCount A), pairBudget (pack (allCount A))) ∈
      ([([0, 0, 0, 0, 29, 0, 0], [0, 0, 0, 0, 29, 0, 0], 0),
  ([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 22, 0, 0, 0], 12),
  ([0, 0, 0, 24, 5, 0, 0], [0, 0, 0, 23, 0, 0, 0], 12),
  ([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 23, 0, 0, 0], 10),
  ([0, 0, 1, 24, 4, 0, 0], [0, 0, 0, 24, 0, 0, 0], 10),
  ([0, 0, 1, 28, 0, 0, 0], [0, 0, 1, 16, 0, 0, 0], 12),
  ([0, 0, 2, 24, 3, 0, 0], [0, 0, 0, 24, 0, 0, 0], 8),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 22, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 23, 0, 0, 0], 7),
  ([0, 0, 3, 26, 0, 0, 0], [0, 0, 0, 24, 0, 0, 0], 7)] : List Row) := by
  have h := graph_survives A hs hz hb hred hblue
  rw [relaxed_classification_computation] at h
  exact h


end Book59Soundness

/- New proof block. Append after EnumerationSoundness_FullCandidate.lean.
   Candidate, not compiled here. Cases I, II, III, V and VI are addressed;
   Case IV integer-polynomial core included, but cycle-vector construction,
   histogram assembly and the final theorem are not included. -/
namespace Book59CaseElimination
open scoped BigOperators
open BookRamseyUpper Book59Soundness
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- A symmetric cyclic triple sum with repeated-index terms zero is a multiple of 3.
theorem cyclic_triple_multiple (f : V → V → V → ℤ)
    (hc : ∀ i j k, f i j k = f j k i)
    (hd₁ : ∀ i j, f i i j = 0)
    (hd₂ : ∀ i j, f i j i = 0)
    (hd₃ : ∀ i j, f i j j = 0)
    (s : Finset V) :
    ∃ z : ℤ, (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k) = 3*z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨z, hz⟩ := ih
    have hB : (∑ i ∈ s, ∑ j ∈ s, f i a j) =
        ∑ i ∈ s, ∑ j ∈ s, f a i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hc j a i
    have hC : (∑ i ∈ s, ∑ j ∈ s, f i j a) =
        ∑ i ∈ s, ∑ j ∈ s, f a i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact (hc a i j).symm
    refine ⟨z + ∑ i ∈ s, ∑ j ∈ s, f a i j, ?_⟩
    simp only [Finset.sum_insert ha, hd₁, hd₂, hd₃,
      Finset.sum_add_distrib, Finset.sum_const_zero, zero_add, add_zero]
    rw [hB, hC, hz]
    ring

-- CASE I: all degrees fourteen. No eigenvalue argument is needed.
theorem case_I (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (hd : ∀ i, deg A i = 14) : False := by
  have hg := global_deficit_sum A hs
  have hsum : (∑ i : V, (3*deg A i-40)^2) = 116 := by
    simp [hd]
  rw [hsum] at hg
  have htot : (∑ i : V, rowDeficit A i) = 0 := by
    change 3*(∑ i : V, rowDeficit A i) = 116-116 at hg
    omega
  have he : ∀ i j, deficit A i j = 0 := by
    intro i j
    have hi := Finset.single_le_sum (s := (Finset.univ : Finset V))
      (fun k _ => row_deficit_nonnegative A hn k) (Finset.mem_univ i)
    rw [htot] at hi
    exact clean_deficit_zero A hn i (le_antisymm hi (row_deficit_nonnegative A hn i)) j
  have hr : ∀ i j, A i j = 1 → common A i j = 4 := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      rw [hz] at hij
      omega
    have h := he i j
    unfold deficit at h
    rw [if_neg hne, hij, hd i, hd j] at h
    linarith
  let f : V → V → V → ℤ := fun i j k => A i j * (A j k * A k i)
  obtain ⟨z, htr⟩ := cyclic_triple_multiple f
    (by intro i j k; dsimp [f]; ring)
    (by intro i j; simp [f, hz])
    (by intro i j; simp [f, hz])
    (by intro i j; simp [f, hz]) Finset.univ
  have hval : (∑ i : V, ∑ j : V, ∑ k : V, f i j k) = 1624 := by
    calc
      _ = ∑ i : V, ∑ j : V, A i j * common A i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        unfold common
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        rw [hs j k, hs k i]
        ring
      _ = ∑ i : V, ∑ j : V, 4 * A i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rcases hb i j with h | h
        · simp [h]
        · simp [h, hr i j h]
      _ = ∑ i : V, 4 * deg A i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [deg, Finset.mul_sum]
      _ = 1624 := by simp [hd]
  rw [hval] at htr
  omega

-- A generic finite-set cardinality estimate used in the mixed-degree cases.
theorem sum_indicator (s : Finset V) :
    (∑ i : V, if i ∈ s then (1 : ℤ) else 0) = (s.card : ℤ) := by
  rw [← Finset.sum_filter]
  simp

-- CASES II and III: the common contradiction after deriving the row identities.
-- The hypotheses hclean, hhigh, hno and hcap describe actual vertex classes.
-- hrows and hbudget must be derived from the histogram and shifted identity.
theorem cases_II_III_core (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (C H : Finset V)
    (hclean : ∀ i ∈ C, deg A i = 13 ∧ rowDeficit A i = 0)
    (hhigh : ∀ i ∈ H, deg A i = 14 ∧ rowDeficit A i = 4)
    (hno : ∀ i ∈ H, ∀ j ∈ H, A i j = 0)
    (hcap : 27 ≤ (C.card : ℤ) + H.card)
    (hH : 4 ≤ H.card)
    (hbudget : (∑ i : V, rowDeficit A i) ≤ 4*(H.card : ℤ)+4) : False := by
  classical
  have hdis : Disjoint C H := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 := (hclean i hi).1
    have h2 := (hhigh i hj).1
    omega
  have hcount : ((C ∪ H).card : ℤ) = (C.card : ℤ) + H.card := by
    exact_mod_cast Finset.card_union_of_disjoint hdis
  have hother : (∑ i : V, if i ∈ C ∪ H then (0 : ℤ) else 1) ≤ 2 := by
    have hh := sum_indicator (C ∪ H)
    have hp : (∑ i : V, if i ∈ C ∪ H then (0 : ℤ) else 1) =
        ∑ i : V, (1 - (if i ∈ C ∪ H then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ∈ C ∪ H <;> simp [h]
    rw [hp, Finset.sum_sub_distrib, hh]
    norm_num
    omega
  have hzero : ∀ w ∈ H, ∀ u ∈ H, deficit A w u = 0 := by
    intro w hw u hu
    by_cases hwu : w = u
    · subst u
      exact deficit_diagonal A hs hz hb w
    by_contra hne
    have hpos : 0 < deficit A w u := lt_of_le_of_ne (hn w u) (Ne.symm hne)
    have hforce : ∀ v ∈ C, A w v = 1 → A u v = 1 := by
      intro v hv hvw
      have hvne : v ≠ w := by
        intro heq
        subst v
        exact (Finset.disjoint_left.mp hdis hv hw)
      have hc := clean_commutator A hs hb hn v w hvne (hclean v hv).2
      rw [hs v w, hvw, if_pos rfl, (hclean v hv).1,
        (hhigh w hw).1, (hhigh w hw).2] at hc
      norm_num at hc
      have hAE : AE A v w = 4 := by omega
      have hsum : (∑ j : V, (1-A v j)*deficit A w j) = 0 := by
        have hs' : (∑ j : V, A v j * deficit A w j) = AE A v w := by
          unfold AE
          apply Finset.sum_congr rfl
          intro j hj
          rw [deficit_symmetric A hs w j]
        simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
        change rowDeficit A w - (∑ j : V, A v j * deficit A w j) = 0
        rw [hs', (hhigh w hw).2, hAE] <;> norm_num
      have hle := Finset.single_le_sum (s := (Finset.univ : Finset V))
        (f := fun j => (1-A v j)*deficit A w j)
        (fun j _ => by rcases hb v j with h | h <;> simp [h, hn w j])
        (Finset.mem_univ u)
      rw [hsum] at hle
      rw [hs u v]
      rcases hb v u with h | h
      · simp [h] at hle
        omega
      · exact h
    have hterm : ∀ v : V, A w v ≤ A w v * A v u +
        (if v ∈ C ∪ H then 0 else 1) := by
      intro v
      by_cases hv : v ∈ C ∪ H
      · rw [if_pos hv, add_zero]
        rcases Finset.mem_union.mp hv with hc | hh
        · rcases hb w v with h | h
          · simp [h]
          · rw [h, hs v u, hforce v hc h]
            norm_num
        · simp [hno w hw v hh]
      · rw [if_neg hv]
        rcases hb w v with h | h <;> rcases hb v u with h' | h' <;> norm_num [h,h']
    have hle := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hterm v)
    rw [Finset.sum_add_distrib] at hle
    change deg A w ≤ common A w u + _ at hle
    have hed := hn w u
    unfold deficit at hed
    rw [if_neg hwu, hno w hw u hu, (hhigh w hw).1, (hhigh u hu).1] at hed
    rw [(hhigh w hw).1] at hle
    linarith only [hed, hle, hother]
  -- High-high deficits vanish; all of their deficit must be paid outside H.
  have hcross : (∑ i : V, ∑ j ∈ H, deficit A i j) = 4*(H.card : ℤ) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j ∈ H, rowDeficit A j := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold rowDeficit
        apply Finset.sum_congr rfl
        intro i hi
        exact deficit_symmetric A hs i j
      _ = ∑ _j ∈ H, (4 : ℤ) := Finset.sum_congr rfl (fun j hj => (hhigh j hj).2)
      _ = _ := by simp [mul_comm]
  have hpoint : ∀ i : V, (if i ∈ H then (4 : ℤ) else 0) +
      (∑ j ∈ H, deficit A i j) ≤ rowDeficit A i := by
    intro i
    by_cases hi : i ∈ H
    · rw [if_pos hi, (hhigh i hi).2]
      have hz' : (∑ j ∈ H, deficit A i j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact hzero i hi j hj
      rw [hz']
      omega
    · rw [if_neg hi, zero_add]
      unfold rowDeficit
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun j _ _ => hn i j)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib, hcross] at hsum
  have hfour : (∑ i : V, if i ∈ H then (4 : ℤ) else 0) = 4*(H.card : ℤ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hfour] at hsum
  omega

-- CASE V: once the shifted row identity forces adjacency from every high
-- vertex to both low vertices, the required weighted degree is impossible.
theorem case_V_core (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (L H : Finset V)
    (hL : L.card = 2) (hH : H.card = 3)
    (hl : ∀ i ∈ L, deg A i = 12 ∧ rowDeficit A i = 2)
    (hh : ∀ i ∈ H, deg A i = 14)
    (hm : ∀ i, i ∉ L → i ∉ H → deg A i = 13)
    (hX : (∑ i : V, shifted A i) = 1)
    (hadj : ∀ i ∈ H, ∀ j ∈ L, A i j = 1) : False := by
  classical
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
  have hdis : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 := (hl i hi).1
    have h2 := hh i hj
    omega
  have hterm : ∀ j : V, (if j ∈ H then (1 : ℤ) else 0) -
      (if j ∈ L ∧ j ≠ u then (1 : ℤ) else 0) ≤ A u j * shifted A j := by
    intro j
    by_cases hj : j ∈ L
    · have hj' : j ∉ H := fun h => Finset.disjoint_left.mp hdis hj h
      rw [if_neg hj', shifted, (hl j hj).1]
      by_cases hju : j = u
      · subst j
        simp [hz]
      · rw [if_pos ⟨hj,hju⟩]
        rcases hb u j with h | h <;> norm_num [h]
    · have hn : ¬(j ∈ L ∧ j ≠ u) := fun h => hj h.1
      rw [if_neg hn, sub_zero]
      by_cases hj' : j ∈ H
      · rw [if_pos hj', shifted, hh j hj', hs u j, hadj j hj' u hu]
        norm_num
      · rw [if_neg hj', shifted, hm j hj hj'] <;> norm_num
  have hle := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun j _ => hterm j)
  rw [Finset.sum_sub_distrib, sum_indicator H] at hle
  have herase : (∑ j : V, if j ∈ L ∧ j ≠ u then (1 : ℤ) else 0) =
      ((L.erase u).card : ℤ) := by
    rw [← sum_indicator (L.erase u)]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_erase, and_comm]
  rw [herase, Finset.card_erase_of_mem hu, hL, hH] at hle
  have hr := shifted_row_identity A u
  rw [hX, (hl u hu).2] at hr
  have hshift : shifted A u = -1 := by simp [shifted, (hl u hu).1]
  rw [hshift] at hr
  norm_num at hr hle
  linarith only [hr, hle]

-- In all three mixed cases, every vertex of degree 12 or 14 has a
-- red neighbor in the large class of clean degree-13 vertices.
theorem red_neighbor_in_large_class (A : V → V → ℤ)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (C : Finset V) (w : V) (hC : 22 ≤ C.card)
    (hd : 12 ≤ deg A w) : ∃ v ∈ C, A w v = 1 := by
  classical
  by_contra! h
  have hpoint : ∀ j : V, A w j ≤ (if j ∈ C then (0 : ℤ) else 1) := by
    intro j
    by_cases hj : j ∈ C
    · rw [if_pos hj]
      rcases hb w j with h0 | h1
      · omega
      · exact (h j hj h1).elim
    · rw [if_neg hj]
      rcases hb w j with h0 | h1 <;> omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun j _ => hpoint j)
  have hcomp : (∑ j : V, if j ∈ C then (0 : ℤ) else 1) = 29-(C.card : ℤ) := by
    calc
      _ = ∑ j : V, (1 - (if j ∈ C then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj' : j ∈ C <;> simp [hj']
      _ = _ := by rw [Finset.sum_sub_distrib, sum_indicator]; simp
  rw [hcomp] at hs
  change deg A w ≤ _ at hs
  omega

-- Cases II, III and V, with only their degree-class/cardinality data as
-- hypotheses in addition to the graph identities. The shifted row identity
-- derives the extra hypotheses of the core lemmas, rather than assuming them.
theorem mixed_cases (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (L H C : Finset V) (l : ℕ) (hlmax : l ≤ 2)
    (hL : L.card = l) (hH : H.card = 5-l) (hC : 22+l ≤ C.card)
    (hl : ∀ i ∈ L, deg A i = 12)
    (hh : ∀ i ∈ H, deg A i = 14)
    (hm : ∀ i, i ∉ L → i ∉ H → deg A i = 13)
    (hc : ∀ i ∈ C, deg A i = 13 ∧ rowDeficit A i = 0)
    (hbudget : (∑ i : V, rowDeficit A i) ≤ 24-4*(l : ℤ)) : False := by
  classical
  have hLH : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 := hl i hi
    have h2 := hh i hj
    omega
  have hshift : ∀ i : V, shifted A i =
      (if i ∈ H then (1 : ℤ) else 0) - (if i ∈ L then (1 : ℤ) else 0) := by
    intro i
    by_cases hi : i ∈ L
    · have hj : i ∉ H := fun h => Finset.disjoint_left.mp hLH hi h
      simp [shifted, hl i hi, hi, hj]
    · by_cases hj : i ∈ H
      · simp [shifted, hh i hj, hi, hj]
      · simp [shifted, hm i hi hj, hi, hj]
  have hX : (∑ i : V, shifted A i) = 5-2*(l : ℤ) := by
    simp only [hshift, Finset.sum_sub_distrib, sum_indicator, hL, hH]
    omega
  have hhighrow : ∀ w ∈ H, 4 ≤ rowDeficit A w := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := red_neighbor_in_large_class A hb C w (by omega) (by rw [hh w hw]; norm_num)
    have hvne : v ≠ w := by
      intro h
      subst v
      have h1 := (hc w hv).1
      have h2 := hh w hw
      omega
    have h := clean_commutator A hs hb hn v w hvne (hc v hv).2
    rw [hs v w, hvw, if_pos rfl, (hc v hv).1, hh w hw] at h
    norm_num at h
    have hu := (AE_bounds A hs hb hn v w).2
    omega
  have hlowrow : ∀ w ∈ L, 2 ≤ rowDeficit A w := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := red_neighbor_in_large_class A hb C w (by omega) (by rw [hl w hw])
    have hvne : v ≠ w := by
      intro h
      subst v
      have h1 := (hc w hv).1
      have h2 := hl w hw
      omega
    have h := clean_commutator A hs hb hn v w hvne (hc v hv).2
    rw [hs v w, hvw, if_pos rfl, (hc v hv).1, hl w hw] at h
    norm_num at h
    have hlo := (AE_bounds A hs hb hn v w).1
    omega
  have hnon : ∀ w j : V, 0 ≤ A w j * shifted A j + (if j ∈ L then (1 : ℤ) else 0) := by
    intro w j
    rw [hshift]
    by_cases hj : j ∈ L
    · have hj' : j ∉ H := fun h => Finset.disjoint_left.mp hLH hj h
      rcases hb w j with h | h <;> norm_num [hj,hj',h]
    · by_cases hj' : j ∈ H <;> rcases hb w j with h | h <;> norm_num [hj,hj',h]
  have heq : ∀ w ∈ H, rowDeficit A w = 4 ∧
      ∀ j : V, A w j * shifted A j + (if j ∈ L then (1 : ℤ) else 0) = 0 := by
    intro w hw
    have hrow := shifted_row_identity A w
    have hsw : shifted A w = 1 := by simp [shifted, hh w hw]
    rw [hX, hsw] at hrow
    norm_num at hrow
    have hsum : 0 ≤ ∑ j : V, (A w j * shifted A j + (if j ∈ L then (1 : ℤ) else 0)) :=
      Finset.sum_nonneg (fun j _ => hnon w j)
    have hform : (∑ j : V, (A w j * shifted A j + (if j ∈ L then (1 : ℤ) else 0))) =
        (∑ j : V, A w j * shifted A j) + (l : ℤ) := by
      rw [Finset.sum_add_distrib, sum_indicator, hL]
    rw [hform] at hsum
    have hge := hhighrow w hw
    have ht : rowDeficit A w = 4 := by omega
    have hzero : (∑ j : V, (A w j * shifted A j + (if j ∈ L then (1 : ℤ) else 0))) = 0 := by
      rw [hform]
      omega
    refine ⟨ht, ?_⟩
    intro j
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset V)) (fun k _ => hnon w k) (Finset.mem_univ j)
    rw [hzero] at hle
    exact le_antisymm hle (hnon w j)
  have hhigh : ∀ i ∈ H, deg A i = 14 ∧ rowDeficit A i = 4 :=
    fun i hi => ⟨hh i hi, (heq i hi).1⟩
  have hno : ∀ i ∈ H, ∀ j ∈ H, A i j = 0 := by
    intro i hi j hj
    have hj' : j ∉ L := fun h => Finset.disjoint_left.mp hLH h hj
    have he := (heq i hi).2 j
    have hsj : shifted A j = 1 := by simp [shifted, hh j hj]
    rw [hsj, if_neg hj'] at he
    omega
  have hadj : ∀ i ∈ H, ∀ j ∈ L, A i j = 1 := by
    intro i hi j hj
    have he := (heq i hi).2 j
    have hsj : shifted A j = -1 := by simp [shifted, hl j hj]
    rw [hsj, if_pos hj] at he
    omega
  by_cases hl2 : l = 2
  · rw [hl2] at hL hH hX hbudget
    norm_num at hH hX hbudget
    have hbase : ∀ i : V, 0 ≤ rowDeficit A i -
        (4*(if i ∈ H then (1 : ℤ) else 0)+2*(if i ∈ L then (1 : ℤ) else 0)) := by
      intro i
      by_cases hi : i ∈ L
      · have hj : i ∉ H := fun h => Finset.disjoint_left.mp hLH hi h
        have h := hlowrow i hi
        simp [hi,hj] <;> omega
      · by_cases hj : i ∈ H
        · have h := hhighrow i hj
          simp [hi,hj] <;> omega
        · have h := row_deficit_nonnegative A hn i
          simp [hi,hj] <;> omega
    have hsum : (∑ i : V, (rowDeficit A i -
        (4*(if i ∈ H then (1 : ℤ) else 0)+2*(if i ∈ L then (1 : ℤ) else 0)))) ≤ 0 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_indicator, hH, hL]
      norm_num at hbudget ⊢
      omega
    have hlow : ∀ i ∈ L, deg A i = 12 ∧ rowDeficit A i = 2 := by
      intro i hi
      have hj : i ∉ H := fun h => Finset.disjoint_left.mp hLH hi h
      have hle := Finset.single_le_sum (s := (Finset.univ : Finset V)) (fun k _ => hbase k) (Finset.mem_univ i)
      have hh' := hle.trans hsum
      have hlow := hlowrow i hi
      refine ⟨hl i hi, ?_⟩
      simp [hi,hj] at hh'
      omega
    exact case_V_core A hs hz hb L H hL (by simpa using hH) hlow hh hm (by simpa using hX) hadj
  · apply cases_II_III_core A hs hz hb hn C H hc hhigh hno
    · omega
    · omega
    · omega

-- CASE VI. Three degree-12 vertices, all dirty; the others have degree 13.
-- The proof uses a sharp second-moment bound instead of separate counts of
-- vertices with two and three low-degree neighbors.
theorem case_VI (A : V → V → ℤ)
    (hs : ∀ i j, A i j = A j i) (hz : ∀ i, A i i = 0)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hn : ∀ i j, 0 ≤ deficit A i j)
    (L : Finset V) (hL : L.card = 3)
    (hl : ∀ i ∈ L, deg A i = 12 ∧ rowDeficit A i ≠ 0)
    (hm : ∀ i, i ∉ L → deg A i = 13)
    (hbudget : (∑ i : V, rowDeficit A i) = 14)
    (hclean : ∃ i : V, deg A i = 13 ∧ rowDeficit A i = 0) : False := by
  classical
  let q : V → ℤ := fun i => ∑ j ∈ L, A i j
  have hshift : ∀ i : V, shifted A i = -(if i ∈ L then (1 : ℤ) else 0) := by
    intro i
    by_cases hi : i ∈ L
    · norm_num [shifted, (hl i hi).1, hi]
    · norm_num [shifted, hm i hi, hi]
  have hX : (∑ i : V, shifted A i) = -3 := by
    simp only [hshift, Finset.sum_neg_distrib, sum_indicator, hL]
    norm_num
  have hweighted : ∀ i : V, (∑ j : V, A i j * shifted A j) = -q i := by
    intro i
    simp only [hshift, mul_neg, Finset.sum_neg_distrib]
    congr 1
    unfold q
    have hfilter : (Finset.univ : Finset V).filter (fun j => j∈L) = L := by
      ext j; simp
    rw [← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hj' : j∈L <;> simp [hj']
  have hrow : ∀ i : V, rowDeficit A i = -2+2*q i := by
    intro i
    have h := shifted_row_identity A i
    rw [hX, hweighted i, hshift i] at h
    by_cases hi : i ∈ L <;> norm_num [hi] at h <;> linarith
  have hqlo : ∀ i : V, 1 ≤ q i := by
    intro i
    have h := row_deficit_nonnegative A hn i
    rw [hrow i] at h
    omega
  have hqhi : ∀ i : V, q i ≤ 3 := by
    intro i
    calc
      q i ≤ ∑ _j ∈ L, (1 : ℤ) := by
        unfold q
        apply Finset.sum_le_sum
        intro j hj
        rcases hb i j with h | h <;> omega
      _ = 3 := by simp [hL]
  have hqL : ∀ i ∈ L, q i = 2 ∧ rowDeficit A i = 2 := by
    intro i hi
    have hupper : q i ≤ 2 := by
      calc
        q i ≤ ∑ j ∈ L, (if j=i then (0 : ℤ) else 1) := by
          unfold q
          apply Finset.sum_le_sum
          intro j hj
          by_cases hji : j=i
          · subst j
            simp [hz]
          · rw [if_neg hji]
            rcases hb i j with h | h <;> omega
        _ = 2 := by
          have hf : (∑ j ∈ L, if j=i then (0 : ℤ) else 1) =
              ∑ j ∈ L, (1-(if j=i then (1 : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hj' : j=i <;> simp [hj']
          rw [hf, Finset.sum_sub_distrib]
          simp [hi,hL]
    have ht := dirty_minimum A hs hz hn i (hl i hi).2
    rw [hrow i] at ht
    have hqi : q i = 2 := by omega
    exact ⟨hqi, by rw [hrow i,hqi]; norm_num⟩
  have hcomplete : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → A i j = 1 := by
    intro i hi j hj hij
    have hnon : ∀ k ∈ L, 0 ≤ (if k=i then (0 : ℤ) else 1)-A i k := by
      intro k hk
      by_cases hki : k=i
      · subst k
        simp [hz]
      · rw [if_neg hki]
        rcases hb i k with h | h <;> omega
    have hsum : (∑ k ∈ L, ((if k=i then (0 : ℤ) else 1)-A i k)) = 0 := by
      rw [Finset.sum_sub_distrib]
      change (∑ k ∈ L, (if k=i then (0 : ℤ) else 1))-q i = 0
      rw [(hqL i hi).1]
      have hf : (∑ k ∈ L, if k=i then (0 : ℤ) else 1) =
          ∑ k ∈ L, (1-(if k=i then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k=i <;> simp [h]
      rw [hf, Finset.sum_sub_distrib]
      simp [hi,hL]
    have hle := Finset.single_le_sum hnon hj
    rw [hsum, if_neg (Ne.symm hij)] at hle
    rcases hb i j with h | h <;> omega
  have hqsum : (∑ i : V, q i) = 36 := by
    unfold q
    rw [Finset.sum_comm]
    calc
      _ = ∑ j ∈ L, deg A j := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold deg
        apply Finset.sum_congr rfl
        intro i hi
        exact hs i j
      _ = ∑ _j ∈ L, (12 : ℤ) := Finset.sum_congr rfl (fun j hj => (hl j hj).1)
      _ = 36 := by simp [hL]
  have hcommon_diag : ∀ i : V, common A i i = deg A i := by
    intro i
    unfold common deg
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j i]
    rcases hb i j with h | h <;> norm_num [h]
  have hcommon_sum : (∑ i ∈ L, ∑ j ∈ L, common A i j) = ∑ k : V, (q k)^2 := by
    unfold common
    calc
      _ = ∑ i ∈ L, ∑ k : V, ∑ j ∈ L, A i k * A k j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ k : V, ∑ i ∈ L, ∑ j ∈ L, A i k * A k j := by rw [Finset.sum_comm]
      _ = ∑ k : V, (q k)^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        have hcol : (∑ i ∈ L, A i k) = q k := by
          unfold q
          apply Finset.sum_congr rfl
          intro i hi
          exact hs i k
        change (∑ i ∈ L, A i k) * q k = (q k)^2
        rw [hcol]
        ring
  have hEform : ∀ i ∈ L, ∀ j ∈ L, deficit A i j =
      4-common A i j+(if i=j then 8 else 0) := by
    intro i hi j hj
    by_cases hij : i=j
    · subst j
      rw [deficit_diagonal A hs hz hb, hcommon_diag, (hl i hi).1]
      norm_num
    · unfold deficit
      rw [if_neg hij, hcomplete i hi j hj hij]
      simp [hij]
      <;> ring
  have hEtotal : (∑ i ∈ L, ∑ j ∈ L, deficit A i j) = 60-∑ k : V, (q k)^2 := by
    calc
      _ = ∑ i ∈ L, ∑ j ∈ L, (4-common A i j+(if i=j then 8 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_congr rfl (fun j hj => hEform i hi j hj)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hcommon_sum]
        have hdiag : (∑ i ∈ L, ∑ j ∈ L, if i=j then (8 : ℤ) else 0) = 24 := by
          calc
            _ = ∑ _i ∈ L, (8 : ℤ) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [eq_comm,hi]
            _ = 24 := by simp [hL]
        rw [hdiag]
        simp [hL] <;> ring
  have hLbudget : (∑ i ∈ L, rowDeficit A i) = 6 := by
    calc
      _ = ∑ _i ∈ L, (2 : ℤ) := Finset.sum_congr rfl (fun i hi => (hqL i hi).2)
      _ = 6 := by simp [hL]
  have hEbound : (∑ i ∈ L, ∑ j ∈ L, deficit A i j) ≤ 6 := by
    rw [← hLbudget]
    apply Finset.sum_le_sum
    intro i hi
    unfold rowDeficit
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hn i j)
  have hmoment : ∀ i : V, (q i)^2 ≤ 4*q i-3-(if i∈L then (1 : ℤ) else 0) := by
    intro i
    by_cases hi : i∈L
    · norm_num [hi,(hqL i hi).1]
    · rw [if_neg hi, sub_zero]
      nlinarith [mul_nonneg (show 0≤q i-1 by have h:=hqlo i; omega)
        (show 0≤3-q i by have h:=hqhi i; omega)]
  have hmoment_sum : (∑ i : V, (4*q i-3-(if i∈L then (1 : ℤ) else 0))) = 54 := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicator, hL, hqsum]
    norm_num
  have hmle := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => hmoment i)
  rw [hmoment_sum] at hmle
  have hmeq : (∑ i : V, (q i)^2) = 54 := by
    rw [hEtotal] at hEbound
    omega
  have hEeq : (∑ i ∈ L, ∑ j ∈ L, deficit A i j) = 6 := by rw [hEtotal,hmeq]; norm_num
  have hmid : ∀ i : V, i ∉ L → q i = 1 ∨ q i = 3 := by
    intro i hi
    have hnon : ∀ j : V, 0 ≤ 4*q j-3-(if j∈L then (1 : ℤ) else 0)-(q j)^2 := by
      intro j
      linarith only [hmoment j]
    have hzero : (∑ j : V, (4*q j-3-(if j∈L then (1 : ℤ) else 0)-(q j)^2)) = 0 := by
      rw [Finset.sum_sub_distrib, hmoment_sum, hmeq]
      norm_num
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset V)) (fun j _ => hnon j) (Finset.mem_univ i)
    rw [hzero, if_neg hi] at hle
    have hlo := hqlo i
    have hhi := hqhi i
    have hcases : q i = 1 ∨ q i = 2 ∨ q i = 3 := by omega
    rcases hcases with h | h | h
    · exact Or.inl h
    · norm_num [h] at hle
    · exact Or.inr h
  have hcross : ∀ i ∈ L, ∀ j : V, j ∉ L → deficit A i j = 0 := by
    intro i hi j hj
    have hnon : ∀ k ∈ L, 0 ≤ rowDeficit A k-∑ w ∈ L, deficit A k w := by
      intro k hk
      have h : (∑ w ∈ L, deficit A k w) ≤ rowDeficit A k := by
        unfold rowDeficit
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => hn k w)
      omega
    have hzero : (∑ k ∈ L, (rowDeficit A k-∑ w ∈ L, deficit A k w)) = 0 := by
      rw [Finset.sum_sub_distrib,hLbudget,hEeq]
      norm_num
    have hle := Finset.single_le_sum hnon hi
    rw [hzero] at hle
    have hsub : (∑ w ∈ insert j L, deficit A i w) ≤ rowDeficit A i := by
      unfold rowDeficit
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => hn i w)
    rw [Finset.sum_insert hj] at hsub
    have hnj := hn i j
    omega
  let T : Finset V := Finset.univ.filter (fun i => i∉L ∧ q i=3)
  have hTmem : ∀ i : V, i∈T ↔ i∉L ∧ q i=3 := by intro i; simp [T]
  have htform : ∀ i : V, rowDeficit A i =
      2*(if i∈L then (1 : ℤ) else 0)+4*(if i∈T then (1 : ℤ) else 0) := by
    intro i
    by_cases hi : i∈L
    · have hj : i∉T := fun h => ((hTmem i).mp h).1 hi
      simp [hi,hj,(hqL i hi).2]
    · rcases hmid i hi with h | h
      · have hj : i∉T := by intro hj; have hh := ((hTmem i).mp hj).2; omega
        norm_num [hi,hj,hrow i,h]
      · have hj : i∈T := (hTmem i).mpr ⟨hi,h⟩
        norm_num [hi,hj,hrow i,h]
  have hTcard : T.card=2 := by
    have ht := hbudget
    simp only [htform, Finset.sum_add_distrib, ← Finset.mul_sum, sum_indicator, hL] at ht
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0<T.card)
  have herase : (T.erase w).card=1 := by rw [Finset.card_erase_of_mem hw,hTcard]
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0<(T.erase w).card)
  have huT := (Finset.mem_erase.mp hu).2
  have huw := (Finset.mem_erase.mp hu).1
  have hTout : ∀ j∈T, j≠w → j=u := by
    intro j hj hjw
    have hj' : j∈T.erase w := Finset.mem_erase.mpr ⟨hjw,hj⟩
    have hset : T.erase w = {u} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.singleton_subset_iff.mpr hu
      · simp [herase]
    simpa [hset] using hj'
  have hwL : w∉L := ((hTmem w).mp hw).1
  have hwu : ∀ j : V, j≠u → deficit A j w=0 := by
    intro j hj
    by_cases hjw : j=w
    · subst j
      exact deficit_diagonal A hs hz hb w
    · by_cases hjL : j∈L
      · exact hcross j hjL w hwL
      · have hjT : j∉T := fun h => hj (hTout j h hjw)
        exact clean_deficit_zero A hn j (by simp [htform j,hjL,hjT]) w
  have huwE : deficit A u w = 4 := by
    have ht : rowDeficit A w = 4 := by simp [htform w,hwL,hw]
    have hsum : rowDeficit A w = ∑ j : V, if j=u then deficit A u w else 0 := by
      unfold rowDeficit
      apply Finset.sum_congr rfl
      intro j hj
      rw [deficit_symmetric A hs w j]
      by_cases h : j=u
      · subst j; simp
      · simp [h,hwu j h]
    rw [ht] at hsum
    simpa using hsum.symm
  obtain ⟨v,hvd,hvc⟩ := hclean
  have hvne : v≠w := by
    intro h
    subst v
    have ht : rowDeficit A w = 4 := by simp [htform w,hwL,hw]
    omega
  have hAE : AE A v w = 4*A v u := by
    unfold AE
    calc
      _ = ∑ j : V, if j=u then A v u*4 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j=u
        · subst j; simp [huwE]
        · simp [h,hwu j h]
      _ = _ := by simp [mul_comm]
  have h := clean_commutator A hs hb hn v w hvne hvc
  rw [hAE, hvd, hm w hwL, htform w] at h
  simp [hwL,hw] at h
  rcases hb v u with h0 | h1
  · norm_num [h0] at h
  · norm_num [h1] at h

-- CASE IV: an integer replacement for the irrational-eigenvalue argument.
-- The cycle and matrix steps must still supply v,u with these properties.
def ip (S : Finset V) (v u : V → ℤ) : ℤ := ∑ i ∈ S, v i*u i

def mv (S : Finset V) (H : V → V → ℤ) (v : V → ℤ) (i : V) : ℤ :=
  ∑ j ∈ S, H i j*v j

def qform (S : Finset V) (H : V → V → ℤ) (v : V → ℤ) : ℤ :=
  ip S v (mv S H v) + 4*ip S v v

theorem ip_sym (S : Finset V) (v u : V → ℤ) : ip S v u = ip S u v := by
  unfold ip
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem ip_act_sym (S : Finset V) (H : V → V → ℤ)
    (hs : ∀ i j, H i j=H j i) (v u : V → ℤ) :
    ip S v (mv S H u) = ip S (mv S H v) u := by
  unfold ip mv
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j i]
  ring

-- H+4I is positive semidefinite, proved by sums of squares, not by spectra.
theorem qform_nonnegative (S : Finset V) (H : V → V → ℤ)
    (hs : ∀ i j, H i j=H j i)
    (hn : ∀ i j, 0≤H i j)
    (hdeg : ∀ i∈S, (∑ j∈S, H i j)=4) (v : V → ℤ) :
    0≤qform S H v := by
  have h1 : (∑ i∈S, ∑ j∈S, H i j*(v i)^2) = 4*ip S v v := by
    unfold ip
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_mul,hdeg i hi]
    ring
  have h2 : (∑ i∈S, ∑ j∈S, H i j*(v j)^2) = 4*ip S v v := by
    rw [← h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j i]
  have h3 : (∑ i∈S, ∑ j∈S, H i j*(v i*v j)) = ip S v (mv S H v) := by
    unfold ip mv
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h : 0≤∑ i∈S, ∑ j∈S, H i j*(v i+v j)^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hn i j) (sq_nonneg _)))
  have heq : (∑ i∈S, ∑ j∈S, H i j*(v i+v j)^2) =
      (∑ i∈S, ∑ j∈S, H i j*(v i)^2) +
      (∑ i∈S, ∑ j∈S, H i j*(v j)^2) +
      2*(∑ i∈S, ∑ j∈S, H i j*(v i*v j)) := by
    calc
      _ = ∑ i∈S, ∑ j∈S, (H i j*(v i)^2+H i j*(v j)^2+2*(H i j*(v i*v j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
  rw [heq,h1,h2,h3] at h
  unfold qform
  linarith

theorem ip_combo (S : Finset V) (a b c d : V → ℤ) (x y : ℤ) :
    ip S (fun i=>x*a i+y*b i) (fun i=>x*c i+y*d i) =
    x^2*ip S a c+x*y*ip S a d+x*y*ip S b c+y^2*ip S b d := by
  unfold ip
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem mv_combo (S : Finset V) (H : V → V → ℤ) (a b : V → ℤ) (x y : ℤ) :
    mv S H (fun i=>x*a i+y*b i) = fun i=>x*mv S H a i+y*mv S H b i := by
  funext i
  unfold mv
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem qform_combo (S : Finset V) (H : V → V → ℤ)
    (hs : ∀ i j,H i j=H j i) (v u : V → ℤ) (x y : ℤ) :
    qform S H (fun i=>x*v i+y*u i) =
    x^2*qform S H v+2*x*y*(ip S v (mv S H u)+4*ip S v u)+y^2*qform S H u := by
  unfold qform
  rw [mv_combo,ip_combo,ip_combo]
  have hcross : ip S u (mv S H v)=ip S v (mv S H u) := by
    rw [ip_act_sym S H hs u v,ip_sym S (mv S H u) v]
  rw [hcross,ip_sym S u v]
  ring

theorem no_integer_root_41 (k : ℤ) : k^2+3*k-8≠0 := by
  intro hk
  by_cases h₁ : k≤-5
  · nlinarith [mul_nonneg (show 0≤-k-5 by omega) (show 0≤-k-2 by omega)]
  · by_cases h₂ : 2≤k
    · nlinarith [mul_nonneg (show 0≤k-2 by omega) (show 0≤k+5 by omega)]
    · have hlo : -4≤k := by omega
      have hhi : k≤1 := by omega
      interval_cases k <;> norm_num at hk

-- The hypotheses are exactly the polynomial relation and a unit entry of an
-- integer alternating cycle vector. No rational eigenvalue lemma is assumed.
theorem case_IV_integer_core (S : Finset V) (H : V → V → ℤ)
    (hs : ∀ i j,H i j=H j i) (hn : ∀ i j,0≤H i j)
    (hdeg : ∀ i∈S,(∑ j∈S,H i j)=4)
    (v u : V → ℤ)
    (hu : ∀ i∈S, mv S H v i=u i)
    (hpoly : ∀ i∈S,mv S H u i=8*v i-3*u i)
    (hunit : ∃ i∈S,v i=1) : False := by
  obtain ⟨i,hi,hvi⟩ := hunit
  let a := ip S v v
  let b := ip S v u
  let c := ip S u u
  have ha : 0<a := by
    have hle := Finset.single_le_sum (s := S)
      (f := fun j => v j*v j) (fun j _ => mul_self_nonneg (v j)) hi
    change v i*v i≤a at hle
    rw [hvi] at hle
    omega
  have hvv : ip S v (mv S H v)=b := by
    unfold b ip
    apply Finset.sum_congr rfl
    intro j hj
    rw [hu j hj]
  have huv : ip S u (mv S H v)=c := by
    unfold c ip
    apply Finset.sum_congr rfl
    intro j hj
    rw [hu j hj]
  have hvu : ip S v (mv S H u)=8*a-3*b := by
    unfold a b ip
    calc
      _ = ∑ j∈S, v j*(8*v j-3*u j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpoly j hj]
      _ = _ := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have huu : ip S u (mv S H u)=8*b-3*c := by
    unfold b c ip
    calc
      _ = ∑ j∈S, u j*(8*v j-3*u j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpoly j hj]
      _ = _ := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hcross : ip S v (mv S H u)=c := by
    rw [ip_act_sym S H hs v u,ip_sym S (mv S H v) u,huv]
  have hc : c=8*a-3*b := hcross.symm.trans hvu
  let p := b+4*a
  let r := c+4*b
  let t := 8*b+c
  have hp : qform S H v=p := by unfold qform p; rw [hvv] <;> rfl
  have ht : qform S H u=t := by unfold qform t; rw [huu]; change 8*b-3*c+4*c=8*b+c; ring
  have hr : ip S v (mv S H u)+4*ip S v u=r := by unfold r; rw [hcross] <;> rfl
  have hp0 := qform_nonnegative S H hs hn hdeg v
  have ht0 := qform_nonnegative S H hs hn hdeg u
  rw [hp] at hp0
  rw [ht] at ht0
  have hp_pos : 0<p := by
    dsimp [p] at hp0 ⊢
    dsimp [t] at ht0
    omega
  have hcombo := qform_combo S H hs v u r (-p)
  rw [hp,ht,hr] at hcombo
  have hpos := qform_nonnegative S H hs hn hdeg (fun j=>r*v j+(-p)*u j)
  rw [hcombo] at hpos
  have hprod : 0≤p*(p*t-r^2) := by nlinarith only [hpos]
  have hdet : 0≤p*t-r^2 := by
    by_contra! h
    have hh := mul_neg_of_pos_of_neg hp_pos h
    linarith only [hh,hprod]
  have hdeteq : p*t-r^2 = -4*(a*c-b^2) := by
    dsimp [p,t,r]
    rw [hc]
    ring
  rw [hdeteq] at hdet
  have hsq : (∑ j∈S,(a*u j-b*v j)^2)=a*(a*c-b^2) := by
    have haform : (∑ j∈S, v j*v j)=a := rfl
    have hbform : (∑ j∈S, v j*u j)=b := rfl
    have hcform : (∑ j∈S, u j*u j)=c := rfl
    calc
      _ = ∑ j∈S, (a^2*(u j*u j)-(2*a*b)*(v j*u j)+b^2*(v j*v j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = a^2*c-2*a*b*b+b^2*a := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          haform,hbform,hcform]
      _ = _ := by ring
  have hnon : 0≤∑ j∈S,(a*u j-b*v j)^2 := Finset.sum_nonneg (fun j _=>sq_nonneg _)
  rw [hsq] at hnon
  have hgram : a*c-b^2=0 := by
    by_contra hne
    have hle : a*c-b^2≤0 := by linarith only [hdet]
    have hneg : a*c-b^2<0 := lt_of_le_of_ne hle hne
    have hh := mul_neg_of_pos_of_neg ha hneg
    linarith only [hh,hnon]
  have hzero : (∑ j∈S,(a*u j-b*v j)^2)=0 := by rw [hsq,hgram,mul_zero]
  have hle := Finset.single_le_sum (s := S) (fun j _=>sq_nonneg (a*u j-b*v j)) hi
  rw [hzero,hvi,mul_one] at hle
  have hz : (a*u i-b)^2=0 := le_antisymm hle (sq_nonneg _)
  have hz' : (a*u i-b)*(a*u i-b)=0 := by simpa [pow_two] using hz
  have hlin : a*u i-b=0 := (mul_eq_zero.mp hz').elim id id
  have hb : b=a*u i := by omega
  have heq : a^2*((u i)^2+3*u i-8)=0 := by
    calc
      _ = b^2-a*c := by rw [hc,hb]; ring
      _ = 0 := by linarith only [hgram]
  rcases mul_eq_zero.mp heq with he | he
  · have hapos : 0<a^2 := pow_pos ha 2
    omega
  · exact no_integer_root_41 (u i) he

-- Two fixed-point-free involutions, one preserving and one reversing an
-- integer binary label, admit a nonzero sign vector negated by both.
-- This is an elementary alternative to formalizing all cycle components.
theorem alternating_sign {α : Type} (P Q : Equiv.Perm α) (a : α→ℤ)
    (hP : ∀ x, P (P x)=x) (hQ : ∀ x, Q (Q x)=x)
    (hPf : ∀ x, P x≠x)
    (hPa : ∀ x, a (P x)=a x) (hQa : ∀ x, a (Q x)=1-a x)
    (w : α) : ∃ v : α→ℤ, v w=1 ∧
      (∀ x, v (P x) = -v x) ∧ (∀ x,v (Q x) = -v x) := by
  classical
  let T : Equiv.Perm α := P*Q
  have hPP : P*P=1 := by ext x; exact hP x
  have hQQ : Q*Q=1 := by ext x; exact hQ x
  have hPinv : P⁻¹=P := by
    ext x
    apply P.injective
    change P (P.symm x)=P (P x)
    rw [P.apply_symm_apply,hP]
  have hQinv : Q⁻¹=Q := by
    ext x
    apply Q.injective
    change Q (Q.symm x)=Q (Q x)
    rw [Q.apply_symm_apply,hQ]
  have hTinv : T⁻¹=Q*P := by simp [T,mul_inv_rev,hPinv,hQinv]
  have hconj : P*T*P⁻¹=T⁻¹ := by
    rw [hPinv,hTinv]
    change P*(P*Q)*P=Q*P
    rw [← mul_assoc P P Q,hPP,one_mul]
  have hcomm (n : ℤ) : P*T^n=T^(-n)*P := by
    calc
      _ = (P*T^n*P⁻¹)*P := by group
      _ = (P*T*P⁻¹)^n*P := by rw [conj_zpow]
      _ = _ := by rw [hconj,inv_zpow,zpow_neg]
  have hflip (x : α) : a (T x)=1-a x := by simp [T,Equiv.Perm.mul_apply,hPa,hQa]
  have hTin (x : α) : T (T⁻¹ x)=x := by
    rw [← Equiv.Perm.mul_apply,mul_inv_cancel] <;> rfl
  have hflipInv (x : α) : a (T⁻¹ x)=1-a x := by
    have h := hflip (T⁻¹ x)
    rw [hTin] at h
    omega
  have hcol (n : ℤ) : ∀ x : α, a ((T^n) x)=if n%2=0 then a x else 1-a x := by
    refine Int.induction_on n ?_ ?_ ?_
    · intro x
      simp
    · intro k ih x
      rw [zpow_add,zpow_one,Equiv.Perm.mul_apply,ih,hflip]
      by_cases hk : (k:ℤ)%2=0
      · have hh : ((k:ℤ)+1)%2≠0 := by omega
        simp [hk,hh]
      · have hh : ((k:ℤ)+1)%2=0 := by omega
        simp [hk,hh] <;> ring
    · intro k ih x
      rw [sub_eq_add_neg,zpow_add,show T^(-1:ℤ)=T⁻¹ by simp,Equiv.Perm.mul_apply,ih,hflipInv]
      split_ifs <;> omega
  have hno (x : α) : ¬∃ n : ℤ, P x=(T^n) x := by
    rintro ⟨n,hn⟩
    have hc := hcol n x
    rw [← hn,hPa] at hc
    have heven : n%2=0 := by
      by_contra hn'
      rw [if_neg hn'] at hc
      omega
    let k : ℤ := n/2
    have hk : n=2*k := by dsimp [k]; omega
    have hc' := congrArg (fun g : Equiv.Perm α => g x) (hcomm k)
    simp only [Equiv.Perm.mul_apply] at hc'
    rw [hn] at hc'
    have hp : (T^(-k)) ((T^n) x)=(T^k) x := by
      rw [← Equiv.Perm.mul_apply,← zpow_add,show -k+n=k by omega]
    exact hPf ((T^k) x) (hc'.trans hp)
  let O : α→Prop := fun x => ∃ n : ℤ, x=(T^n) w
  have hO_T (x : α) : O (T x) ↔ O x := by
    constructor
    · rintro ⟨n,hn⟩
      refine ⟨n-1,?_⟩
      calc
        x = (T^(-1:ℤ)) (T x) := by
          rw [zpow_neg,zpow_one,← Equiv.Perm.mul_apply,inv_mul_cancel] <;> rfl
        _ = (T^(-1:ℤ)) ((T^n) w) := congrArg (fun y=>(T^(-1:ℤ)) y) hn
        _ = _ := by rw [← Equiv.Perm.mul_apply,← zpow_add,show -1+n=n-1 by ring]
    · rintro ⟨n,hn⟩
      refine ⟨1+n,?_⟩
      calc
        T x = T ((T^n) w) := congrArg T hn
        _ = _ := by
          change (T * T^n) w = (T^(1+n)) w
          rw [zpow_add,zpow_one]
  have hO_inv (x : α) : O (T⁻¹ x) ↔ O x := by
    have h := hO_T (T⁻¹ x)
    rw [hTin] at h
    exact h.symm
  have hdis (x : α) (hx : O x) : ¬O (P x) := by
    obtain ⟨n,hn⟩ := hx
    rintro ⟨m,hm⟩
    apply hno x
    refine ⟨m-n,?_⟩
    rw [hm,hn,← Equiv.Perm.mul_apply,← zpow_add,show m-n+n=m by ring]
  let v : α→ℤ := fun x => if O x then 1 else if O (P x) then -1 else 0
  have hvP (x : α) : v (P x) = -v x := by
    by_cases hx : O x
    · have hp := hdis x hx
      simp [v,hx,hp,hP]
    · by_cases hp : O (P x) <;> simp [v,hx,hp,hP]
  have hPT (x : α) : P (T x)=T⁻¹ (P x) := by
    have h := congrArg (fun g : Equiv.Perm α => g x) (hcomm 1)
    simpa only [zpow_one,zpow_neg,Equiv.Perm.mul_apply] using h
  have hvT (x : α) : v (T x)=v x := by
    simp only [v]
    rw [hO_T,hPT,hO_inv]
  have hQform (x : α) : Q x=P (T x) := by
    simp [T,Equiv.Perm.mul_apply,hP]
  have hw : O w := ⟨0,by simp⟩
  refine ⟨v,by simp [v,hw],hvP,?_⟩
  intro x
  rw [hQform,hvP,hvT]

end Book59CaseElimination



namespace Book59CaseElimination
open scoped BigOperators
open BookRamseyUpper Book59Soundness
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Restrict a finite sum to its support.
theorem sum_on_support (S : Finset V) (f : V→ℤ)
    (hf : ∀ j, j∉S → f j=0) : (∑ j : V, f j)=∑ j∈S,f j := by
  have hfilter : (Finset.univ : Finset V).filter (fun j=>j∈S)=S := by ext j; simp
  calc
    _ = ∑ j : V, if j∈S then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j∈S <;> simp [h,hf]
    _ = _ := by rw [← Finset.sum_filter,hfilter]

-- Nonnegative integer weights summing to one have a unique unit entry.
theorem unit_weight (S : Finset V) (f : V→ℤ)
    (hn : ∀ j∈S,0≤f j) (hs : (∑ j∈S,f j)=1) :
    ∃ j∈S, f j=1 ∧ ∀ k∈S,k≠j → f k=0 := by
  have he : ∃ j∈S, 0<f j := by
    by_contra! h
    have hh : (∑ j∈S,f j)≤0 := Finset.sum_nonpos (fun j hj=>h j hj)
    omega
  obtain ⟨j,hj,hjp⟩ := he
  have hle := Finset.single_le_sum hn hj
  rw [hs] at hle
  have hval : f j=1 := by omega
  refine ⟨j,hj,hval,?_⟩
  intro k hk hkj
  have hsub : insert k ({j} : Finset V) ⊆ S := by
    intro x hx
    simp at hx
    rcases hx with h | h
    · simpa [h] using hk
    · simpa [h] using hj
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _=>hn x hx)
  have hknot : k∉({j} : Finset V) := by simp [hkj]
  rw [Finset.sum_insert hknot,Finset.sum_singleton,hs,hval] at hsum
  have hh := hn k hk
  omega

-- A symmetric deficit matrix with row sum two and a binary vector selecting
-- exactly one unit in every row has an integer -2 eigenvector with a unit entry.
theorem deficit_alternating_vector (S : Finset V) (E : V→V→ℤ) (a : V→ℤ)
    (hs : ∀ i j,E i j=E j i) (hz : ∀ i,E i i=0)
    (hn : ∀ i j,0≤E i j) (ha : ∀ i,a i=0∨a i=1)
    (hrows : ∀ i∈S,(∑ j∈S,E i j)=2)
    (hselect : ∀ i∈S,(∑ j∈S,a j*E i j)=1)
    (hS : S.Nonempty) :
    ∃ v : V→ℤ, (∃ i∈S,v i=1) ∧ (∀ i∈S,mv S E v i = -2*v i) := by
  classical
  have split_row (i : V) (hi : i∈S) (b : ℤ) (hb : b=0∨b=1) :
      ∃ j∈S, a j=b ∧ E i j=1 ∧ ∀ k∈S,a k=b → k≠j → E i k=0 := by
    let f : V→ℤ := fun j=>if a j=b then E i j else 0
    have hf : ∀ j∈S,0≤f j := by
      intro j hj
      by_cases h : a j=b <;> simp [f,h,hn]
    have hsum : (∑ j∈S,f j)=1 := by
      rcases hb with h | h
      · subst b
        calc
          _ = ∑ j∈S,(E i j-a j*E i j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rcases ha j with h | h <;> simp [f,h]
          _ = _ := by rw [Finset.sum_sub_distrib,hrows i hi,hselect i hi] <;> norm_num
      · subst b
        calc
          _ = ∑ j∈S,a j*E i j := by
            apply Finset.sum_congr rfl
            intro j hj
            rcases ha j with h | h <;> simp [f,h]
          _ = 1 := hselect i hi
    obtain ⟨j,hj,hval,hu⟩ := unit_weight S f hf hsum
    have hlabel : a j=b := by
      by_contra h
      simp [f,h] at hval
    refine ⟨j,hj,hlabel,by simpa [f,hlabel] using hval,?_⟩
    intro k hk hl hkj
    simpa [f,hl] using hu k hk hkj
  let W := {i : V // i∈S}
  have hSame : ∀ w : W, ∃ p : W, a p.val=a w.val ∧ E w.val p.val=1 ∧
      ∀ z : W, a z.val=a w.val → z≠p → E w.val z.val=0 := by
    intro w
    obtain ⟨j,hj,hlabel,hval,hu⟩ := split_row w.val w.property (a w.val) (ha w.val)
    refine ⟨⟨j,hj⟩,hlabel,hval,?_⟩
    intro z hl hne
    exact hu z.val z.property hl (fun h=>hne (Subtype.ext h))
  have hOpp : ∀ w : W, ∃ p : W, a p.val=1-a w.val ∧ E w.val p.val=1 ∧
      ∀ z : W, a z.val=1-a w.val → z≠p → E w.val z.val=0 := by
    intro w
    have hb : 1-a w.val=0∨1-a w.val=1 := by rcases ha w.val with h | h <;> omega
    obtain ⟨j,hj,hlabel,hval,hu⟩ := split_row w.val w.property (1-a w.val) hb
    refine ⟨⟨j,hj⟩,hlabel,hval,?_⟩
    intro z hl hne
    exact hu z.val z.property hl (fun h=>hne (Subtype.ext h))
  choose P hP using hSame
  choose Q hQ using hOpp
  have hPInv : ∀ w : W,P (P w)=w := by
    intro w
    by_contra hne
    have hh := (hP (P w)).2.2 w (hP w).1.symm (Ne.symm hne)
    have hp := (hP w).2.1
    rw [hs] at hh
    omega
  have hQInv : ∀ w : W,Q (Q w)=w := by
    intro w
    by_contra hne
    have hlabel : a w.val=1-a (Q w).val := by have h:=(hQ w).1; omega
    have hh := (hQ (Q w)).2.2 w hlabel (Ne.symm hne)
    have hp := (hQ w).2.1
    rw [hs] at hh
    omega
  have hPf : ∀ w : W,P w≠w := by
    intro w h
    have hp := (hP w).2.1
    rw [h,hz] at hp
    omega
  have hPQ : ∀ w : W,P w≠Q w := by
    intro w h
    have hp := (hP w).1
    have hq := (hQ w).1
    rw [h] at hp
    omega
  let pe : Equiv.Perm W := ⟨P,P,hPInv,hPInv⟩
  let qe : Equiv.Perm W := ⟨Q,Q,hQInv,hQInv⟩
  obtain ⟨i,hi⟩ := hS
  obtain ⟨v0,hunit,hvp,hvq⟩ := alternating_sign pe qe (fun w=>a w.val)
    hPInv hQInv hPf (fun w=>(hP w).1) (fun w=>(hQ w).1) ⟨i,hi⟩
  let v : V→ℤ := fun j=>if h : j∈S then v0 ⟨j,h⟩ else 0
  have hv (w : W) : v w.val=v0 w := by simp [v,w.property]
  refine ⟨v,⟨i,hi,by simpa [v,hi] using hunit⟩,?_⟩
  intro j hj
  let w : W := ⟨j,hj⟩
  have hneq : (P w).val≠(Q w).val := fun h=>hPQ w (Subtype.ext h)
  have hform : ∀ k∈S,E j k=(if k=(P w).val then (1 : ℤ) else 0)+
      (if k=(Q w).val then (1 : ℤ) else 0) := by
    intro k hk
    by_cases hp : k=(P w).val
    · subst k
      have he : E j (P w).val=1 := (hP w).2.1
      simp [he,hneq]
    · by_cases hq : k=(Q w).val
      · subst k
        have he : E j (Q w).val=1 := (hQ w).2.1
        simp [he,Ne.symm hneq]
      · have hb : a k=a w.val∨a k=1-a w.val := by
          rcases ha k with h | h <;> rcases ha w.val with h' | h' <;> omega
        rcases hb with h | h
        · have he := (hP w).2.2 ⟨k,hk⟩ h (fun hh=>hp (congrArg Subtype.val hh))
          simpa [w,hp,hq] using he
        · have he := (hQ w).2.2 ⟨k,hk⟩ h (fun hh=>hq (congrArg Subtype.val hh))
          simpa [w,hp,hq] using he
  calc
    mv S E v j = ∑ k∈S, ((if k=(P w).val then (1 : ℤ) else 0)+
        (if k=(Q w).val then (1 : ℤ) else 0))*v k := by
      unfold mv
      apply Finset.sum_congr rfl
      intro k hk
      rw [hform k hk]
    _ = v (P w).val+v (Q w).val := by
      simp [add_mul,Finset.sum_add_distrib,ite_mul,(P w).property,(Q w).property]
    _ = -2*v j := by
      rw [hv (P w),hv (Q w)]
      have hp : v0 (P w) = -v0 w := hvp w
      have hq : v0 (Q w) = -v0 w := hvq w
      rw [hp,hq,← hv w]
      change -v j + -v j = -2*v j
      ring

-- CASE IV in terms of the actual graph: exactly one degree-12 vertex (clean),
-- all other degrees 13, and both a clean degree-13 vertex and a dirty vertex.
-- All conditions are direct consequences of the surviving histogram row.
theorem case_IV (A : V → V → ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1)
    (hn : ∀ i j,0≤deficit A i j)
    (o : V) (ho : deg A o=12 ∧ rowDeficit A o=0)
    (hm : ∀ i,i≠o → deg A i=13)
    (hdirty : ∃ i,rowDeficit A i≠0)
    (hclean : ∃ i,deg A i=13∧rowDeficit A i=0) : False := by
  classical
  let S : Finset V := Finset.univ.filter (fun i=>rowDeficit A i≠0)
  have hSmem (i : V) : i∈S ↔ rowDeficit A i≠0 := by simp [S]
  have hSo : o∉S := by simp [hSmem,ho.2]
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hdirty
    exact ⟨i,(hSmem i).mpr hi⟩
  have hshift (i : V) : shifted A i=-(if i=o then (1 : ℤ) else 0) := by
    by_cases hi : i=o
    · subst i; norm_num [shifted,ho.1]
    · simp [shifted,hi,hm i hi]
  have hX : (∑ i : V,shifted A i)= -1 := by simp [hshift,Finset.sum_neg_distrib]
  have hweighted (i : V) : (∑ j : V,A i j*shifted A j) = -A i o := by
    calc
      _ = ∑ j : V,if j=o then -A i o else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j=o
        · subst j; simp [hshift]
        · simp [hshift,h]
      _ = _ := by simp
  have hrow (i : V) (hi : i≠o) : rowDeficit A i=2*A i o := by
    have h := shifted_row_identity A i
    rw [hX,hweighted,hshift] at h
    simp [hi] at h
    linarith
  have hSdata : ∀ i∈S, i≠o ∧ deg A i=13 ∧ rowDeficit A i=2 ∧ A i o=1 := by
    intro i hi
    have hio : i≠o := by intro h; subst i; exact hSo hi
    have h := hrow i hio
    have hd := (hSmem i).mp hi
    rcases hb i o with h0 | h1
    · rw [h0] at h
      exact (hd (by omega)).elim
    · exact ⟨hio,hm i hio,by omega,h1⟩
  have hAorow (j : V) : A o j=if j∈S then 1 else 0 := by
    by_cases hj : j∈S
    · rw [if_pos hj,hs o j]
      exact (hSdata j hj).2.2.2
    · rw [if_neg hj]
      by_cases hjo : j=o
      · subst j; exact hz o
      · have hclean' : rowDeficit A j=0 := by by_contra h; exact hj ((hSmem j).mpr h)
        have h := hrow j hjo
        rw [hclean',hs j o] at h
        omega
  have hEout (i j : V) (hj : j∉S) : deficit A i j=0 := by
    have hj' : rowDeficit A j=0 := by by_contra h; exact hj ((hSmem j).mpr h)
    rw [deficit_symmetric A hs i j]
    exact clean_deficit_zero A hn j hj' i
  have hErow : ∀ i∈S,(∑ j∈S,deficit A i j)=2 := by
    intro i hi
    rw [← sum_on_support S (deficit A i) (hEout i)]
    exact (hSdata i hi).2.2.1
  have hHrow : ∀ i∈S,(∑ j∈S,A i j)=4 := by
    intro i hi
    have hdata := hSdata i hi
    have hE := clean_deficit_zero A hn o ho.2 i
    have hne : o≠i := Ne.symm hdata.1
    have ha : A o i=1 := by simp [hAorow,hi]
    have hcommon : common A o i=4 := by
      unfold deficit at hE
      rw [if_neg hne,ha] at hE
      linarith
    have heq : common A o i=∑ j∈S,A i j := by
      unfold common
      calc
        _ = ∑ j : V,if j∈S then A i j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hAorow,hs j i]
          by_cases h : j∈S <;> simp [h]
        _ = _ := by
          have hfilter : (Finset.univ : Finset V).filter (fun j=>j∈S)=S := by ext j; simp
          rw [← Finset.sum_filter,hfilter]
    rw [← heq,hcommon]
  have hAEclean : ∀ c, deg A c=13 → rowDeficit A c=0 → ∀ i∈S,
      (∑ j∈S,A c j*deficit A j i)=1 := by
    intro c hcd hct i hi
    have hdata := hSdata i hi
    have hne : c≠i := by
      intro h
      subst c
      omega
    have h := clean_commutator A hs hb hn c i hne hct
    rw [hcd,hdata.2.1,hdata.2.2.1] at h
    simp at h
    have hAE : AE A c i=1 := by omega
    unfold AE at hAE
    rw [sum_on_support S (fun j=>A c j*deficit A j i)] at hAE
    · exact hAE
    · intro j hj
      rw [deficit_symmetric A hs j i,hEout i j hj,mul_zero]
  obtain ⟨c,hcd,hct⟩ := hclean
  have hselect : ∀ i∈S,(∑ j∈S,A c j*deficit A i j)=1 := by
    intro i hi
    calc
      _ = ∑ j∈S,A c j*deficit A j i := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [deficit_symmetric A hs i j]
      _ = _ := hAEclean c hcd hct i hi
  obtain ⟨v,hunit,hEv⟩ := deficit_alternating_vector S (deficit A) (A c)
    (deficit_symmetric A hs) (deficit_diagonal A hs hz hb) hn (hb c) hErow hselect hS
  have hsumv : (∑ j∈S,v j)=0 := by
    have hleft : (∑ i∈S,mv S (deficit A) v i)= -2*(∑ i∈S,v i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi=>hEv i hi)
    have hright : (∑ i∈S,mv S (deficit A) v i)=2*(∑ i∈S,v i) := by
      unfold mv
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul]
      have hc' : (∑ i∈S,deficit A i j)=2 := by
        calc
          _ = ∑ i∈S,deficit A j i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact deficit_symmetric A hs i j
          _ = _ := hErow j hj
      rw [hc']
    linarith only [hleft,hright]
  let u : V→ℤ := mv S A v
  have hRv : ∀ c',deg A c'=13 → rowDeficit A c'=0 → u c'=0 := by
    intro c' hcd' hct'
    have hleft : (∑ j∈S,A c' j*mv S (deficit A) v j) = -2*u c' := by
      -- Expand only the target row, then use the eigenvector equation.
      change (∑ j∈S,A c' j*mv S (deficit A) v j) = -2*(∑ j∈S,A c' j*v j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hEv j hj]
      ring
    have hright : (∑ j∈S,A c' j*mv S (deficit A) v j)=0 := by
      unfold mv
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ k∈S,(∑ j∈S,A c' j*deficit A j k)*v k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ k∈S,v k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hAEclean c' hcd' hct' k hk,one_mul]
        _ = 0 := hsumv
    linarith only [hleft,hright]
  have huout : ∀ i,i∉S → u i=0 := by
    intro i hi
    by_cases hio : i=o
    · subst i
      change (∑ j∈S,A o j*v j)=0
      calc
        _ = ∑ j∈S,v j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hAorow,hj]
        _ = _ := hsumv
    · have hct' : rowDeficit A i=0 := by by_contra h; exact hi ((hSmem i).mpr h)
      exact hRv i (hm i hio) hct'
  have hpoly : ∀ i∈S,mv S A u i=8*v i-3*u i := by
    intro i hi
    have hcform : ∀ j∈S,common A i j=7-3*A i j+(if i=j then 6 else 0)-deficit A i j := by
      intro j hj
      have h := common_expand A i j
      rw [(hSdata i hi).2.1,(hSdata j hj).2.1] at h
      by_cases hij : i=j <;> simp [hij] at h ⊢ <;> linarith only [h]
    calc
      mv S A u i = ∑ j : V,A i j*u j := by
        unfold mv
        symm
        apply sum_on_support S (fun j=>A i j*u j)
        intro j hj
        simp [huout j hj]
      _ = ∑ k∈S,common A i k*v k := by
        unfold u mv common
        simp only [Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j∈S,(7-3*A i j+(if i=j then (6 : ℤ) else 0)-deficit A i j)*v j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcform j hj]
      _ = 8*v i-3*u i := by
        have hdiag : (∑ j∈S,(if i=j then (6 : ℤ) else 0)*v j)=6*v i := by
          simp [ite_mul,eq_comm,hi]
        have hE : (∑ j∈S,deficit A i j*v j) = -2*v i := hEv i hi
        have hU : (∑ j∈S,A i j*v j)=u i := rfl
        calc
          _ = 7*(∑ j∈S,v j)-3*(∑ j∈S,A i j*v j)+
              (∑ j∈S,(if i=j then (6 : ℤ) else 0)*v j)-
              (∑ j∈S,deficit A i j*v j) := by
            simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [hsumv,hU,hdiag,hE]; ring
  have hAn : ∀ i j,0≤A i j := by intro i j; rcases hb i j with h | h <;> omega
  exact case_IV_integer_core S A hs hAn hHrow v u (by intros; rfl) hpoly hunit

end Book59CaseElimination
/- Append after the enumeration-soundness and six-case blocks. Candidate,
   not yet compiled. This derives the case data from the verified classifier. -/
namespace Book59Finish
open scoped BigOperators
open BookRamseyUpper Book59Soundness Book59DegreeClassification Book59CaseElimination
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_count_unpack (A : V→V→ℤ) (h : Hist)
    (hh : pack (allCount A)=h) (k : K) : allCount A k=unpack h k := by
  rw [← hh,unpack_pack]

theorem clean_count_unpack (A : V→V→ℤ) (h : Hist)
    (hh : pack (cleanCount A)=h) (k : K) : cleanCount A k=unpack h k := by
  rw [← hh,unpack_pack]

theorem all_count_positive (A : V→V→ℤ) (i : V) (k : K)
    (hi : deg A i=degree k) : 0<allCount A k := by
  change 0<(classSet Finset.univ A k).card
  exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩

theorem degree_of_class (A : V→V→ℤ) (s : Finset V) (k : K)
    (i : V) (hi : i∈classSet s A k) : deg A i=degree k :=
  (Finset.mem_filter.mp hi).2

theorem class_of_degree (A : V→V→ℤ) (k : K) (i : V)
    (hi : deg A i=degree k) : i∈classSet Finset.univ A k :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩

theorem case_I_hist (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1) (hn : ∀ i j,0≤deficit A i j)
    (hpack : pack (allCount A)=[0,0,0,0,29,0,0]) : False := by
  apply case_I A hs hz hb hn
  intro i
  obtain ⟨k,hk⟩ := degree_index (deg A i) (degree_range A hs hn i).1 (degree_range A hs hn i).2
  have hp := all_count_positive A i k hk
  rw [all_count_unpack A _ hpack k] at hp
  fin_cases k
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega
  · simpa [degree] using hk
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega

theorem mixed_hist (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1) (hn : ∀ i j,0≤deficit A i j)
    (l : ℕ) (hlmax : l≤2)
    (hpack : pack (allCount A)=[0,0,l,24,5-l,0,0])
    (hclean : 22+l≤cleanCount A 3)
    (hD : pairBudget (pack (allCount A))=12-2*l) : False := by
  let L := classSet Finset.univ A 2
  let H := classSet Finset.univ A 4
  let C := classSet (cleanSet A) A 3
  have hL : L.card=l := all_count_unpack A _ hpack 2
  have hH : H.card=5-l := all_count_unpack A _ hpack 4
  have hC : 22+l≤C.card := hclean
  have hl : ∀ i∈L,deg A i=12 := by
    intro i hi
    simpa [degree] using degree_of_class A Finset.univ 2 i hi
  have hh : ∀ i∈H,deg A i=14 := by
    intro i hi
    simpa [degree] using degree_of_class A Finset.univ 4 i hi
  have hc : ∀ i∈C,deg A i=13∧rowDeficit A i=0 := by
    intro i hi
    have hd := degree_of_class A (cleanSet A) 3 i hi
    have hc' : i∈cleanSet A := (Finset.mem_filter.mp hi).1
    exact ⟨by simpa [degree] using hd,(Finset.mem_filter.mp hc').2⟩
  have hm : ∀ i,i∉L → i∉H → deg A i=13 := by
    intro i hiL hiH
    obtain ⟨k,hk⟩ := degree_index (deg A i) (degree_range A hs hn i).1 (degree_range A hs hn i).2
    have hp := all_count_positive A i k hk
    rw [all_count_unpack A _ hpack k] at hp
    fin_cases k
    · change 0<0 at hp; omega
    · change 0<0 at hp; omega
    · exact (hiL (class_of_degree A 2 i hk)).elim
    · simpa [degree] using hk
    · exact (hiH (class_of_degree A 4 i hk)).elim
    · change 0<0 at hp; omega
    · change 0<0 at hp; omega
  have hbudget := (graph_pair_budget A hs hz hb hn (degree_range A hs hn)).1
  rw [hD] at hbudget
  exact mixed_cases A hs hz hb hn L H C l hlmax hL hH hC hl hh hm hc (by omega)

theorem only_twelve_thirteen (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hn : ∀ i j,0≤deficit A i j)
    (l m : ℕ) (hpack : pack (allCount A)=[0,0,l,m,0,0,0]) :
    ∀ i, deg A i=12∨deg A i=13 := by
  intro i
  obtain ⟨k,hk⟩ := degree_index (deg A i) (degree_range A hs hn i).1 (degree_range A hs hn i).2
  have hp := all_count_positive A i k hk
  rw [all_count_unpack A _ hpack k] at hp
  fin_cases k
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega
  · exact Or.inl (by simpa [degree] using hk)
  · exact Or.inr (by simpa [degree] using hk)
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega
  · change 0<0 at hp; omega

theorem case_IV_hist (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1) (hn : ∀ i j,0≤deficit A i j)
    (hpack : pack (allCount A)=[0,0,1,28,0,0,0])
    (hcpack : pack (cleanCount A)=[0,0,1,16,0,0,0])
    (hD : pairBudget (pack (allCount A))=12) : False := by
  have hc12 : cleanCount A 2=1 := clean_count_unpack A _ hcpack 2
  have hc13 : cleanCount A 3=16 := clean_count_unpack A _ hcpack 3
  obtain ⟨o,hoC,hoD⟩ := clean_count_vertex A 2 (by omega)
  have hoD' : deg A o=12 := by simpa [degree] using hoD
  let L := classSet Finset.univ A 2
  have hL : L.card=1 := all_count_unpack A _ hpack 2
  have hoL : o∈L := class_of_degree A 2 o hoD
  have hLset : L={o} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.singleton_subset_iff.mpr hoL
    · simp [hL]
  have hm : ∀ i,i≠o→deg A i=13 := by
    intro i hi
    rcases only_twelve_thirteen A hs hn 1 28 hpack i with h | h
    · have hiL : i∈L := class_of_degree A 2 i (by simpa [degree] using h)
      rw [hLset] at hiL
      exact (hi (by simpa using hiL)).elim
    · exact h
  have hbudget := (graph_pair_budget A hs hz hb hn (degree_range A hs hn)).1
  rw [hD] at hbudget
  have hdirty : ∃ i,rowDeficit A i≠0 := by
    by_contra! h
    simp [h] at hbudget
  obtain ⟨c,hc,hd⟩ := clean_count_vertex A 3 (by omega)
  exact case_IV A hs hz hb hn o ⟨hoD',hoC⟩ hm hdirty
    ⟨c,by simpa [degree] using hd,hc⟩

theorem case_VI_hist (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1) (hn : ∀ i j,0≤deficit A i j)
    (hpack : pack (allCount A)=[0,0,3,26,0,0,0])
    (hclean12 : cleanCount A 2=0) (hclean13 : 0<cleanCount A 3)
    (hD : pairBudget (pack (allCount A))=7) : False := by
  let L := classSet Finset.univ A 2
  have hL : L.card=3 := all_count_unpack A _ hpack 2
  have hl : ∀ i∈L,deg A i=12∧rowDeficit A i≠0 := by
    intro i hi
    have hd := degree_of_class A Finset.univ 2 i hi
    refine ⟨by simpa [degree] using hd,?_⟩
    intro hc
    have hiC : i∈cleanSet A := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hc⟩
    have hi' : i∈classSet (cleanSet A) A 2 := Finset.mem_filter.mpr ⟨hiC,hd⟩
    have hp : 0<cleanCount A 2 := Finset.card_pos.mpr ⟨i,hi'⟩
    omega
  have hm : ∀ i,i∉L→deg A i=13 := by
    intro i hi
    rcases only_twelve_thirteen A hs hn 3 26 hpack i with h | h
    · exact (hi (class_of_degree A 2 i (by simpa [degree] using h))).elim
    · exact h
  have hbudget := (graph_pair_budget A hs hz hb hn (degree_range A hs hn)).1
  rw [hD] at hbudget
  obtain ⟨c,hc,hd⟩ := clean_count_vertex A 3 (by omega)
  exact case_VI A hs hz hb hn L hL hl hm (by norm_num at hbudget ⊢; exact hbudget)
    ⟨c,by simpa [degree] using hd,hc⟩

-- No extra hypotheses about the graph's degree histogram or case membership.
theorem no_avoiding_29 (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1)
    (hred : ∀ i j,A i j=1→common A i j≤4)
    (hblue : ∀ i j,i≠j→A i j=0→common (blueAdj A) i j≤8) : False := by
  have hn := deficit_nonnegative A hs hz hb hred hblue
  have h := graph_classification A hs hz hb hred hblue
  simp only [List.mem_cons,List.mem_singleton,Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact case_I_hist A hs hz hb hn h.1
  · have hc : cleanCount A 3=22 := clean_count_unpack A _ h.2.1 3
    exact mixed_hist A hs hz hb hn 0 (by decide) h.1 (by omega) h.2.2
  · have hc : cleanCount A 3=23 := clean_count_unpack A _ h.2.1 3
    exact mixed_hist A hs hz hb hn 0 (by decide) h.1 (by omega) h.2.2
  · have hc : cleanCount A 3=23 := clean_count_unpack A _ h.2.1 3
    exact mixed_hist A hs hz hb hn 1 (by decide) h.1 (by omega) h.2.2
  · have hc : cleanCount A 3=24 := clean_count_unpack A _ h.2.1 3
    exact mixed_hist A hs hz hb hn 1 (by decide) h.1 (by omega) h.2.2
  · exact case_IV_hist A hs hz hb hn h.1 h.2.1 h.2.2
  · have hc : cleanCount A 3=24 := clean_count_unpack A _ h.2.1 3
    exact mixed_hist A hs hz hb hn 2 (by decide) h.1 (by omega) h.2.2
  · have hc12 : cleanCount A 2=0 := clean_count_unpack A _ h.2.1 2
    have hc13 : cleanCount A 3=22 := clean_count_unpack A _ h.2.1 3
    exact case_VI_hist A hs hz hb hn h.1 hc12 (by omega) h.2.2
  · have hc12 : cleanCount A 2=0 := clean_count_unpack A _ h.2.1 2
    have hc13 : cleanCount A 3=23 := clean_count_unpack A _ h.2.1 3
    exact case_VI_hist A hs hz hb hn h.1 hc12 (by omega) h.2.2
  · rcases h with h | h
    · have hc12 : cleanCount A 2=0 := clean_count_unpack A _ h.2.1 2
      have hc13 : cleanCount A 3=24 := clean_count_unpack A _ h.2.1 3
      exact case_VI_hist A hs hz hb hn h.1 hc12 (by omega) h.2.2
    · simp at h

-- The actual upper-bound statement: every two-coloring of K_29 has a
-- red B5 or a blue B9. The only hypotheses are the adjacency-matrix axioms.
theorem upper_bound_29 (A : V→V→ℤ)
    (hs : ∀ i j,A i j=A j i) (hz : ∀ i,A i i=0)
    (hb : ∀ i j,A i j=0∨A i j=1) :
    (∃ i j,A i j=1∧5≤common A i j) ∨
    (∃ i j,i≠j∧A i j=0∧9≤common (blueAdj A) i j) := by
  by_cases hr : ∃ i j,A i j=1∧5≤common A i j
  · exact Or.inl hr
  by_cases hbl : ∃ i j,i≠j∧A i j=0∧9≤common (blueAdj A) i j
  · exact Or.inr hbl
  have hred : ∀ i j,A i j=1→common A i j≤4 := by
    intro i j hij
    by_contra! h
    exact hr ⟨i,j,hij,by omega⟩
  have hblue : ∀ i j,i≠j→A i j=0→common (blueAdj A) i j≤8 := by
    intro i j hne hij
    by_contra! h
    exact hbl ⟨i,j,hne,hij,by omega⟩
  exact (no_avoiding_29 A hs hz hb hred hblue).elim

end Book59Finish


namespace BookRamsey

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def red (u v : Fin 28) : Bool :=
  if u == v then false
  else
    let i := u.val % 14
    let j := v.val % 14
    let d := (j + 14 - i) % 14
    if u.val < 14 then
      if v.val < 14 then
        [3, 4, 5, 7, 9, 10, 11].contains d
      else
        [0, 1, 3, 5, 6].contains d
    else
      if v.val < 14 then
        [0, 1, 3, 5, 6].contains ((i + 14 - j) % 14)
      else
        [1, 2, 6, 8, 12, 13].contains d

def blue (u v : Fin 28) : Bool :=
  u != v && !(red u v)

def redCommon (u v : Fin 28) : Nat :=
  (Finset.univ.filter
    (fun w : Fin 28 =>
      red u w = true ∧ red v w = true)).card

def blueCommon (u v : Fin 28) : Nat :=
  (Finset.univ.filter
    (fun w : Fin 28 =>
      blue u w = true ∧ blue v w = true)).card

theorem red_symmetric :
    ∀ u v : Fin 28, red u v = red v u := by
  decide

theorem red_loopless :
    ∀ u : Fin 28, red u u = false := by
  decide

theorem no_red_B5 :
    ∀ u v : Fin 28,
      red u v = true → redCommon u v ≤ 4 := by
  decide

theorem no_blue_B9 :
    ∀ u v : Fin 28,
      blue u v = true → blueCommon u v ≤ 8 := by
  decide


end BookRamsey


namespace Book59Exact
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def commonN {n : ℕ} (A : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  ∑ k, A i k * A k j

def blueN {n : ℕ} (A : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  if i = j then 0 else 1 - A i j

def RamseyProperty (n : ℕ) : Prop :=
  ∀ A : Fin n → Fin n → ℤ,
    (∀ i j, A i j = A j i) →
    (∀ i, A i i = 0) →
    (∀ i j, A i j = 0 ∨ A i j = 1) →
    (∃ i j, A i j = 1 ∧ 5 ≤ commonN A i j) ∨
    (∃ i j, i ≠ j ∧ A i j = 0 ∧ 9 ≤ commonN (blueN A) i j)

def witness (i j : Fin 28) : ℤ := if BookRamsey.red i j then 1 else 0

theorem witness_sym : ∀ i j, witness i j = witness j i := by decide

theorem witness_loop : ∀ i, witness i i = 0 := by decide

theorem witness_binary : ∀ i j, witness i j = 0 ∨ witness i j = 1 := by decide

theorem witness_red : ∀ i j, witness i j = 1 → commonN witness i j ≤ 4 := by decide

theorem witness_blue : ∀ i j, i ≠ j → witness i j = 0 → commonN (blueN witness) i j ≤ 8 := by decide

theorem not_ramsey_28 : ¬ RamseyProperty 28 := by
  intro h
  rcases h witness witness_sym witness_loop witness_binary with hr | hb
  · obtain ⟨i,j,hij,hc⟩ := hr
    have hh := witness_red i j hij
    omega
  · obtain ⟨i,j,hne,hij,hc⟩ := hb
    have hh := witness_blue i j hne hij
    omega

theorem ramsey_29 : RamseyProperty 29 := by
  intro A hs hz hb
  exact Book59Finish.upper_bound_29 A hs hz hb

theorem common_restrict_le {m n : ℕ} (e : Fin m ↪ Fin n)
    (A : Fin n → Fin n → ℤ) (hn : ∀ i j, 0 ≤ A i j)
    (i j : Fin m) :
    commonN (fun u v => A (e u) (e v)) i j ≤ commonN A (e i) (e j) := by
  unfold commonN
  calc
    _ = ∑ k ∈ (Finset.univ : Finset (Fin m)).map e, A (e i) k * A k (e j) := by
      rw [Finset.sum_map]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun k _ _ => mul_nonneg (hn _ _) (hn _ _))

theorem ramsey_mono {m n : ℕ} (hmn : m ≤ n) (hm : RamseyProperty m) :
    RamseyProperty n := by
  intro A hs hz hb
  let e : Fin m ↪ Fin n := ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩,
    fun i j h => Fin.ext (congrArg (fun x : Fin n => x.val) h)⟩
  let B : Fin m → Fin m → ℤ := fun i j => A (e i) (e j)
  have hn : ∀ i j, 0 ≤ A i j := by
    intro i j
    rcases hb i j with h | h <;> omega
  have hbn : ∀ i j, 0 ≤ blueN A i j := by
    intro i j
    unfold blueN
    split <;> rcases hb i j with h | h <;> omega
  have hblue_eq : blueN B = fun i j => blueN A (e i) (e j) := by
    funext i j
    by_cases h : i = j
    · subst j
      simp [blueN]
    · have he : e i ≠ e j := fun heq => h (e.injective heq)
      simp [blueN, B, h, he]
  rcases hm B (fun i j => hs _ _) (fun i => hz _) (fun i j => hb _ _) with hr | hc
  · obtain ⟨i,j,hij,hh⟩ := hr
    exact Or.inl ⟨e i,e j,hij,le_trans hh (common_restrict_le e A hn i j)⟩
  · obtain ⟨i,j,hne,hij,hh⟩ := hc
    rw [hblue_eq] at hh
    exact Or.inr ⟨e i,e j,fun heq => hne (e.injective heq),hij,
      le_trans hh (common_restrict_le e (blueN A) hbn i j)⟩

-- This states the exact least n for the book Ramsey property, not merely
-- a bound or a theorem conditional on one of the missing cases.
theorem book_ramsey_5_9_eq_29 : IsLeast {n : ℕ | RamseyProperty n} 29 := by
  refine ⟨ramsey_29, ?_⟩
  intro n hn
  change RamseyProperty n at hn
  change 29 ≤ n
  by_contra! h
  exact not_ramsey_28 (ramsey_mono (show n ≤ 28 by omega) hn)

end Book59Exact

namespace LeapsInBounds.BookRamsey

open scoped BigOperators

noncomputable section

private def book59Matrix {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : ℤ := by
  classical
  exact if G.Adj i j then 1 else 0

private theorem book59Matrix_sym {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : book59Matrix G i j = book59Matrix G j i := by
  classical
  unfold book59Matrix
  by_cases h : G.Adj i j
  · have h' : G.Adj j i := G.symm h
    simp [h, h']
  · have h' : ¬ G.Adj j i := fun hj => h (G.symm hj)
    simp [h, h']

private theorem book59Matrix_compl {n : ℕ} (G : SimpleGraph (Fin n)) :
    Book59Exact.blueN (book59Matrix G) = book59Matrix Gᶜ := by
  classical
  funext i j
  unfold Book59Exact.blueN book59Matrix
  change (if i = j then (0 : ℤ) else 1 - (if G.Adj i j then 1 else 0)) =
    (if i ≠ j ∧ ¬ G.Adj i j then 1 else 0)
  by_cases he : i = j
  · simp [he]
  · by_cases ha : G.Adj i j <;> simp [he, ha]

private theorem book59Matrix_hasBook {n m : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j)
    (hc : (m : ℤ) ≤ Book59Exact.commonN (book59Matrix G) i j) :
    HasBook G m := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun k => G.Adj i k ∧ G.Adj j k)
  have hcount : Book59Exact.commonN (book59Matrix G) i j = (S.card : ℤ) := by
    unfold Book59Exact.commonN
    calc
      (∑ k : Fin n, book59Matrix G i k * book59Matrix G k j) =
          ∑ k : Fin n, if G.Adj i k ∧ G.Adj j k then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hsym : G.Adj k j ↔ G.Adj j k := ⟨G.symm, G.symm⟩
        unfold book59Matrix
        by_cases h₁ : G.Adj i k <;> by_cases h₂ : G.Adj j k <;>
          simp [h₁, h₂, hsym]
      _ = (S.card : ℤ) := by
        change (∑ k : Fin n, if G.Adj i k ∧ G.Adj j k then (1 : ℤ) else 0) =
          ((Finset.univ.filter (fun k : Fin n => G.Adj i k ∧ G.Adj j k)).card : ℤ)
        rw [← Finset.sum_filter]
        simp
  rw [hcount] at hc
  have hm : m ≤ S.card := by exact_mod_cast hc
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hm
  refine ⟨i, j, hij, s, hcard, ?_⟩
  intro w hw
  exact (Finset.mem_filter.mp (hs hw)).2

/-- Every graph on 29 vertices contains a five-page book, or its complement
contains a nine-page book. -/
theorem book_ramsey_5_9_upper : UpperBound 5 9 29 := by
  classical
  intro G
  have hz : ∀ i, book59Matrix G i i = 0 := by
    intro i
    simp [book59Matrix, G.loopless i]
  have hb : ∀ i j, book59Matrix G i j = 0 ∨ book59Matrix G i j = 1 := by
    intro i j
    by_cases h : G.Adj i j <;> simp [book59Matrix, h]
  rcases Book59Exact.ramsey_29 (book59Matrix G) (book59Matrix_sym G) hz hb with hr | hc
  · obtain ⟨i, j, hij, hcount⟩ := hr
    have ha : G.Adj i j := by
      by_contra hn
      simp [book59Matrix, hn] at hij
    exact Or.inl (book59Matrix_hasBook G i j ha hcount)
  · obtain ⟨i, j, hne, hij, hcount⟩ := hc
    have hn : ¬ G.Adj i j := by
      intro ha
      simp [book59Matrix, ha] at hij
    have ha : Gᶜ.Adj i j := ⟨hne, hn⟩
    rw [book59Matrix_compl G] at hcount
    exact Or.inr (book59Matrix_hasBook Gᶜ i j ha hcount)

end
end LeapsInBounds.BookRamsey

#print axioms LeapsInBounds.BookRamsey.book_ramsey_5_9_upper
