module

public import LeapsInBounds.Statements.Schur
import Mathlib.Logic.Equiv.Basic

/-!
# Upper bounds on small Schur numbers by exhaustive search

A backtracking search colors `1, 2, …` in turn with each of the `k` colors,
and abandons a branch as soon as the last number colored completes a
monochromatic solution to `x + y = z` (with `x ≠ y` for weak Schur numbers).
If every branch is abandoned before coloring `n + 1`, every `k`-coloring of
`1, …, n + 1` has a monochromatic solution. The search runs in the kernel
(`decide +kernel`, no `native_decide`), and is proved sound here.

For each color, the search keeps as bitmasks the set `S` of numbers with that
color and the set `F` of sums `x + y` of two of them (with `x < y` for weak
Schur numbers), so a number `z` can't take the color if `z ∈ F`. By symmetry
between colors, `1` gets the first color.
-/

@[expose] public section

namespace LeapsInBounds.Proofs.SchurSmallUpper

/-- `g` with the value at `i` replaced by `a`. -/
def upd (g : ℕ → ℕ) (i a : ℕ) : ℕ → ℕ := fun j => if j = i then a else g j

/-- Give `z` the color `col`: add it to the color's set `S`, and its sums with
the numbers of that color to the color's set `F`. -/
def step (weak : Bool) (S F : ℕ → ℕ) (z col : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let s := S col ||| 2 ^ z
  (upd S col s, upd F col (F col ||| ((if weak then S col else s) <<< z)))

/-- `true` if every extension of the coloring of `1, …, m` (given by `S` and `F`)
to `1, …, m + fuel` with `k` colors has a monochromatic solution. -/
def search (k : ℕ) (weak : Bool) : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, S, F, m => (List.range k).all fun col =>
      (F col).testBit (m + 1) ||
        search k weak fuel (step weak S F (m + 1) col).1 (step weak S F (m + 1) col).2 (m + 1)

/-- The condition on the two summands. -/
def Cond (weak : Bool) (x y : ℕ) : Prop := if weak then x < y else x ≤ y

/-- `S` and `F` describe the coloring `c` of `1, …, m`. -/
structure Inv (weak : Bool) (c : ℕ → ℕ) (m : ℕ) (S F : ℕ → ℕ) : Prop where
  hS : ∀ col x, (S col).testBit x = true ↔ (0 < x ∧ x ≤ m ∧ c x = col)
  hF : ∀ col w, (F col).testBit w = true →
    ∃ x y, 0 < x ∧ Cond weak x y ∧ x + y = w ∧ c x = col ∧ c y = col

lemma inv_zero (weak : Bool) (c : ℕ → ℕ) : Inv weak c 0 (fun _ => 0) (fun _ => 0) :=
  ⟨fun col x => by simp; intro h1 h2; omega, fun col w h => by simp at h⟩

lemma inv_step {weak : Bool} {c : ℕ → ℕ} {m : ℕ} {S F : ℕ → ℕ} (h : Inv weak c m S F) :
    Inv weak c (m + 1) (step weak S F (m + 1) (c (m + 1))).1
      (step weak S F (m + 1) (c (m + 1))).2 := by
  constructor
  · intro col x
    simp only [step, upd]
    split_ifs with hc
    · subst hc
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, h.hS, decide_eq_true_iff]
      constructor
      · rintro (⟨h1, h2, h3⟩ | rfl)
        · exact ⟨h1, by omega, h3⟩
        · exact ⟨by omega, Nat.le_refl _, rfl⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_or_ge x (m + 1) with hx | hx
        · exact Or.inl ⟨h1, by omega, h3⟩
        · exact Or.inr (by omega)
    · rw [h.hS]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rcases Nat.lt_or_ge x (m + 1) with hx | hx
        · omega
        · exact (hc (by rw [← h3, show x = m + 1 by omega])).elim
  · intro col w hw
    by_cases hc : col = c (m + 1)
    · subst hc
      simp only [step, upd, ↓reduceIte] at hw
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true,
        decide_eq_true_iff] at hw
      cases hw with
      | inl hw => exact h.hF _ _ hw
      | inr hw =>
        obtain ⟨hwz, hw⟩ := hw
        refine ⟨w - (m + 1), m + 1, ?_⟩
        cases weak with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_or, Nat.testBit_two_pow,
            Bool.or_eq_true, h.hS, decide_eq_true_iff] at hw
          cases hw with
          | inl h' =>
            obtain ⟨h1, h2, h3⟩ := h'
            exact ⟨h1, by simp only [Cond, Bool.false_eq_true, ↓reduceIte]; omega, by omega, h3, rfl⟩
          | inr h' =>
            refine ⟨by omega, by simp only [Cond, Bool.false_eq_true, ↓reduceIte]; omega, by omega,
              ?_, rfl⟩
            rw [show w - (m + 1) = m + 1 by omega]
        | true =>
          simp only [↓reduceIte, h.hS] at hw
          obtain ⟨h1, h2, h3⟩ := hw
          exact ⟨h1, by simp only [Cond, ↓reduceIte]; omega, by omega, h3, rfl⟩
    · simp only [step, upd, hc, ↓reduceIte] at hw
      exact h.hF _ _ hw

/-- Soundness of the search. -/
lemma search_sound {k : ℕ} {weak : Bool} {c : ℕ → ℕ} (hc : ∀ x, c x < k) :
    ∀ (fuel : ℕ) (S F : ℕ → ℕ) (m : ℕ), search k weak fuel S F m = true → Inv weak c m S F →
      ∃ x y, 0 < x ∧ Cond weak x y ∧ x + y ≤ m + fuel ∧ c x = c y ∧ c (x + y) = c x
  | 0, _, _, _, h, _ => by simp [search] at h
  | fuel + 1, S, F, m, h, hinv => by
    simp only [search, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
    rcases h (c (m + 1)) (hc _) with hb | hs
    · obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := hinv.hF _ _ hb
      exact ⟨x, y, h1, h2, by omega, by rw [h4, h5], by rw [h3, h4]⟩
    · obtain ⟨x, y, h1, h2, h3, h4⟩ := search_sound hc fuel _ _ _ hs (inv_step hinv)
      exact ⟨x, y, h1, h2, by omega, h4⟩

/-- The state after giving `1` the first color. -/
def S1 (weak : Bool) : ℕ → ℕ := (step weak (fun _ => 0) (fun _ => 0) 1 0).1
def F1 (weak : Bool) : ℕ → ℕ := (step weak (fun _ => 0) (fun _ => 0) 1 0).2

/-- If the search succeeds, every `k`-coloring of `1, …, n + 1` has a monochromatic
solution with summands satisfying `Cond`. -/
theorem exists_of_search {k n : ℕ} {weak : Bool} (h : search k weak n (S1 weak) (F1 weak) 1 = true)
    (c : ℕ → Fin k) :
    ∃ x y, 0 < x ∧ Cond weak x y ∧ x + y ≤ n + 1 ∧ c x = c y ∧ c (x + y) = c x := by
  -- recolor so that `1` has color `0`
  let σ : Equiv.Perm ℕ := Equiv.swap 0 (c 1).val
  let c' : ℕ → ℕ := fun x => σ (c x).val
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) (c 1).isLt
  have hc' : ∀ x, c' x < k := by
    intro x
    simp only [c', σ, Equiv.swap_apply_def]
    split_ifs <;> simp [hk]
  have hc1 : c' 1 = 0 := by simp [c', σ]
  have hinj : ∀ x y, c' x = c' y ↔ c x = c y := by
    intro x y
    simp only [c', σ.injective.eq_iff, Fin.val_inj]
  have hinv : Inv weak c' 1 (S1 weak) (F1 weak) := by
    have := inv_step (inv_zero weak c') (m := 0)
    rwa [Nat.zero_add, hc1] at this
  obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := search_sound hc' n _ _ 1 h hinv
  exact ⟨x, y, h1, h2, by omega, (hinj _ _).1 h4, (hinj _ _).1 h5⟩

theorem upperBound_of_search {k n : ℕ} (h : search k false n (S1 false) (F1 false) 1 = true) :
    Schur.UpperBound k n := fun c => by
  obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := exists_of_search h c
  simp only [Cond, Bool.false_eq_true, ↓reduceIte] at h2
  exact ⟨x, y, h1, by omega, h3, h4, h5⟩

theorem weakUpperBound_of_search {k n : ℕ} (h : search k true n (S1 true) (F1 true) 1 = true) :
    Schur.WeakUpperBound k n := fun c => by
  obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := exists_of_search h c
  simp only [Cond, ↓reduceIte] at h2
  exact ⟨x, y, h1, h2, h3, h4, h5⟩

/-- `S(1) ≤ 1`. -/
theorem upper_1_1 : Schur.UpperBound 1 1 := upperBound_of_search (by decide +kernel)
/-- `S(2) ≤ 4`. -/
theorem upper_2_4 : Schur.UpperBound 2 4 := upperBound_of_search (by decide +kernel)
/-- `WS(1) ≤ 2`. -/
theorem weakUpper_1_2 : Schur.WeakUpperBound 1 2 := weakUpperBound_of_search (by decide +kernel)
/-- `WS(2) ≤ 8`. -/
theorem weakUpper_2_8 : Schur.WeakUpperBound 2 8 := weakUpperBound_of_search (by decide +kernel)
/-- `S(3) ≤ 13`. -/
theorem upper_3_13 : Schur.UpperBound 3 13 := upperBound_of_search (by decide +kernel)
/-- `WS(3) ≤ 23`. -/
theorem weakUpper_3_23 : Schur.WeakUpperBound 3 23 := weakUpperBound_of_search (by decide +kernel)

end LeapsInBounds.Proofs.SchurSmallUpper
