module

public import Mathlib.Data.Fin.Basic

/-!
# Schur numbers

Formal statements of bounds on the Schur number `S(k)`: the largest `n` such
that the integers `1, …, n` can be colored with `k` colors with no
monochromatic solution to `x + y = z`, where `x = y` is allowed. The weak
Schur number `WS(k)` is the same, but only for solutions with `x ≠ y`.

A certificate for `schur-{k}` with lower bound `n` must prove
`LowerBound k n`, and one with upper bound `n` must prove `UpperBound k n`.
Likewise for `weak-schur-{k}`, with `WeakLowerBound` and `WeakUpperBound`.

Colorings are functions on all of `ℕ`, but only the colors of `1, …, n`
matter.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Schur

/-- The coloring `c` has a monochromatic solution to `x + y = z` within
`1, …, n`. -/
def HasMonoSum (k n : ℕ) (c : ℕ → Fin k) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y ≤ n ∧ c x = c y ∧ c (x + y) = c x

/-- The coloring `c` has a monochromatic solution to `x + y = z` with `x ≠ y`
within `1, …, n`. -/
def HasWeakMonoSum (k n : ℕ) (c : ℕ → Fin k) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ x < y ∧ x + y ≤ n ∧ c x = c y ∧ c (x + y) = c x

/-- `S(k) ≥ n`: some `k`-coloring of `1, …, n` has no monochromatic solution
to `x + y = z`. -/
def LowerBound (k n : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ¬ HasMonoSum k n c

/-- `S(k) ≤ n`: every `k`-coloring of `1, …, n + 1` has a monochromatic
solution to `x + y = z`. -/
def UpperBound (k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin k, HasMonoSum k (n + 1) c

/-- `WS(k) ≥ n`: some `k`-coloring of `1, …, n` has no monochromatic solution
to `x + y = z` with `x ≠ y`. -/
def WeakLowerBound (k n : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ¬ HasWeakMonoSum k n c

/-- `WS(k) ≤ n`: every `k`-coloring of `1, …, n + 1` has a monochromatic
solution to `x + y = z` with `x ≠ y`. -/
def WeakUpperBound (k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin k, HasWeakMonoSum k (n + 1) c

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {k m n : ℕ} (hl : LowerBound k m)
    (hu : UpperBound k n) : m ≤ n := by
  by_contra h
  obtain ⟨c, hc⟩ := hl
  obtain ⟨x, y, hx, hy, hle, hxy, hz⟩ := hu c
  exact hc ⟨x, y, hx, hy, by omega, hxy, hz⟩

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem WeakLowerBound.le_of_weakUpperBound {k m n : ℕ} (hl : WeakLowerBound k m)
    (hu : WeakUpperBound k n) : m ≤ n := by
  by_contra h
  obtain ⟨c, hc⟩ := hl
  obtain ⟨x, y, hx, hlt, hle, hxy, hz⟩ := hu c
  exact hc ⟨x, y, hx, hlt, by omega, hxy, hz⟩

end LeapsInBounds.Schur
