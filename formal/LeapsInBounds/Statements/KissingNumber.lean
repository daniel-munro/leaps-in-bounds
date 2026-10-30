module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Kissing numbers

Formal statements of bounds on the kissing number `τ(n)`: the largest number of
non-overlapping unit spheres in `ℝⁿ` that touch a central unit sphere.

The spheres touching the central one have centers `2 x i` for unit vectors
`x i`, and two of them don't overlap exactly when `‖2 x i - 2 x j‖ ≥ 2`, that
is, when `dist (x i) (x j) ≥ 1`.

A certificate for `kissing-number-{n}` with lower bound `k` must prove
`LowerBound n k`, and one with upper bound `k` must prove `UpperBound n k`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.KissingNumber

/-- `x` is a kissing configuration: unit vectors at distance at least `1` from
each other. -/
def IsKissingConfiguration {n m : ℕ} (x : Fin m → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ ∀ i j, i ≠ j → 1 ≤ dist (x i) (x j)

/-- `τ(n) ≥ k`: some kissing configuration in `ℝⁿ` has `k` vectors. -/
def LowerBound (n k : ℕ) : Prop :=
  ∃ x : Fin k → EuclideanSpace ℝ (Fin n), IsKissingConfiguration x

/-- `τ(n) ≤ k`: every kissing configuration in `ℝⁿ` has at most `k` vectors. -/
def UpperBound (n k : ℕ) : Prop :=
  ∀ m, ∀ x : Fin m → EuclideanSpace ℝ (Fin n), IsKissingConfiguration x → m ≤ k

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k l : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n l) : k ≤ l := by
  obtain ⟨x, hx⟩ := hl
  exact hu k x hx

end LeapsInBounds.KissingNumber
