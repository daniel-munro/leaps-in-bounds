module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Isosceles sets

Formal statements of bounds on `i(n)`: the size of the largest isosceles set
in `ℝⁿ`, a set of points any three of which form an isosceles triangle (two
of its sides have the same length).

A certificate for `isosceles-set-{n}` with lower bound `L` must prove
`LowerBound n L`, and one with upper bound `L` must prove `UpperBound n L`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.IsoscelesSet

/-- Every three distinct points of `s` form an isosceles triangle. -/
def IsIsosceles {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
    dist x y = dist x z ∨ dist y x = dist y z ∨ dist z x = dist z y

/-- `i(n) ≥ L`: some isosceles set in `ℝⁿ` has at least `L` points. -/
def LowerBound (n L : ℕ) : Prop :=
  ∃ s : Finset (EuclideanSpace ℝ (Fin n)), IsIsosceles s ∧ L ≤ s.card

/-- `i(n) ≤ L`: every isosceles set in `ℝⁿ` has at most `L` points. -/
def UpperBound (n L : ℕ) : Prop :=
  ∀ s : Finset (EuclideanSpace ℝ (Fin n)), IsIsosceles s → s.card ≤ L

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k L : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n L) : k ≤ L := by
  obtain ⟨s, hs, hk⟩ := hl
  have := hu s hs
  omega

end LeapsInBounds.IsoscelesSet
