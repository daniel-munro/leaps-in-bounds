module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The chromatic number of Euclidean space

Formal statements of bounds on `χ(ℝⁿ)`: the fewest colors needed to color the
points of `ℝⁿ` so that no two points at distance exactly 1 have the same color.
A coloring is any function to `Fin k`, with no assumption such as
measurability on its color classes.

A certificate for `chromatic-number-space-{n}` with lower bound `k` must prove
`LowerBound n k`, and one with upper bound `k` must prove `UpperBound n k`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.ChromaticNumberSpace

/-- `c` colors `ℝⁿ` with `k` colors so that no two points at distance 1 have
the same color. -/
def ProperColoring {n k : ℕ} (c : EuclideanSpace ℝ (Fin n) → Fin k) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin n), dist x y = 1 → c x ≠ c y

/-- `χ(ℝⁿ) ≥ k`: no coloring of `ℝⁿ` with `k - 1` colors is proper. -/
def LowerBound (n k : ℕ) : Prop :=
  ¬ ∃ c : EuclideanSpace ℝ (Fin n) → Fin (k - 1), ProperColoring c

/-- `χ(ℝⁿ) ≤ k`: some coloring of `ℝⁿ` with `k` colors is proper. -/
def UpperBound (n k : ℕ) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin n) → Fin k, ProperColoring c

/-- A lower bound never exceeds an upper bound, as a sanity check on the
definitions: a proper coloring with `u` colors is one with `l - 1` colors
when `u ≤ l - 1`. -/
theorem le_of_lowerBound_of_upperBound {n l u : ℕ} (hl : LowerBound n l) (hu : UpperBound n u) :
    l ≤ u := by
  by_contra h
  obtain ⟨c, hc⟩ := hu
  exact hl ⟨fun x => Fin.castLE (by omega) (c x), fun x y hxy heq => hc x y hxy (Fin.castLE_injective _ heq)⟩

end LeapsInBounds.ChromaticNumberSpace
