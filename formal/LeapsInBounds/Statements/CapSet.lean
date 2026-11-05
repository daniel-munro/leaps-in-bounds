module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Finset.Card

/-!
# Cap sets

Formal statements of bounds on `r(n)`: the size of the largest cap set in
`𝔽₃ⁿ`, a set of points with no three on a line. Three distinct points
`x, y, z` of `𝔽₃ⁿ` are on a line exactly when `x + y + z = 0`.

A certificate for `cap-set-{n}` with lower bound `L` must prove
`LowerBound n L`, and one with upper bound `L` must prove `UpperBound n L`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.CapSet

/-- `s` is a cap set in `𝔽₃ⁿ`: no three distinct points of `s` sum to zero. -/
def IsCap {n : ℕ} (s : Finset (Fin n → ZMod 3)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → x + y + z ≠ 0

/-- `r(n) ≥ L`: some cap set in `𝔽₃ⁿ` has at least `L` points. -/
def LowerBound (n L : ℕ) : Prop :=
  ∃ s : Finset (Fin n → ZMod 3), IsCap s ∧ L ≤ s.card

/-- `r(n) ≤ L`: every cap set in `𝔽₃ⁿ` has at most `L` points. -/
def UpperBound (n L : ℕ) : Prop :=
  ∀ s : Finset (Fin n → ZMod 3), IsCap s → s.card ≤ L

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k L : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n L) : k ≤ L := by
  obtain ⟨s, hs, hk⟩ := hl
  have := hu s hs
  omega

end LeapsInBounds.CapSet
