module

public import Mathlib.Data.Finset.Card

/-!
# Optimal Golomb rulers

Formal statements of bounds on `G(n)`: the smallest length of a Golomb ruler
with `n` marks, a set of `n` integers whose pairwise differences are all
distinct. The length of a ruler is the difference between its largest and
smallest marks, and since rulers can be translated, marks are taken to be
natural numbers.

A certificate for `golomb-ruler-{n}` with lower bound `L` must prove
`LowerBound n L`, and one with upper bound `L` must prove `UpperBound n L`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Golomb

/-- The marks `s` form a Golomb ruler: no two pairs of marks are the same
distance apart. -/
def IsGolomb (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s, a < b → c < d → b - a = d - c → a = c ∧ b = d

/-- `G(n) ≥ L`: every Golomb ruler with `n` marks has two marks at least `L`
apart. -/
def LowerBound (n L : ℕ) : Prop :=
  ∀ s : Finset ℕ, s.card = n → IsGolomb s → ∃ a ∈ s, ∃ b ∈ s, L ≤ b - a

/-- `G(n) ≤ L`: some Golomb ruler with `n` marks has its marks in `0, …, L`. -/
def UpperBound (n L : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = n ∧ IsGolomb s ∧ ∀ a ∈ s, a ≤ L

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n m L : ℕ} (hl : LowerBound n m)
    (hu : UpperBound n L) : m ≤ L := by
  obtain ⟨s, hcard, hs, hle⟩ := hu
  obtain ⟨a, -, b, hb, h⟩ := hl s hcard hs
  have := hle b hb
  omega

end LeapsInBounds.Golomb
