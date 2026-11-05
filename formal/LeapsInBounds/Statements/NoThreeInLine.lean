module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Basic

/-!
# The no-three-in-line problem

Formal statements of bounds on `D(n)`: the largest number of points of the
`n × n` grid that can be chosen with no three on a line, in any direction.
The grid's points are the pairs of natural numbers less than `n`.

A certificate for `no-three-in-line-{n}` with lower bound `L` must prove
`LowerBound n L`, and one with upper bound `L` must prove `UpperBound n L`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.NoThreeInLine

/-- The points `p`, `q` and `r` are on a line. -/
def Collinear (p q r : ℕ × ℕ) : Prop :=
  ((q.1 : ℤ) - p.1) * ((r.2 : ℤ) - p.2) = ((r.1 : ℤ) - p.1) * ((q.2 : ℤ) - p.2)

/-- No three distinct points of `s` are on a line. -/
def NoThreeCollinear (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear p q r

/-- Every point of `s` is in the `n × n` grid. -/
def InGrid (n : ℕ) (s : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ s, p.1 < n ∧ p.2 < n

/-- `D(n) ≥ L`: some `L` points of the `n × n` grid have no three on a line. -/
def LowerBound (n L : ℕ) : Prop :=
  ∃ s : Finset (ℕ × ℕ), InGrid n s ∧ NoThreeCollinear s ∧ L ≤ s.card

/-- `D(n) ≤ L`: any points of the `n × n` grid with no three on a line number
at most `L`. -/
def UpperBound (n L : ℕ) : Prop :=
  ∀ s : Finset (ℕ × ℕ), InGrid n s → NoThreeCollinear s → s.card ≤ L

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k L : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n L) : k ≤ L := by
  obtain ⟨s, hg, hs, hk⟩ := hl
  have := hu s hg hs
  omega

end LeapsInBounds.NoThreeInLine
