module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Packing unit circles in an equilateral triangle

Formal statements of bounds on `s(n)`: the side of the smallest equilateral
triangle into which `n` unit circles can be packed.

A packing places `n` closed unit disks inside the triangle with pairwise
disjoint interiors. Every equilateral triangle of side `s` is congruent to the
one with vertices `(0, 0)`, `(s, 0)` and `(s / 2, s √3 / 2)`, so that one is
used.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`). A certificate for
`circle-in-equilateral-{n}` with lower bound `radical terms d` must prove
`RadicalLowerBound n terms d`, and one with that upper bound must prove
`RadicalUpperBound n terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.CircleInTriangle

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The equilateral triangle with vertices `(0, 0)`, `(s, 0)` and
`(s / 2, s √3 / 2)`: the points on or above the line through the first two,
and on or below the lines through the third and each of the others. -/
def triangle (s : ℝ) : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ √3 * p 0 ∧ p 1 ≤ √3 * (s - p 0)}

/-- `c` places `n` closed unit disks with centers `c i` in the triangle of side
`s`, with pairwise disjoint interiors. -/
def IsPacking {n : ℕ} (s : ℝ) (c : Fin n → Plane) : Prop :=
  0 ≤ s ∧ (∀ i, Metric.closedBall (c i) 1 ⊆ triangle s) ∧
    ∀ i j, i ≠ j → Disjoint (Metric.ball (c i) 1) (Metric.ball (c j) 1)

/-- `s(n) ≥ a`: no packing of `n` unit circles fits in an equilateral triangle
of side less than `a`. -/
def LowerBound (n : ℕ) (a : ℝ) : Prop :=
  ∀ s, ∀ c : Fin n → Plane, IsPacking s c → a ≤ s

/-- `s(n) ≤ a`: `n` unit circles can be packed in an equilateral triangle of
side `a`. -/
def UpperBound (n : ℕ) (a : ℝ) : Prop :=
  ∃ c : Fin n → Plane, IsPacking a c

/-- `s(n) ≥ radical terms d`. -/
def RadicalLowerBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound n (radical terms d)

/-- `s(n) ≤ radical terms d`. -/
def RadicalUpperBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound n (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n : ℕ} {a b : ℝ} (hl : LowerBound n a)
    (hu : UpperBound n b) : a ≤ b := by
  obtain ⟨c, hc⟩ := hu
  exact hl b c hc

end LeapsInBounds.CircleInTriangle
