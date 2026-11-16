module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Covering a disk with disks

Formal statements of bounds on `r(n)`: the smallest radius such that `n`
closed disks of that radius cover the closed unit disk.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals. A certificate for
`disk-covering-{n}` with lower bound `radical terms d` must prove
`RadicalLowerBound n terms d`, and one with that upper bound must prove
`RadicalUpperBound n terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.DiskCovering

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed disks of radius `r` with centers `c i` cover the closed unit
disk. -/
def Covers {n : ℕ} (r : ℝ) (c : Fin n → Plane) : Prop :=
  Metric.closedBall (0 : Plane) 1 ⊆ ⋃ i, Metric.closedBall (c i) r

/-- `r(n) ≥ a`: no `n` disks of radius less than `a` cover the unit disk. -/
def LowerBound (n : ℕ) (a : ℝ) : Prop :=
  ∀ r, ∀ c : Fin n → Plane, Covers r c → a ≤ r

/-- `r(n) ≤ a`: some `n` disks of radius `a` cover the unit disk. -/
def UpperBound (n : ℕ) (a : ℝ) : Prop :=
  ∃ c : Fin n → Plane, Covers a c

/-- `r(n) ≥ radical terms d`. -/
def RadicalLowerBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound n (radical terms d)

/-- `r(n) ≤ radical terms d`. -/
def RadicalUpperBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound n (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n : ℕ} {a b : ℝ} (hl : LowerBound n a)
    (hu : UpperBound n b) : a ≤ b := by
  obtain ⟨c, hc⟩ := hu
  exact hl b c hc

end LeapsInBounds.DiskCovering
