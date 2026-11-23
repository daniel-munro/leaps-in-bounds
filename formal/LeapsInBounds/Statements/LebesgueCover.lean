module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue's universal covering problem

Formal statements of bounds on the Lebesgue universal covering constant: the
smallest area of a convex set in the plane that contains a congruent copy of
every set of diameter 1.

A universal cover is a convex set `U` such that every bounded set `A` of
diameter at most 1 has an image under some isometry of the plane (rotations,
translations and reflections) inside `U`. Asking this of sets of diameter at
most 1 rather than exactly 1 changes nothing: a set of diameter `d < 1`
extends to a set of constant width `d` (Vrečica 1981), and adding a disk of
radius `(1 - d) / 2` to that gives a set of constant width 1 containing it.

The area is the Lebesgue measure `volume U`. A smallest convex universal cover
exists (Kelly and Weiss 1979), but the bounds are stated for the infimum, so
that the statements don't depend on it: a lower bound says every universal
cover has at least that area, and an upper bound that some universal cover
has at most that area. The variant without convexity, which has a smaller
infimum (Duff 1980), isn't covered here.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals such as `0.832`. A
certificate for `lebesgue-universal-cover` with lower bound `radical terms d`
must prove `RadicalLowerBound terms d`, and one with that upper bound must
prove `RadicalUpperBound terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.LebesgueCover

open MeasureTheory

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `U` is a universal cover: it's convex, and every bounded set of diameter
at most 1 is congruent to a subset of it. -/
def IsUniversalCover (U : Set Plane) : Prop :=
  Convex ℝ U ∧ ∀ A : Set Plane, Bornology.IsBounded A → Metric.diam A ≤ 1 →
    ∃ f : Plane ≃ᵢ Plane, f '' A ⊆ U

/-- The Lebesgue universal covering constant is at least `a`: every universal
cover has area at least `a`. -/
def LowerBound (a : ℝ) : Prop :=
  ∀ U, IsUniversalCover U → ENNReal.ofReal a ≤ volume U

/-- The Lebesgue universal covering constant is at most `a`: `a ≥ 0`, and some
universal cover has area at most `a`. -/
def UpperBound (a : ℝ) : Prop :=
  0 ≤ a ∧ ∃ U, IsUniversalCover U ∧ volume U ≤ ENNReal.ofReal a

/-- The Lebesgue universal covering constant is at least `radical terms d`. -/
def RadicalLowerBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound (radical terms d)

/-- The Lebesgue universal covering constant is at most `radical terms d`. -/
def RadicalUpperBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {a b : ℝ} (hl : LowerBound a)
    (hu : UpperBound b) : a ≤ b := by
  obtain ⟨hb, U, hU, hUb⟩ := hu
  exact (ENNReal.ofReal_le_ofReal_iff hb).1 ((hl U hU).trans hUb)

end LeapsInBounds.LebesgueCover
