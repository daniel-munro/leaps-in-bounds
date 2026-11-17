module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The moving sofa problem

Formal statements of bounds on the moving sofa constant: the largest area of
a connected shape in the plane that can be moved around a right-angled corner
in a hallway of width 1.

The hallway is the union of a horizontal arm `{(x, y) | x ≤ 1, 0 ≤ y ≤ 1}`
and a vertical arm `{(x, y) | 0 ≤ x ≤ 1, y ≤ 1}`, meeting in the unit square
at the corner. A shape `S` moves around the corner if a continuous family of
rotations and translations, at times `t ∈ [0, 1]`, keeps it in the hallway, and
takes it from the horizontal arm left of the corner (`x ≤ 0`) at time `0` to
the vertical arm below it (`y ≤ 0`) at time `1`. Reflections aren't needed,
since a reflected shape moves around the corner when its mirror image does.

The area is the Lebesgue measure `volume S`, which for a set that isn't
measurable is its outer measure. A set moves around the corner just when its
closure does (the hallway and the end regions are closed), so this changes
nothing.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals such as `2.2195`. A
certificate for `moving-sofa` with lower bound `radical terms d` must prove
`RadicalLowerBound terms d`, and one with that upper bound must prove
`RadicalUpperBound terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.MovingSofa

open Real MeasureTheory

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The hallway: a horizontal arm and a vertical arm of width 1. -/
def hallway : Set Plane :=
  {p | (p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∨ (0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1)}

/-- The horizontal arm left of the corner, where a sofa starts. -/
def start : Set Plane :=
  {p | p 0 ≤ 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}

/-- The vertical arm below the corner, where a sofa ends. -/
def finish : Set Plane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 0}

/-- The rotation by `θ` followed by the translation by `v`. -/
noncomputable def motion (θ : ℝ) (v : Plane) (p : Plane) : Plane :=
  !₂[cos θ * p 0 - sin θ * p 1 + v 0, sin θ * p 0 + cos θ * p 1 + v 1]

/-- `S` is a moving sofa: it's connected, and rotations by `θ t` followed by
translations by `v t`, continuous in `t`, keep it in the hallway for
`t ∈ [0, 1]`, starting left of the corner and finishing below it. -/
def IsMovingSofa (S : Set Plane) : Prop :=
  IsConnected S ∧ ∃ θ : ℝ → ℝ, ∃ v : ℝ → Plane, Continuous θ ∧ Continuous v ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, motion (θ t) (v t) '' S ⊆ hallway) ∧
    motion (θ 0) (v 0) '' S ⊆ start ∧ motion (θ 1) (v 1) '' S ⊆ finish

/-- The moving sofa constant is at least `a`: some moving sofa has area at
least `a`. -/
def LowerBound (a : ℝ) : Prop :=
  ∃ S, IsMovingSofa S ∧ ENNReal.ofReal a ≤ volume S

/-- The moving sofa constant is at most `a`: `a ≥ 0`, and every moving sofa
has area at most `a`. -/
def UpperBound (a : ℝ) : Prop :=
  0 ≤ a ∧ ∀ S, IsMovingSofa S → volume S ≤ ENNReal.ofReal a

/-- The moving sofa constant is at least `radical terms d`. -/
def RadicalLowerBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound (radical terms d)

/-- The moving sofa constant is at most `radical terms d`. -/
def RadicalUpperBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {a b : ℝ} (hl : LowerBound a)
    (hu : UpperBound b) : a ≤ b := by
  obtain ⟨S, hS, ha⟩ := hl
  exact (ENNReal.ofReal_le_ofReal_iff hu.1).1 (ha.trans (hu.2 S hS))

end LeapsInBounds.MovingSofa
