module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Packing unit squares in a square

Formal statements of bounds on `s(n)`: the side of the smallest square into
which `n` unit squares can be packed.

A unit square is the image of `[0, 1]²` under an isometry of the plane (so it
can be translated and rotated), and a packing places `n` of them inside
`[0, s]²` with pairwise disjoint interiors.

Bounds are stated for values `√m` with `m` a natural number, which covers the
integers (`m = k²`) and the area bound `√n`. A certificate for
`square-packing-in-square-{n}` with lower bound `√m` must prove
`SqrtLowerBound n m`, and one with upper bound `√m` must prove
`SqrtUpperBound n m`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.SquarePacking

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The square `[0, s]²`. -/
def square (s : ℝ) : Set Plane := {x | ∀ i, 0 ≤ x i ∧ x i ≤ s}

/-- `f` places `n` unit squares in `[0, s]²` with pairwise disjoint interiors. -/
def IsPacking {n : ℕ} (s : ℝ) (f : Fin n → Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  0 ≤ s ∧ (∀ i, f i '' square 1 ⊆ square s) ∧
    ∀ i j, i ≠ j → Disjoint (interior (f i '' square 1)) (interior (f j '' square 1))

/-- `s(n) ≥ a`: no packing of `n` unit squares fits in a square of side less
than `a`. -/
def LowerBound (n : ℕ) (a : ℝ) : Prop :=
  ∀ s, ∀ f : Fin n → Plane ≃ᵃⁱ[ℝ] Plane, IsPacking s f → a ≤ s

/-- `s(n) ≤ a`: `n` unit squares can be packed in a square of side `a`. -/
def UpperBound (n : ℕ) (a : ℝ) : Prop :=
  ∃ f : Fin n → Plane ≃ᵃⁱ[ℝ] Plane, IsPacking a f

/-- `s(n) ≥ √m`. -/
def SqrtLowerBound (n m : ℕ) : Prop := LowerBound n (Real.sqrt m)

/-- `s(n) ≤ √m`. -/
def SqrtUpperBound (n m : ℕ) : Prop := UpperBound n (Real.sqrt m)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n : ℕ} {a b : ℝ} (hl : LowerBound n a)
    (hu : UpperBound n b) : a ≤ b := by
  obtain ⟨f, hf⟩ := hu
  exact hl b f hf

end LeapsInBounds.SquarePacking
