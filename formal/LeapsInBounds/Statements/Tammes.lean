module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The Tammes problem

Formal statements of bounds on `T(n)`: the largest possible least angle, in
degrees, between two of `n` points on the unit sphere in `ℝ³`. The angle
between unit vectors `x` and `y` is `arccos ⟪x, y⟫`
(`InnerProductGeometry.angle`), in radians, so `a` degrees is `a * π / 180`.

The family starts at `n = 2`: with fewer points there are no angles, and no
upper bound holds.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals such as `57.1367`. A
certificate for `tammes-{n}` with lower bound `radical terms d` must prove
`RadicalLowerBound n terms d`, and one with that upper bound must prove
`RadicalUpperBound n terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Tammes

open Real

/-- Euclidean space `ℝ³`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- `x` places `n` points on the unit sphere, each two at an angle of at least
`a` degrees. -/
def IsSeparated {n : ℕ} (a : ℝ) (x : Fin n → Space) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧
    ∀ i j, i ≠ j → a * π / 180 ≤ InnerProductGeometry.angle (x i) (x j)

/-- `T(n) ≥ a`: some `n` points on the unit sphere are each at least `a`
degrees apart. -/
def LowerBound (n : ℕ) (a : ℝ) : Prop :=
  ∃ x : Fin n → Space, IsSeparated a x

/-- `T(n) ≤ a`: whenever `n` points on the unit sphere are each at least `b`
degrees apart, `b ≤ a`. -/
def UpperBound (n : ℕ) (a : ℝ) : Prop :=
  ∀ b, ∀ x : Fin n → Space, IsSeparated b x → b ≤ a

/-- `T(n) ≥ radical terms d`. -/
def RadicalLowerBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound n (radical terms d)

/-- `T(n) ≤ radical terms d`. -/
def RadicalUpperBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound n (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n : ℕ} {a b : ℝ} (hl : LowerBound n a)
    (hu : UpperBound n b) : a ≤ b := by
  obtain ⟨x, hx⟩ := hl
  exact hu a x hx

end LeapsInBounds.Tammes
