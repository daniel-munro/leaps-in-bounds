module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Heilbronn triangle problem

Formal statements of bounds on the Heilbronn numbers: the largest possible
area of the smallest triangle formed by three of `n` points in a region.

* `heilbronn-square-{n}`, `H(n)`: points in the unit square `[0, 1]²`.
* `heilbronn-triangle-{n}`, `Δ(n)`: points in a triangle, with the area of the
  smallest triangle as a fraction of the area of the region. Every triangle is
  the image of every other under an affine map, which scales all areas by the
  same factor, so one is used: the triangle with vertices `(0, 0)`, `(1, 0)`
  and `(0, 1)`, of area `1/2`.

The families start at `n = 3`: with fewer points there are no triangles, and
no upper bound holds. Points needn't be distinct, but if two coincide, every
triangle containing both has area 0.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals such as `0.0271`. A
certificate for `heilbronn-square-{n}` with lower bound `radical terms d` must
prove `SquareRadicalLowerBound n terms d`, and so on for the upper bound and
for `heilbronn-triangle-{n}` (`TriangleRadicalLowerBound`).

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Heilbronn

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The area of the triangle with vertices `p`, `q` and `r`: half the absolute
value of the determinant of `q - p` and `r - p`. -/
noncomputable def area (p q r : Plane) : ℝ :=
  |(q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)| / 2

/-- The unit square `[0, 1]²`, of area 1. -/
def unitSquare : Set Plane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}

/-- The triangle with vertices `(0, 0)`, `(1, 0)` and `(0, 1)`, of area `1/2`. -/
def unitTriangle : Set Plane :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

/-- `x` places `n` points in `K`, each three of them forming a triangle of
area at least `a`. -/
def IsSpread {n : ℕ} (K : Set Plane) (a : ℝ) (x : Fin n → Plane) : Prop :=
  (∀ i, x i ∈ K) ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → a ≤ area (x i) (x j) (x k)

/-- Some `n` points in `K` have each three forming a triangle of area at least
`a`. -/
def LowerBound (K : Set Plane) (n : ℕ) (a : ℝ) : Prop :=
  ∃ x : Fin n → Plane, IsSpread K a x

/-- Whenever `n` points in `K` have each three forming a triangle of area at
least `b`, `b ≤ a`. -/
def UpperBound (K : Set Plane) (n : ℕ) (a : ℝ) : Prop :=
  ∀ b, ∀ x : Fin n → Plane, IsSpread K b x → b ≤ a

/-- `H(n) ≥ radical terms d`. -/
def SquareRadicalLowerBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound unitSquare n (radical terms d)

/-- `H(n) ≤ radical terms d`. -/
def SquareRadicalUpperBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound unitSquare n (radical terms d)

/-- `Δ(n) ≥ radical terms d`: areas in the triangle of area `1/2`, as a
fraction of its area. -/
def TriangleRadicalLowerBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound unitTriangle n (radical terms d / 2)

/-- `Δ(n) ≤ radical terms d`. -/
def TriangleRadicalUpperBound (n : ℕ) (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound unitTriangle n (radical terms d / 2)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {K : Set Plane} {n : ℕ} {a b : ℝ}
    (hl : LowerBound K n a) (hu : UpperBound K n b) : a ≤ b := by
  obtain ⟨x, hx⟩ := hl
  exact hu a x hx

end LeapsInBounds.Heilbronn
