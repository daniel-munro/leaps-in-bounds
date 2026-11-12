module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Real.Basic

/-!
# The rectilinear crossing number of the complete graph

Formal statements of bounds on `cr̄(Kₙ)`: the fewest crossings in a drawing of
the complete graph `Kₙ` in the plane with straight edges, its vertices in
general position (no three on a line).

A drawing is given by the positions `p : Fin n → ℝ × ℝ` of the vertices. Two
edges cross if they share no vertex and their segments meet. With no three
vertices on a line, they then meet in one point inside both.

A certificate for `rectilinear-crossing-{n}` with lower bound `c` must prove
`LowerBound n c`, and one with upper bound `c` must prove `UpperBound n c`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.RectilinearCrossing

/-- The points `p i` are distinct, and no three of them are on a line. -/
def GeneralPosition {n : ℕ} (p : Fin n → ℝ × ℝ) : Prop :=
  Function.Injective p ∧
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ ({p i, p j, p k} : Set (ℝ × ℝ))

/-- The pairs of crossing edges `{a, b}` and `{c, d}` of the straight-line
drawing of `Kₙ` with vertices `p`, each pair listed once: as `(a, b, c, d)`
with `a < b`, `c < d` and `a < c`. -/
def crossingPairs {n : ℕ} (p : Fin n → ℝ × ℝ) : Set (Fin n × Fin n × Fin n × Fin n) :=
  {q | q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.1 < q.2.2.1 ∧
    q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧
    (segment ℝ (p q.1) (p q.2.1) ∩ segment ℝ (p q.2.2.1) (p q.2.2.2)).Nonempty}

/-- The number of crossings in the straight-line drawing of `Kₙ` with
vertices `p`. -/
noncomputable def crossings {n : ℕ} (p : Fin n → ℝ × ℝ) : ℕ :=
  (crossingPairs p).ncard

/-- `cr̄(Kₙ) ≥ c`: every straight-line drawing of `Kₙ` with its vertices in
general position has at least `c` crossings. -/
def LowerBound (n c : ℕ) : Prop :=
  ∀ p : Fin n → ℝ × ℝ, GeneralPosition p → c ≤ crossings p

/-- `cr̄(Kₙ) ≤ c`: some straight-line drawing of `Kₙ` with its vertices in
general position has at most `c` crossings. -/
def UpperBound (n c : ℕ) : Prop :=
  ∃ p : Fin n → ℝ × ℝ, GeneralPosition p ∧ crossings p ≤ c

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k c : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n c) : k ≤ c := by
  obtain ⟨p, hp, hc⟩ := hu
  exact (hl p hp).trans hc

end LeapsInBounds.RectilinearCrossing
