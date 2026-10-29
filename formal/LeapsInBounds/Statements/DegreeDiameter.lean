module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Data.Set.Card

/-!
# Degree-diameter problem

Formal statements of bounds on `N(d, k)`: the largest number of vertices in a
graph of maximum degree `d` and diameter `k`.

A certificate for `degree-diameter-{d}-{k}` with lower bound `n` must prove
`LowerBound d k n`, and one with upper bound `n` must prove `UpperBound d k n`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.DegreeDiameter

open SimpleGraph

/-- `G` has maximum degree at most `d` and diameter at most `k`: every two
vertices are joined by a walk of length at most `k`. -/
def HasDegreeDiameter {V : Type*} (G : SimpleGraph V) (d k : ℕ) : Prop :=
  (∀ v, (G.neighborSet v).ncard ≤ d) ∧ ∀ u v, ∃ p : G.Walk u v, p.length ≤ k

/-- `N(d, k) ≥ n`: some graph on `n` vertices has maximum degree at most `d`
and diameter at most `k`. -/
def LowerBound (d k n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), HasDegreeDiameter G d k

/-- `N(d, k) ≤ n`: every graph with maximum degree at most `d` and diameter at
most `k` has at most `n` vertices. -/
def UpperBound (d k n : ℕ) : Prop :=
  ∀ m, ∀ G : SimpleGraph (Fin m), HasDegreeDiameter G d k → m ≤ n

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {d k m n : ℕ} (hl : LowerBound d k m)
    (hu : UpperBound d k n) : m ≤ n := by
  obtain ⟨G, hG⟩ := hl
  exact hu m G hG

end LeapsInBounds.DegreeDiameter
