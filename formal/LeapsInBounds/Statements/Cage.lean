module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Card

/-!
# Cages

Formal statements of bounds on the cage order `n(k, g)`: the smallest number
of vertices in a `k`-regular graph of girth `g`.

A certificate for `cage-{k}-{g}` with lower bound `n` must prove
`LowerBound k g n`, and one with upper bound `n` must prove `UpperBound k g n`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Cage

open SimpleGraph

/-- `G` is `k`-regular with girth `g`. -/
def IsRegularOfGirth {V : Type*} (G : SimpleGraph V) (k g : ℕ) : Prop :=
  (∀ v, (G.neighborSet v).ncard = k) ∧ G.egirth = g

/-- `n(k, g) ≥ n`: no graph on fewer than `n` vertices is `k`-regular with
girth `g`. -/
def LowerBound (k g n : ℕ) : Prop :=
  ∀ m < n, ∀ G : SimpleGraph (Fin m), ¬ IsRegularOfGirth G k g

/-- `n(k, g) ≤ n`: some graph on `n` vertices is `k`-regular with girth `g`. -/
def UpperBound (k g n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), IsRegularOfGirth G k g

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {k g m n : ℕ} (hl : LowerBound k g m)
    (hu : UpperBound k g n) : m ≤ n := by
  by_contra h
  obtain ⟨G, hG⟩ := hu
  exact hl n (by omega) G hG

end LeapsInBounds.Cage
