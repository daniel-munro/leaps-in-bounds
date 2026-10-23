module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Ramsey numbers

Formal statements of bounds on the Ramsey number `R(r, s)`: the smallest `n`
such that every graph on `n` vertices has a clique of size `r` or an
independent set of size `s`. (A two-coloring of the edges of `K_n` is a graph
together with its complement.)

A certificate for `ramsey-{r}-{s}` with lower bound `n` must prove
`LowerBound r s n`, and one with upper bound `n` must prove `UpperBound r s n`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Ramsey

open SimpleGraph

/-- `R(r, s) ≥ n`: some graph on `n - 1` vertices has no clique of size `r` and
no independent set of size `s`. -/
def LowerBound (r s n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin (n - 1)), G.CliqueFree r ∧ Gᶜ.CliqueFree s

/-- `R(r, s) ≤ n`: every graph on `n` vertices has a clique of size `r` or an
independent set of size `s`. -/
def UpperBound (r s n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {r s m n : ℕ} (hl : LowerBound r s m)
    (hu : UpperBound r s n) : m ≤ n := by
  by_contra h
  obtain ⟨G, hr, hs⟩ := hl
  let f := Embedding.comap (Fin.castLEEmb (show n ≤ m - 1 by omega)) G
  rcases hu (G.comap (Fin.castLEEmb (show n ≤ m - 1 by omega))) with h' | h'
  · exact h' (hr.comap f.isContained)
  · exact h' (hs.comap (Embedding.complEquiv f).isContained)

end LeapsInBounds.Ramsey
