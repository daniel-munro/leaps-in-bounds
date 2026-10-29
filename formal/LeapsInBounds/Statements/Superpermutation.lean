module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.List.Infix

/-!
# Minimal superpermutations

Formal statements of bounds on `L(n)`: the shortest length of a string that
contains every permutation of `n` symbols as a contiguous substring.

A certificate for `minimal-superpermutation-{n}` with lower bound `m` must
prove `LowerBound n m`, and one with upper bound `m` must prove
`UpperBound n m`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Superpermutation

/-- `s` contains every permutation of `n` symbols as a contiguous substring. -/
def IsSuperpermutation (n : ℕ) (s : List (Fin n)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), List.ofFn p <:+: s

/-- `L(n) ≥ m`: every superpermutation on `n` symbols has length at least `m`. -/
def LowerBound (n m : ℕ) : Prop :=
  ∀ s : List (Fin n), IsSuperpermutation n s → m ≤ s.length

/-- `L(n) ≤ m`: some superpermutation on `n` symbols has length at most `m`. -/
def UpperBound (n m : ℕ) : Prop :=
  ∃ s : List (Fin n), IsSuperpermutation n s ∧ s.length ≤ m

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n m m' : ℕ} (hl : LowerBound n m)
    (hu : UpperBound n m') : m ≤ m' := by
  obtain ⟨s, hs, hlen⟩ := hu
  exact (hl s hs).trans hlen

end LeapsInBounds.Superpermutation
