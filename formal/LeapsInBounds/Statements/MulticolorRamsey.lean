module

public import Mathlib.Data.Fin.Basic

/-!
# Multicolor Ramsey numbers for triangles

Formal statements of bounds on the multicolor Ramsey number
`R_k(3) = R(3, 3, …, 3)`: the smallest `n` such that every coloring of the
edges of the complete graph `K_n` with `k` colors has a monochromatic
triangle.

A certificate for `multicolor-ramsey-triangle-{k}` with lower bound `n` must
prove `LowerBound k n`, and one with upper bound `n` must prove
`UpperBound k n`.

An edge coloring of `K_n` is a function `c : Fin n → Fin n → Fin k`, where the
edge between `a < b` has color `c a b`. Only the values with `a < b` matter.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.MulticolorRamsey

/-- The edge coloring `c` of `K_n` has a monochromatic triangle. -/
def HasMonoTriangle (k n : ℕ) (c : Fin n → Fin n → Fin k) : Prop :=
  ∃ a b d : Fin n, a < b ∧ b < d ∧ c a b = c a d ∧ c a b = c b d

/-- `R_k(3) ≥ n`: some coloring of the edges of `K_{n - 1}` with `k` colors has
no monochromatic triangle. -/
def LowerBound (k n : ℕ) : Prop :=
  ∃ c : Fin (n - 1) → Fin (n - 1) → Fin k, ¬ HasMonoTriangle k (n - 1) c

/-- `R_k(3) ≤ n`: every coloring of the edges of `K_n` with `k` colors has a
monochromatic triangle. -/
def UpperBound (k n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Fin k, HasMonoTriangle k n c

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {k m n : ℕ} (hl : LowerBound k m)
    (hu : UpperBound k n) : m ≤ n := by
  by_contra h
  obtain ⟨c, hc⟩ := hl
  have hle : n ≤ m - 1 := by omega
  obtain ⟨a, b, d, hab, hbd, h1, h2⟩ :=
    hu (fun x y => c (Fin.castLE hle x) (Fin.castLE hle y))
  exact hc ⟨Fin.castLE hle a, Fin.castLE hle b, Fin.castLE hle d, hab, hbd, h1, h2⟩

end LeapsInBounds.MulticolorRamsey
