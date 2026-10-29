module

public import Mathlib.Data.Fin.Basic

/-!
# Van der Waerden numbers

Formal statements of bounds on the van der Waerden number `W(r, k)`: the
smallest `n` such that every coloring of `n` consecutive integers with `r`
colors has a monochromatic arithmetic progression of length `k`. The integers
are taken to be `0, …, n - 1`, and only the colors of those matter.

A certificate for `van-der-waerden-{r}-{k}` with lower bound `n` must prove
`LowerBound r k n`, and one with upper bound `n` must prove `UpperBound r k n`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.VanDerWaerden

/-- The coloring `c` has a monochromatic arithmetic progression of length `k`
within `0, …, n - 1`. -/
def HasMonoAP (r k n : ℕ) (c : ℕ → Fin r) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < n ∧ ∀ i < k, c (a + i * d) = c a

/-- `W(r, k) ≥ n`: some `r`-coloring of `n - 1` consecutive integers has no
monochromatic arithmetic progression of length `k`. -/
def LowerBound (r k n : ℕ) : Prop :=
  ∃ c : ℕ → Fin r, ¬ HasMonoAP r k (n - 1) c

/-- `W(r, k) ≤ n`: every `r`-coloring of `n` consecutive integers has a
monochromatic arithmetic progression of length `k`. -/
def UpperBound (r k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, HasMonoAP r k n c

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {r k m n : ℕ} (hl : LowerBound r k m)
    (hu : UpperBound r k n) : m ≤ n := by
  by_contra h
  obtain ⟨c, hc⟩ := hl
  obtain ⟨a, d, hd, hlt, hmono⟩ := hu c
  exact hc ⟨a, d, hd, by omega, hmono⟩

end LeapsInBounds.VanDerWaerden
