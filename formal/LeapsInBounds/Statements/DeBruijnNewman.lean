module

public import LeapsInBounds.Statements.Radical
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The de Bruijn–Newman constant

Formal statements of bounds on the de Bruijn–Newman constant `Λ`. For real
`t` and complex `z`, let

  `H(t, z) = ∫₀^∞ e^(t u²) Φ(u) cos(z u) du`, where
  `Φ(u) = ∑_{k ≥ 1} (2π² k⁴ e^(9u) - 3π k² e^(5u)) e^(-π k² e^(4u))`.

De Bruijn and Newman showed that there is a constant `Λ` such that `H(t, ·)`
has only real zeros exactly when `t ≥ Λ`. The Riemann hypothesis is equivalent
to `Λ ≤ 0`, and Rodgers and Tao proved `Λ ≥ 0`. The bounds are stated
directly in terms of the zeros, so they don't depend on the existence of `Λ`.
The integral converges absolutely for all `t` and `z`, since `Φ` decays
faster than any exponential.

Bounds are stated for values that are sums of rational multiples of square
roots (see `LeapsInBounds.radical`), including rationals such as `0.2`, which
is `radical [(1, 1)] 5`. A certificate for `debruijn-newman` with lower bound
`radical terms d` must prove `RadicalLowerBound terms d`, and one with that
upper bound must prove `RadicalUpperBound terms d`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.DeBruijnNewman

open Real

/-- `Φ(u) = ∑_{k ≥ 1} (2π² k⁴ e^(9u) - 3π k² e^(5u)) e^(-π k² e^(4u))`. -/
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' j : ℕ, ((2 * π ^ 2 * ((j : ℝ) + 1) ^ 4 * exp (9 * u) -
      3 * π * ((j : ℝ) + 1) ^ 2 * exp (5 * u)) * exp (-π * ((j : ℝ) + 1) ^ 2 * exp (4 * u)))

/-- `H(t, z) = ∫₀^∞ e^(t u²) Φ(u) cos(z u) du`. -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((exp (t * u ^ 2) * Φ u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `Λ ≥ a`: for every `t < a`, `H(t, ·)` has a zero that isn't real. -/
def LowerBound (a : ℝ) : Prop :=
  ∀ t < a, ∃ z : ℂ, z.im ≠ 0 ∧ H t z = 0

/-- `Λ ≤ a`: for every `t ≥ a`, every zero of `H(t, ·)` is real. -/
def UpperBound (a : ℝ) : Prop :=
  ∀ t ≥ a, ∀ z : ℂ, H t z = 0 → z.im = 0

/-- `Λ ≥ radical terms d`. -/
def RadicalLowerBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  LowerBound (radical terms d)

/-- `Λ ≤ radical terms d`. -/
def RadicalUpperBound (terms : List (ℤ × ℕ)) (d : ℕ) : Prop :=
  UpperBound (radical terms d)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {a b : ℝ} (hl : LowerBound a)
    (hu : UpperBound b) : a ≤ b := by
  by_contra h
  obtain ⟨z, hz, hH⟩ := hl b (lt_of_not_ge h)
  exact hz (hu b le_rfl z hH)

end LeapsInBounds.DeBruijnNewman
