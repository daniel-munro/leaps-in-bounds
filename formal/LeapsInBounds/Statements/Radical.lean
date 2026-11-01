module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sums of square roots

Some bounds are sums of rational multiples of square roots, such as
`4 + 2√3 + 4√6 / 3`. Certificates state them as `radical terms d`, the
real number `(c₁ √m₁ + ⋯ + cₖ √mₖ) / d` for `terms = [(c₁, m₁), …, (cₖ, mₖ)]`.
The checker writes a value with the `mᵢ` squarefree and increasing (`1` for
the rational part), integer `cᵢ`, and `d` the least common denominator, so
`4 + 2√3 + 4√6 / 3` is `radical [(12, 1), (6, 3), (4, 6)] 3`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds

/-- `(c₁ √m₁ + ⋯ + cₖ √mₖ) / d` for `terms = [(c₁, m₁), …, (cₖ, mₖ)]`. -/
noncomputable def radical (terms : List (ℤ × ℕ)) (d : ℕ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * Real.sqrt t.2).sum / d

end LeapsInBounds
