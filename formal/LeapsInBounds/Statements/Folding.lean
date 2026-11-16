module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Folding maps and strips of stamps

Formal statements of bounds on the number of ways to fold an `m × n` map, a
rectangle ruled into `m n` unit cells, into a stack of cells of the size of one
cell, and of a strip of `n` stamps, the `1 × n` map.

A folding is counted by its final stack: the order of the cells from the
bottom up, an `Equiv` from the cells to the levels `Fin (m n)`, with the cells
labeled so that turning the stack over or rotating it gives a different
folding. This is the count of OEIS A000136 for strips of stamps, A001415 for
`2 × n` maps and A001418 for `n × n` maps.

When the map is folded flat, all the creases between rows `i` and `i + 1` end
up on the same edge of the stack, and those between rows `i + 1` and `i + 2`
on the opposite edge, and the same for columns, so the creases are on four
edges, by direction and parity. Each crease joins the levels of the two cells
it's between, and two creases on the same edge can't cross: their intervals of
levels are nested or disjoint. A stack is a folding exactly when this holds
for every two creases on the same edge. This combinatorial characterization
(due to Koehler for strips and Lunnon for maps) is what's stated here, rather
than a geometric model of paper.

A certificate for `map-folding-{m}-{n}` with lower bound `N` must prove
`LowerBound m n N`, and one with upper bound `N` must prove
`UpperBound m n N`. For `stamp-folding-{n}`, they are `StampLowerBound n N`
and `StampUpperBound n N`, the same for the `1 × n` map.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.Folding

/-- The intervals of levels between `a` and `b` and between `c` and `d`
(in either order) cross: each contains exactly one end of the other. -/
def Cross (a b c d : ℕ) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
    (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

/-- The stack `ℓ` of the cells of an `m × n` map, giving the level of each
cell (row, column), is a folding: no two creases on the same edge cross. The
creases between `a` and `b` in rows `i` and `i + 1`, and between `c` and `d`
in rows `i'` and `i' + 1`, are on the same edge when `i` and `i'` have the
same parity, and the same for columns. -/
def IsFolding {m n : ℕ} (ℓ : Fin m × Fin n ≃ Fin (m * n)) : Prop :=
  (∀ a b c d : Fin m × Fin n, b.1.val = a.1.val + 1 → b.2 = a.2 →
    d.1.val = c.1.val + 1 → d.2 = c.2 → a.1.val % 2 = c.1.val % 2 →
    ¬Cross (ℓ a) (ℓ b) (ℓ c) (ℓ d)) ∧
  (∀ a b c d : Fin m × Fin n, b.2.val = a.2.val + 1 → b.1 = a.1 →
    d.2.val = c.2.val + 1 → d.1 = c.1 → a.2.val % 2 = c.2.val % 2 →
    ¬Cross (ℓ a) (ℓ b) (ℓ c) (ℓ d))

/-- The number of foldings of an `m × n` map. -/
noncomputable def count (m n : ℕ) : ℕ :=
  Nat.card {ℓ : Fin m × Fin n ≃ Fin (m * n) // IsFolding ℓ}

/-- There are at least `N` foldings of an `m × n` map. -/
def LowerBound (m n N : ℕ) : Prop :=
  N ≤ count m n

/-- There are at most `N` foldings of an `m × n` map. -/
def UpperBound (m n N : ℕ) : Prop :=
  count m n ≤ N

/-- There are at least `N` foldings of a strip of `n` stamps. -/
def StampLowerBound (n N : ℕ) : Prop :=
  LowerBound 1 n N

/-- There are at most `N` foldings of a strip of `n` stamps. -/
def StampUpperBound (n N : ℕ) : Prop :=
  UpperBound 1 n N

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {m n a b : ℕ} (hl : LowerBound m n a)
    (hu : UpperBound m n b) : a ≤ b :=
  hl.trans hu

end LeapsInBounds.Folding
