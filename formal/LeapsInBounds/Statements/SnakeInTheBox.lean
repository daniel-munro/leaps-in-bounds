module

public import Mathlib.InformationTheory.Hamming

/-!
# Snake-in-the-box and coil-in-the-box

Formal statements of bounds on the longest snake and the longest coil in the
`n`-dimensional hypercube `Q_n`, whose vertices are the binary vectors of
length `n`, two of them adjacent if they differ in exactly one coordinate.

A snake is an induced path in `Q_n`: a path whose vertices are adjacent only
when they're consecutive on the path. A coil is an induced cycle. Lengths are
numbers of edges.

A certificate for `snake-in-the-box-{n}` with lower bound `L` must prove
`LowerBound n L`, and one with upper bound `L` must prove `UpperBound n L`.
Likewise for `coil-in-the-box-{n}`, with `CoilLowerBound` and
`CoilUpperBound`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.SnakeInTheBox

/-- Two vertices of `Q_n` are adjacent: they differ in exactly one coordinate. -/
def Adj {n : ℕ} (u v : Fin n → Bool) : Prop :=
  hammingDist u v = 1

/-- `p` is a snake of length `L` in `Q_n`: its `L + 1` vertices are distinct,
and two of them are adjacent exactly when they're consecutive. -/
def IsSnake {n L : ℕ} (p : Fin (L + 1) → Fin n → Bool) : Prop :=
  Function.Injective p ∧
    ∀ i j : Fin (L + 1), Adj (p i) (p j) ↔ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i

/-- `c` is a coil of length `L` in `Q_n`: its `L ≥ 3` vertices are distinct,
and two of them are adjacent exactly when they're consecutive around the
cycle. -/
def IsCoil {n L : ℕ} (c : Fin L → Fin n → Bool) : Prop :=
  3 ≤ L ∧ Function.Injective c ∧
    ∀ i j : Fin L, Adj (c i) (c j) ↔ ((i : ℕ) + 1) % L = j ∨ ((j : ℕ) + 1) % L = i

/-- The longest snake in `Q_n` has length at least `L`. -/
def LowerBound (n L : ℕ) : Prop :=
  ∃ m, L ≤ m ∧ ∃ p : Fin (m + 1) → Fin n → Bool, IsSnake p

/-- Every snake in `Q_n` has length at most `L`. -/
def UpperBound (n L : ℕ) : Prop :=
  ∀ m, ∀ p : Fin (m + 1) → Fin n → Bool, IsSnake p → m ≤ L

/-- The longest coil in `Q_n` has length at least `L`. -/
def CoilLowerBound (n L : ℕ) : Prop :=
  ∃ m, L ≤ m ∧ ∃ c : Fin m → Fin n → Bool, IsCoil c

/-- Every coil in `Q_n` has length at most `L`. -/
def CoilUpperBound (n L : ℕ) : Prop :=
  ∀ m, ∀ c : Fin m → Fin n → Bool, IsCoil c → m ≤ L

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {n k L : ℕ} (hl : LowerBound n k)
    (hu : UpperBound n L) : k ≤ L := by
  obtain ⟨m, hm, p, hp⟩ := hl
  have := hu m p hp
  omega

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem CoilLowerBound.le_of_coilUpperBound {n k L : ℕ} (hl : CoilLowerBound n k)
    (hu : CoilUpperBound n L) : k ≤ L := by
  obtain ⟨m, hm, c, hc⟩ := hl
  have := hu m c hc
  omega

end LeapsInBounds.SnakeInTheBox
