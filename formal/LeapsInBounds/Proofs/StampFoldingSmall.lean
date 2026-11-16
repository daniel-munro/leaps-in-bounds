module

public import LeapsInBounds.Statements.Folding
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Foldings of at most three stamps

An `m × n` map has at most `(m n)!` foldings, one for each order of its cells.
For a strip of at most three stamps, every order is a folding, so this bound is
the number of foldings: `1`, `2` and `6`.
-/

public section

namespace LeapsInBounds.Proofs.StampFoldingSmall

open Folding

/-- An `m × n` map has at most `(m n)!` foldings. -/
theorem count_le (m n : ℕ) : count m n ≤ (m * n).factorial := by
  unfold count
  calc Nat.card {ℓ : Fin m × Fin n ≃ Fin (m * n) // IsFolding ℓ}
      ≤ Nat.card (Fin m × Fin n ≃ Fin (m * n)) := Finite.card_subtype_le _
    _ = (m * n).factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_equiv (Fintype.equivOfCardEq (by simp))]
      simp

theorem upper_one : StampUpperBound 1 1 := by
  simpa [StampUpperBound, UpperBound] using count_le 1 1

theorem upper_two : StampUpperBound 2 2 := by
  simpa [StampUpperBound, UpperBound] using count_le 1 2

theorem upper_three : StampUpperBound 3 6 := by
  simpa [StampUpperBound, UpperBound, Nat.factorial] using count_le 1 3

end LeapsInBounds.Proofs.StampFoldingSmall
