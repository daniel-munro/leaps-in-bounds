module

public import LeapsInBounds.Statements.Superpermutation
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.OfFn

/-!
# Counting lower bound for superpermutations

A superpermutation on `n` symbols has length at least `n! + n - 1`: the `n!`
permutations occur as distinct windows of length `n`, which start at distinct
positions, of which there are `length - n + 1`.
-/

public section

namespace LeapsInBounds.Proofs.SuperpermutationCounting

open Finset

/-- `L(n) ≥ n! + n - 1`. -/
theorem lower (n : ℕ) : Superpermutation.LowerBound n (n.factorial + n - 1) := by
  intro s hs
  -- the window of length `n` at each start position
  have hsub : (univ.image fun p : Equiv.Perm (Fin n) => List.ofFn p) ⊆
      (range (s.length - n + 1)).image fun i => (s.drop i).take n := by
    intro l hl
    obtain ⟨p, -, rfl⟩ := mem_image.mp hl
    obtain ⟨a, b, hab⟩ := hs p
    have hlen : s.length = a.length + n + b.length := by
      rw [← hab]; simp; omega
    refine mem_image.mpr ⟨a.length, mem_range.mpr (by omega), ?_⟩
    rw [← hab, List.append_assoc, List.drop_left, List.take_left' (by simp)]
  have hcard := (card_le_card hsub).trans card_image_le
  rw [card_image_of_injective _ (fun p q h => DFunLike.coe_injective (List.ofFn_injective h)), card_univ, Fintype.card_perm,
    Fintype.card_fin, card_range] at hcard
  -- some window exists, so `n ≤ length`
  obtain ⟨a, b, hab⟩ := hs 1
  have hlen : s.length = a.length + n + b.length := by
    rw [← hab]; simp; omega
  have := n.factorial_pos
  omega

theorem lower_1 : Superpermutation.LowerBound 1 1 := by simpa [Nat.factorial] using lower 1
theorem lower_2 : Superpermutation.LowerBound 2 3 := by simpa [Nat.factorial] using lower 2
theorem lower_3 : Superpermutation.LowerBound 3 8 := by simpa [Nat.factorial] using lower 3
theorem lower_4 : Superpermutation.LowerBound 4 27 := by simpa [Nat.factorial] using lower 4
theorem lower_5 : Superpermutation.LowerBound 5 124 := by simpa [Nat.factorial] using lower 5
theorem lower_6 : Superpermutation.LowerBound 6 725 := by simpa [Nat.factorial] using lower 6
theorem lower_7 : Superpermutation.LowerBound 7 5046 := by simpa [Nat.factorial] using lower 7
theorem lower_8 : Superpermutation.LowerBound 8 40327 := by simpa [Nat.factorial] using lower 8
theorem lower_9 : Superpermutation.LowerBound 9 362888 := by simpa [Nat.factorial] using lower 9

end LeapsInBounds.Proofs.SuperpermutationCounting
