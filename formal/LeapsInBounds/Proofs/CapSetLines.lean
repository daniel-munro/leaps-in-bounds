module

public import LeapsInBounds.Statements.CapSet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Trivial upper bounds for cap sets

A cap set in `𝔽₃^(m+1)` has at most `2 · 3^m` points. Partition the space into
the `3^m` lines `{x, x + e₀, x + 2e₀}`, the fibers of the map forgetting the
first coordinate. Three distinct points of one fiber have first coordinates
`0, 1, 2` in some order and agree elsewhere, so they sum to zero; a cap set
therefore has at most two points in each fiber.
-/

public section

namespace LeapsInBounds.Proofs.CapSetLines

open Finset LeapsInBounds

lemma sum_distinct : ∀ a b c : ZMod 3, a ≠ b → a ≠ c → b ≠ c → a + b + c = 0 := by decide

lemma three_mul : ∀ a : ZMod 3, a + a + a = 0 := by decide

/-- Points with the same tail and the same first coordinate are equal. -/
lemma eq_of_tail {m : ℕ} {x y : Fin (m + 1) → ZMod 3} (ht : Fin.tail x = Fin.tail y)
    (h0 : x 0 = y 0) : x = y := by
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  exact congrFun ht j

/-- `r(m + 1) ≤ 2 · 3^m`: each line `{x, x + e₀, x + 2e₀}` holds at most two
points of a cap set. -/
theorem upper (m : ℕ) : CapSet.UpperBound (m + 1) (2 * 3 ^ m) := by
  intro s hs
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin (m + 1) → ZMod 3 => Fin.tail x)
    (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ t, #(s.filter fun x => Fin.tail x = t)
      ≤ ∑ _t : Fin m → ZMod 3, 2 := by
        refine sum_le_sum fun t _ => ?_
        by_contra h
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.mp (not_le.mp h)
        simp only [mem_filter] at hx hy hz
        have txy : Fin.tail x = Fin.tail y := hx.2.trans hy.2.symm
        have txz : Fin.tail x = Fin.tail z := hx.2.trans hz.2.symm
        have tyz : Fin.tail y = Fin.tail z := hy.2.trans hz.2.symm
        refine hs x hx.1 y hy.1 z hz.1 hxy hxz hyz ?_
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact sum_distinct _ _ _ (fun h => hxy (eq_of_tail txy h))
            (fun h => hxz (eq_of_tail txz h)) (fun h => hyz (eq_of_tail tyz h))
        · have hy' : y j.succ = x j.succ := (congrFun txy j).symm
          have hz' : z j.succ = x j.succ := (congrFun txz j).symm
          simp only [Pi.add_apply, Pi.zero_apply, hy', hz']
          exact three_mul _
    _ = 2 * 3 ^ m := by simp [mul_comm]

theorem upper_1 : CapSet.UpperBound 1 2 := upper 0
theorem upper_2 : CapSet.UpperBound 2 6 := upper 1
theorem upper_3 : CapSet.UpperBound 3 18 := upper 2
theorem upper_4 : CapSet.UpperBound 4 54 := upper 3
theorem upper_5 : CapSet.UpperBound 5 162 := upper 4
theorem upper_6 : CapSet.UpperBound 6 486 := upper 5
theorem upper_7 : CapSet.UpperBound 7 1458 := upper 6
theorem upper_8 : CapSet.UpperBound 8 4374 := upper 7

end LeapsInBounds.Proofs.CapSetLines
