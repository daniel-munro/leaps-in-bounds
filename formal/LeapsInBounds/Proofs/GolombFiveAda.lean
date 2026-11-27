module

public import LeapsInBounds.Statements.Golomb
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup

/-! Five-mark Golomb ruler certificate by Ada Folio (ChatGPT), Panoramica Systems. -/
public section
namespace LeapsInBounds.Proofs.GolombFiveAda
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private def ds (a b c d : Nat) := [a,b,c,d,b-a,c-a,d-a,c-b,d-b,d-c]
private theorem exhaust : ∀ a b c d : Fin 11, 0 < a.val → a.val < b.val → b.val < c.val → c.val < d.val → ¬ (ds a b c d).Nodup := by decide
private abbrev Pair := {p : Fin 5 × Fin 5 // p.1 < p.2}
private def pairs : List Pair := [ ⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(0,3), by decide⟩, ⟨(0,4), by decide⟩, ⟨(1,2), by decide⟩, ⟨(1,3), by decide⟩, ⟨(1,4), by decide⟩, ⟨(2,3), by decide⟩, ⟨(2,4), by decide⟩, ⟨(3,4), by decide⟩]
theorem lower_5 : Golomb.LowerBound 5 11 := by
  intro s hs hg
  let m := s.orderEmbOfFin hs
  have mem (i : Fin 5) : m i ∈ s := s.orderEmbOfFin_mem hs i
  refine ⟨m 0, mem 0, m 4, mem 4, ?_⟩
  by_contra h
  let z (i : Fin 5) := m i - m 0
  have first (i : Fin 5) : m 0 ≤ m i := m.monotone (Fin.zero_le i)
  have last (i : Fin 5) : m i ≤ m 4 := m.monotone (Fin.le_last i)
  have strictly : StrictMono z := by
    intro i j hij
    have := m.strictMono hij
    have := first i
    dsimp [z]
    omega
  have zero : z 0 = 0 := Nat.sub_self _
  have bounded (i : Fin 5) : z i < 11 := by
    have := last i
    dsimp [z]
    omega
  have shift (i j : Fin 5) : z j - z i = m j - m i := by
    have := first i
    have := first j
    dsimp [z]
    omega
  let distance (p : Pair) := z p.val.2 - z p.val.1
  have unique : Function.Injective distance := by
    intro p q eq
    change z p.val.2 - z p.val.1 = z q.val.2 - z q.val.1 at eq
    rw [shift, shift] at eq
    obtain ⟨hx, hy⟩ := hg _ (mem p.val.1) _ (mem p.val.2) _ (mem q.val.1) _ (mem q.val.2)
      (m.strictMono p.property) (m.strictMono q.property) eq
    exact Subtype.ext (Prod.ext (m.injective hx) (m.injective hy))
  have distinct : (pairs.map distance).Nodup := List.Nodup.map unique (by decide)
  change [z 1 - z 0, z 2 - z 0, z 3 - z 0, z 4 - z 0, z 2 - z 1, z 3 - z 1, z 4 - z 1, z 3 - z 2, z 4 - z 2, z 4 - z 3].Nodup at distinct
  simp only [zero,Nat.sub_zero] at distinct
  have h₁ := strictly (show (0 : Fin 5) < 1 by decide)
  rw [zero] at h₁
  exact exhaust ⟨z 1, bounded 1⟩ ⟨z 2, bounded 2⟩ ⟨z 3, bounded 3⟩ ⟨z 4, bounded 4⟩ h₁ (strictly (by decide)) (strictly (by decide)) (strictly (by decide)) distinct
end LeapsInBounds.Proofs.GolombFiveAda
