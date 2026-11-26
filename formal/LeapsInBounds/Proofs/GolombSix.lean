module

public import LeapsInBounds.Statements.Golomb
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup

/-!
# Exact lower bound for the six-mark Golomb ruler

Translate the leftmost mark to zero. At span at most sixteen, distinct positive
adjacent gaps are at most six. Lean checks that no arrangement of such gaps
produces fifteen distinct distances.
-/

public section

namespace LeapsInBounds.Proofs.GolombSix

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 2048

private def distances (a b c d e : Nat) : List Nat :=
  [a, b, c, d, e, b-a, c-a, d-a, e-a, c-b, d-b, e-b, d-c, e-c, e-d]

/-- Four other distinct positive gaps already occupy at least ten units. -/
private theorem gapBounds (a b c d e : Nat) (h₁ : 0 < a) (h₂ : 0 < b)
    (h₃ : 0 < c) (h₄ : 0 < d) (h₅ : 0 < e) (hs : a+b+c+d+e ≤ 16)
    (hn : [a,b,c,d,e].Nodup) : a < 7 ∧ b < 7 ∧ c < 7 ∧ d < 7 ∧ e < 7 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hn
  omega

/-- Check only ordered lists of distinct positive gaps in 1 through 6. -/
private theorem small :
    ∀ a : Fin 7, 0 < a.val →
    ∀ b : Fin 7, 0 < b.val → a.val ≠ b.val →
    ∀ c : Fin 7, 0 < c.val → a.val ≠ c.val → b.val ≠ c.val →
    ∀ d : Fin 7, 0 < d.val → a.val ≠ d.val → b.val ≠ d.val → c.val ≠ d.val →
    ∀ e : Fin 7, 0 < e.val → a.val ≠ e.val → b.val ≠ e.val → c.val ≠ e.val → d.val ≠ e.val →
    a.val+b.val+c.val+d.val+e.val ≤ 16 →
    ¬ (distances a.val (a.val+b.val) (a.val+b.val+c.val)
      (a.val+b.val+c.val+d.val) (a.val+b.val+c.val+d.val+e.val)).Nodup := by
  decide +kernel

private theorem takeGaps (a b c d e : Nat) (h : (distances a b c d e).Nodup) :
    [a,b-a,c-b,d-c,e-d].Nodup := by
  refine List.Nodup.sublist ?_ h
  unfold distances
  repeat first | apply List.Sublist.cons_cons | apply List.Sublist.cons | exact List.Sublist.slnil

private abbrev Pair := {p : Fin 6 × Fin 6 // p.1 < p.2}

private def pairs : List Pair :=
  [⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(0,3), by decide⟩,
   ⟨(0,4), by decide⟩, ⟨(0,5), by decide⟩, ⟨(1,2), by decide⟩,
   ⟨(1,3), by decide⟩, ⟨(1,4), by decide⟩, ⟨(1,5), by decide⟩,
   ⟨(2,3), by decide⟩, ⟨(2,4), by decide⟩, ⟨(2,5), by decide⟩,
   ⟨(3,4), by decide⟩, ⟨(3,5), by decide⟩, ⟨(4,5), by decide⟩]

theorem lower_6 : Golomb.LowerBound 6 17 := by
  intro s hs hg
  let m := s.orderEmbOfFin hs
  have mem (i : Fin 6) : m i ∈ s := s.orderEmbOfFin_mem hs i
  refine ⟨m 0, mem 0, m 5, mem 5, ?_⟩
  by_contra h
  let z (i : Fin 6) := m i - m 0
  have first (i : Fin 6) : m 0 ≤ m i := m.monotone (Fin.zero_le i)
  have last (i : Fin 6) : m i ≤ m 5 := m.monotone (Fin.le_last i)
  have strictly : StrictMono z := by
    intro i j hij
    have := m.strictMono hij
    have := first i
    dsimp [z]
    omega
  have zero : z 0 = 0 := Nat.sub_self _
  have bounded (i : Fin 6) : z i < 17 := by
    have := last i
    dsimp [z]
    omega
  have shift (i j : Fin 6) : z j - z i = m j - m i := by
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
  change [z 1 - z 0, z 2 - z 0, z 3 - z 0, z 4 - z 0, z 5 - z 0,
    z 2 - z 1, z 3 - z 1, z 4 - z 1, z 5 - z 1, z 3 - z 2, z 4 - z 2, z 5 - z 2,
    z 4 - z 3, z 5 - z 3, z 5 - z 4].Nodup at distinct
  simp only [zero, Nat.sub_zero] at distinct
  let a := z 1
  let b := z 2 - z 1
  let c := z 3 - z 2
  let d := z 4 - z 3
  let e := z 5 - z 4
  have z01 : z 0 < z 1 := strictly (by decide)
  have z12 : z 1 < z 2 := strictly (by decide)
  have z23 : z 2 < z 3 := strictly (by decide)
  have z34 : z 3 < z 4 := strictly (by decide)
  have z45 : z 4 < z 5 := strictly (by decide)
  have hp : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e := by dsimp [a,b,c,d,e]; omega
  have hb : a+b=z 2 ∧ a+b+c=z 3 ∧ a+b+c+d=z 4 ∧ a+b+c+d+e=z 5 := by
    dsimp [a,b,c,d,e]; omega
  have hs' : a+b+c+d+e ≤ 16 := by have := bounded 5; omega
  have hn := takeGaps _ _ _ _ _ distinct
  change [a,b,c,d,e].Nodup at hn
  obtain ⟨ha,hB,hc,hd,he⟩ := gapBounds a b c d e hp.1 hp.2.1 hp.2.2.1
    hp.2.2.2.1 hp.2.2.2.2 hs' hn
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hn
  have fail := small ⟨a,ha⟩ hp.1 ⟨b,hB⟩ hp.2.1 (by tauto)
    ⟨c,hc⟩ hp.2.2.1 (by tauto) (by tauto)
    ⟨d,hd⟩ hp.2.2.2.1 (by tauto) (by tauto) (by tauto)
    ⟨e,he⟩ hp.2.2.2.2 (by tauto) (by tauto) (by tauto) (by tauto) hs'
  change ¬ (distances a (a+b) (a+b+c) (a+b+c+d) (a+b+c+d+e)).Nodup at fail
  rw [hb.2.2.2, hb.2.2.1, hb.2.1, hb.1] at fail
  exact fail distinct

end LeapsInBounds.Proofs.GolombSix
