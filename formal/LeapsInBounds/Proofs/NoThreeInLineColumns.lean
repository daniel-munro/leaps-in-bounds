module

public import LeapsInBounds.Statements.NoThreeInLine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Trivial upper bounds for the no-three-in-line problem

Points of the `n × n` grid with no three on a line number at most `2n`: each of
the `n` columns `x = c` holds at most two of them, since three points with the
same `x`-coordinate are on a line. For `n = 1` the grid has a single point.
-/

public section

namespace LeapsInBounds.Proofs.NoThreeInLineColumns

open Finset LeapsInBounds

/-- Three points with the same `x`-coordinate are on a line. -/
lemma collinear_of_fst {p q r : ℕ × ℕ} (hq : q.1 = p.1) (hr : r.1 = p.1) :
    NoThreeInLine.Collinear p q r := by
  simp [NoThreeInLine.Collinear, hq, hr]

/-- `D(n) ≤ 2n`: each column holds at most two points. -/
theorem upper (n : ℕ) : NoThreeInLine.UpperBound n (2 * n) := by
  intro s hg hs
  rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1) (t := range n)
    (fun p hp => mem_range.mpr (hg p hp).1)]
  calc ∑ c ∈ range n, #(s.filter fun p => p.1 = c)
      ≤ ∑ _c ∈ range n, 2 := by
        refine sum_le_sum fun c _ => ?_
        by_contra h
        obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := two_lt_card.mp (not_le.mp h)
        simp only [mem_filter] at hp hq hr
        exact hs p hp.1 q hq.1 r hr.1 hpq hpr hqr
          (collinear_of_fst (hq.2.trans hp.2.symm) (hr.2.trans hp.2.symm))
    _ = 2 * n := by simp [mul_comm]

/-- `D(1) ≤ 1`: the `1 × 1` grid has one point. -/
theorem upper_1 : NoThreeInLine.UpperBound 1 1 := by
  intro s hg _
  refine card_le_one.mpr fun a ha b hb => ?_
  have := hg a ha
  have := hg b hb
  ext <;> omega

theorem upper_2 : NoThreeInLine.UpperBound 2 4 := upper 2
theorem upper_3 : NoThreeInLine.UpperBound 3 6 := upper 3
theorem upper_4 : NoThreeInLine.UpperBound 4 8 := upper 4
theorem upper_5 : NoThreeInLine.UpperBound 5 10 := upper 5
theorem upper_6 : NoThreeInLine.UpperBound 6 12 := upper 6
theorem upper_7 : NoThreeInLine.UpperBound 7 14 := upper 7
theorem upper_8 : NoThreeInLine.UpperBound 8 16 := upper 8
theorem upper_9 : NoThreeInLine.UpperBound 9 18 := upper 9
theorem upper_10 : NoThreeInLine.UpperBound 10 20 := upper 10
theorem upper_11 : NoThreeInLine.UpperBound 11 22 := upper 11
theorem upper_12 : NoThreeInLine.UpperBound 12 24 := upper 12
theorem upper_13 : NoThreeInLine.UpperBound 13 26 := upper 13
theorem upper_14 : NoThreeInLine.UpperBound 14 28 := upper 14
theorem upper_15 : NoThreeInLine.UpperBound 15 30 := upper 15
theorem upper_16 : NoThreeInLine.UpperBound 16 32 := upper 16
theorem upper_17 : NoThreeInLine.UpperBound 17 34 := upper 17
theorem upper_18 : NoThreeInLine.UpperBound 18 36 := upper 18
theorem upper_19 : NoThreeInLine.UpperBound 19 38 := upper 19
theorem upper_20 : NoThreeInLine.UpperBound 20 40 := upper 20
theorem upper_21 : NoThreeInLine.UpperBound 21 42 := upper 21
theorem upper_22 : NoThreeInLine.UpperBound 22 44 := upper 22
theorem upper_23 : NoThreeInLine.UpperBound 23 46 := upper 23
theorem upper_24 : NoThreeInLine.UpperBound 24 48 := upper 24
theorem upper_25 : NoThreeInLine.UpperBound 25 50 := upper 25
theorem upper_26 : NoThreeInLine.UpperBound 26 52 := upper 26
theorem upper_27 : NoThreeInLine.UpperBound 27 54 := upper 27
theorem upper_28 : NoThreeInLine.UpperBound 28 56 := upper 28
theorem upper_29 : NoThreeInLine.UpperBound 29 58 := upper 29
theorem upper_30 : NoThreeInLine.UpperBound 30 60 := upper 30
theorem upper_31 : NoThreeInLine.UpperBound 31 62 := upper 31
theorem upper_32 : NoThreeInLine.UpperBound 32 64 := upper 32
theorem upper_33 : NoThreeInLine.UpperBound 33 66 := upper 33
theorem upper_34 : NoThreeInLine.UpperBound 34 68 := upper 34
theorem upper_35 : NoThreeInLine.UpperBound 35 70 := upper 35
theorem upper_36 : NoThreeInLine.UpperBound 36 72 := upper 36
theorem upper_37 : NoThreeInLine.UpperBound 37 74 := upper 37
theorem upper_38 : NoThreeInLine.UpperBound 38 76 := upper 38
theorem upper_39 : NoThreeInLine.UpperBound 39 78 := upper 39
theorem upper_40 : NoThreeInLine.UpperBound 40 80 := upper 40
theorem upper_41 : NoThreeInLine.UpperBound 41 82 := upper 41
theorem upper_42 : NoThreeInLine.UpperBound 42 84 := upper 42
theorem upper_43 : NoThreeInLine.UpperBound 43 86 := upper 43
theorem upper_44 : NoThreeInLine.UpperBound 44 88 := upper 44
theorem upper_45 : NoThreeInLine.UpperBound 45 90 := upper 45
theorem upper_46 : NoThreeInLine.UpperBound 46 92 := upper 46
theorem upper_47 : NoThreeInLine.UpperBound 47 94 := upper 47
theorem upper_48 : NoThreeInLine.UpperBound 48 96 := upper 48
theorem upper_49 : NoThreeInLine.UpperBound 49 98 := upper 49
theorem upper_50 : NoThreeInLine.UpperBound 50 100 := upper 50
theorem upper_51 : NoThreeInLine.UpperBound 51 102 := upper 51
theorem upper_52 : NoThreeInLine.UpperBound 52 104 := upper 52
theorem upper_53 : NoThreeInLine.UpperBound 53 106 := upper 53
theorem upper_54 : NoThreeInLine.UpperBound 54 108 := upper 54
theorem upper_55 : NoThreeInLine.UpperBound 55 110 := upper 55
theorem upper_56 : NoThreeInLine.UpperBound 56 112 := upper 56
theorem upper_57 : NoThreeInLine.UpperBound 57 114 := upper 57
theorem upper_58 : NoThreeInLine.UpperBound 58 116 := upper 58
theorem upper_59 : NoThreeInLine.UpperBound 59 118 := upper 59
theorem upper_60 : NoThreeInLine.UpperBound 60 120 := upper 60
theorem upper_61 : NoThreeInLine.UpperBound 61 122 := upper 61
theorem upper_62 : NoThreeInLine.UpperBound 62 124 := upper 62
theorem upper_63 : NoThreeInLine.UpperBound 63 126 := upper 63
theorem upper_64 : NoThreeInLine.UpperBound 64 128 := upper 64
theorem upper_65 : NoThreeInLine.UpperBound 65 130 := upper 65
theorem upper_66 : NoThreeInLine.UpperBound 66 132 := upper 66
theorem upper_67 : NoThreeInLine.UpperBound 67 134 := upper 67
theorem upper_68 : NoThreeInLine.UpperBound 68 136 := upper 68
theorem upper_69 : NoThreeInLine.UpperBound 69 138 := upper 69
theorem upper_70 : NoThreeInLine.UpperBound 70 140 := upper 70
theorem upper_71 : NoThreeInLine.UpperBound 71 142 := upper 71
theorem upper_72 : NoThreeInLine.UpperBound 72 144 := upper 72
theorem upper_73 : NoThreeInLine.UpperBound 73 146 := upper 73
theorem upper_74 : NoThreeInLine.UpperBound 74 148 := upper 74
theorem upper_75 : NoThreeInLine.UpperBound 75 150 := upper 75
theorem upper_76 : NoThreeInLine.UpperBound 76 152 := upper 76
theorem upper_77 : NoThreeInLine.UpperBound 77 154 := upper 77
theorem upper_78 : NoThreeInLine.UpperBound 78 156 := upper 78

end LeapsInBounds.Proofs.NoThreeInLineColumns
