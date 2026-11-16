module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Function.Iterate

/-!
# Busy beaver functions

Formal statements of bounds on the busy beaver shift function `BB(n)` (also
written `S(n)`), the most steps an `n`-state, 2-symbol Turing machine takes
before halting when started on a blank tape, and the ones function `Σ(n)`, the
most 1s such a machine leaves on the tape when it halts.

A machine has states `Fin n` and symbols `Bool` (`false` is the blank 0, and
`true` is 1), on a tape infinite in both directions. In each state, for each
symbol read, it writes a symbol, moves the head one cell left or right, and
goes to a state or halts. The halting transition also writes and moves, and
counts as a step, as usual for these functions. Since the states can be
renumbered, the machine can start in any of them.

A certificate for `busy-beaver-shift-{n}` with lower bound `N` must prove
`ShiftLowerBound n N`, and one with upper bound `N` must prove
`ShiftUpperBound n N`. For `busy-beaver-ones-{n}`, they are
`OnesLowerBound n N` and `OnesUpperBound n N`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.BusyBeaver

/-- An `n`-state, 2-symbol Turing machine: in state `q` reading `s`,
`δ q s = (w, right, next)` writes `w`, moves right if `right` and left
otherwise, and goes to state `next`, or halts if it's `none`. -/
structure Machine (n : ℕ) where
  δ : Fin n → Bool → Bool × Bool × Option (Fin n)

/-- A configuration: the state (`none` once halted), the head's position, and
the tape. -/
structure Config (n : ℕ) where
  state : Option (Fin n)
  head : ℤ
  tape : ℤ → Bool

/-- One step of `M`. A halted configuration stays as it is. -/
def Machine.step {n : ℕ} (M : Machine n) (c : Config n) : Config n :=
  match c.state with
  | none => c
  | some q =>
    let (w, right, next) := M.δ q (c.tape c.head)
    { state := next
      head := if right then c.head + 1 else c.head - 1
      tape := Function.update c.tape c.head w }

/-- The configuration after `k` steps of `M`, started in state `q` with the
head on a blank tape. -/
def Machine.run {n : ℕ} (M : Machine n) (q : Fin n) (k : ℕ) : Config n :=
  M.step^[k] ⟨some q, 0, fun _ => false⟩

/-- `M`, started in state `q` on a blank tape, halts after exactly `k` steps. -/
def Machine.HaltsIn {n : ℕ} (M : Machine n) (q : Fin n) (k : ℕ) : Prop :=
  (M.run q k).state = none ∧ ∀ j < k, (M.run q j).state ≠ none

/-- The number of 1s on the tape. -/
noncomputable def Config.ones {n : ℕ} (c : Config n) : ℕ :=
  {i : ℤ | c.tape i = true}.ncard

/-- `BB(n) ≥ N`: some `n`-state machine halts after at least `N` steps. -/
def ShiftLowerBound (n N : ℕ) : Prop :=
  ∃ M : Machine n, ∃ q k, M.HaltsIn q k ∧ N ≤ k

/-- `BB(n) ≤ N`: every `n`-state machine that halts does so within `N` steps. -/
def ShiftUpperBound (n N : ℕ) : Prop :=
  ∀ M : Machine n, ∀ q k, M.HaltsIn q k → k ≤ N

/-- `Σ(n) ≥ N`: some `n`-state machine halts with at least `N` 1s on the tape. -/
def OnesLowerBound (n N : ℕ) : Prop :=
  ∃ M : Machine n, ∃ q k, M.HaltsIn q k ∧ N ≤ (M.run q k).ones

/-- `Σ(n) ≤ N`: every `n`-state machine that halts leaves at most `N` 1s on
the tape. -/
def OnesUpperBound (n N : ℕ) : Prop :=
  ∀ M : Machine n, ∀ q k, M.HaltsIn q k → (M.run q k).ones ≤ N

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem ShiftLowerBound.le_of_upperBound {n a b : ℕ} (hl : ShiftLowerBound n a)
    (hu : ShiftUpperBound n b) : a ≤ b := by
  obtain ⟨M, q, k, hk, ha⟩ := hl
  exact ha.trans (hu M q k hk)

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem OnesLowerBound.le_of_upperBound {n a b : ℕ} (hl : OnesLowerBound n a)
    (hu : OnesUpperBound n b) : a ≤ b := by
  obtain ⟨M, q, k, hk, ha⟩ := hl
  exact ha.trans (hu M q k hk)

end LeapsInBounds.BusyBeaver
