module

public import Mathlib.Data.Finset.Card

/-!
# Sorting networks

Formal statements of bounds on `S(n)` and `D(n)`: the smallest size (number of
comparators) and the smallest depth (number of parallel layers) of a sorting
network on `n` inputs.

A network is a list of comparators `(i, j)` on wires numbered from `0`,
applied in order. The comparator `(i, j)` puts the smaller of the values on
wires `i` and `j` on the lower-numbered of the two wires, and the larger on
the other. A network sorts if, for every input, the values it leaves on wires
`0, …, n - 1` are in increasing order. Inputs are natural numbers, which is no
loss, since a comparator network sorts every linearly ordered input if it
sorts every input of natural numbers.

Comparators on different wires can act at the same time, so a network's depth
is the length of the longest chain of comparators, each sharing a wire with
the one before it: each comparator is placed one step after the later of the
last comparators on its wires.

A certificate for `sorting-network-size-{n}` with lower bound `L` must prove
`SizeLowerBound n L`, and one with upper bound `L` must prove
`SizeUpperBound n L`. Similarly, `sorting-network-depth-{n}` uses
`DepthLowerBound` and `DepthUpperBound`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.SortingNetwork

/-- Apply the comparator `c` to the values `v` on the wires. -/
def applyComparator (v : ℕ → ℕ) (c : ℕ × ℕ) : ℕ → ℕ :=
  let i := min c.1 c.2
  let j := max c.1 c.2
  fun k => if k = i then min (v i) (v j) else if k = j then max (v i) (v j) else v k

/-- The values on the wires after applying the comparators of `net` in order. -/
def run (net : List (ℕ × ℕ)) (v : ℕ → ℕ) : ℕ → ℕ :=
  net.foldl applyComparator v

/-- Each comparator of `net` joins two different wires among `0, …, n - 1`. -/
def IsNetwork (n : ℕ) (net : List (ℕ × ℕ)) : Prop :=
  ∀ c ∈ net, c.1 < n ∧ c.2 < n ∧ c.1 ≠ c.2

/-- `net` sorts every input on `n` wires. -/
def Sorts (n : ℕ) (net : List (ℕ × ℕ)) : Prop :=
  ∀ v : ℕ → ℕ, ∀ i j, i ≤ j → j < n → run net v i ≤ run net v j

/-- The step at which each wire is last used by a comparator of `net`, or `0`
if it isn't. -/
def steps (net : List (ℕ × ℕ)) : ℕ → ℕ :=
  net.foldl (fun t c => let s := max (t c.1) (t c.2) + 1
    fun k => if k = c.1 ∨ k = c.2 then s else t k) (fun _ => 0)

/-- The depth of `net` on `n` wires: the last step at which any of its wires is
used. -/
def depth (n : ℕ) (net : List (ℕ × ℕ)) : ℕ :=
  ((List.range n).map (steps net)).foldr max 0

/-- `S(n) ≥ L`: every sorting network on `n` inputs has at least `L`
comparators. -/
def SizeLowerBound (n L : ℕ) : Prop :=
  ∀ net : List (ℕ × ℕ), IsNetwork n net → Sorts n net → L ≤ net.length

/-- `S(n) ≤ L`: some sorting network on `n` inputs has at most `L`
comparators. -/
def SizeUpperBound (n L : ℕ) : Prop :=
  ∃ net : List (ℕ × ℕ), IsNetwork n net ∧ Sorts n net ∧ net.length ≤ L

/-- `D(n) ≥ L`: every sorting network on `n` inputs has depth at least `L`. -/
def DepthLowerBound (n L : ℕ) : Prop :=
  ∀ net : List (ℕ × ℕ), IsNetwork n net → Sorts n net → L ≤ depth n net

/-- `D(n) ≤ L`: some sorting network on `n` inputs has depth at most `L`. -/
def DepthUpperBound (n L : ℕ) : Prop :=
  ∃ net : List (ℕ × ℕ), IsNetwork n net ∧ Sorts n net ∧ depth n net ≤ L

/-- Sanity check on the definitions: a lower bound on size never exceeds an
upper bound. -/
theorem SizeLowerBound.le_of_upperBound {n m L : ℕ} (hl : SizeLowerBound n m)
    (hu : SizeUpperBound n L) : m ≤ L := by
  obtain ⟨net, hn, hs, hle⟩ := hu
  have := hl net hn hs
  omega

/-- Sanity check on the definitions: a lower bound on depth never exceeds an
upper bound. -/
theorem DepthLowerBound.le_of_upperBound {n m L : ℕ} (hl : DepthLowerBound n m)
    (hu : DepthUpperBound n L) : m ≤ L := by
  obtain ⟨net, hn, hs, hle⟩ := hu
  have := hl net hn hs
  omega

end LeapsInBounds.SortingNetwork
