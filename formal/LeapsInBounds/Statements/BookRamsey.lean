module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Card

/-!
# Book Ramsey numbers

Formal statements of bounds on the book Ramsey number `R(B_m, B_n)`: the
smallest `N` such that every graph on `N` vertices contains the book `B_m`, or
its complement contains the book `B_n`. (A two-coloring of the edges of `K_N`
is a graph together with its complement.)

The book `B_m = K_2 + \overline{K_m}` is `m` triangles sharing an edge. A graph
contains it, not necessarily as an induced subgraph, exactly when some edge has
at least `m` common neighbors.

A certificate for `book-ramsey-{m}-{n}` with lower bound `N` must prove
`LowerBound m n N`, and one with upper bound `N` must prove `UpperBound m n N`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.BookRamsey

/-- `G` contains the book `B_m`: an edge `uv` and `m` vertices adjacent to both
`u` and `v`. -/
def HasBook {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v, G.Adj u v ∧ ∃ s : Finset V, s.card = m ∧ ∀ w ∈ s, G.Adj u w ∧ G.Adj v w

/-- `R(B_m, B_n) ≥ N`: some graph on `N - 1` vertices doesn't contain `B_m`,
and neither does its complement contain `B_n`. -/
def LowerBound (m n N : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin (N - 1)), ¬ HasBook G m ∧ ¬ HasBook Gᶜ n

/-- `R(B_m, B_n) ≤ N`: every graph on `N` vertices contains `B_m`, or its
complement contains `B_n`. -/
def UpperBound (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasBook G m ∨ HasBook Gᶜ n

/-- A book in a graph maps to a book under an injective map that preserves
adjacency. -/
theorem HasBook.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {m : ℕ}
    (f : V ↪ W) (hf : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) (h : HasBook G m) :
    HasBook H m := by
  obtain ⟨u, v, huv, s, hs, hw⟩ := h
  exact ⟨f u, f v, hf _ _ huv, s.map f, by simp [hs], by
    simp only [Finset.mem_map]
    rintro _ ⟨w, hw', rfl⟩
    exact ⟨hf _ _ (hw w hw').1, hf _ _ (hw w hw').2⟩⟩

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem LowerBound.le_of_upperBound {m n a b : ℕ} (hl : LowerBound m n a)
    (hu : UpperBound m n b) : a ≤ b := by
  by_contra h
  obtain ⟨G, hm, hn⟩ := hl
  let f := Fin.castLEEmb (show b ≤ a - 1 by omega)
  rcases hu (G.comap f) with h' | h'
  · exact hm (h'.map f fun _ _ hab => hab)
  · refine hn (h'.map f fun x y hxy => ?_)
    exact ⟨fun he => hxy.1 (f.injective he), hxy.2⟩

end LeapsInBounds.BookRamsey
