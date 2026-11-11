module

public import LeapsInBounds.Statements.SortingNetwork
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Simple lower bounds for sorting networks

- Size: `S(n) ≥ n - 1`. If the comparators of a network don't join the wires
  `0, …, n - 1` into one connected component, put `1` on the wires of one
  component and `0` on the others (or the reverse). Each comparator then sees
  two equal values, so nothing moves, and one of the two inputs is left
  unsorted. A connected graph on `n` vertices has at least `n - 1` edges.
- Depth: `D(n) ≥ ⌈log₂ n⌉`. After a comparator at step `s`, the value on each
  of its wires depends only on the inputs on at most `2^s` wires. But the value
  on wire `0` of a sorting network is the minimum of the inputs, which depends
  on all `n` of them: with the input that is `0` on one wire `w` and `1`
  elsewhere, some output is `0`, so wire `0` is `0`, while with all `1`s it is
  `1`.
-/

@[expose] public section

namespace LeapsInBounds.Proofs.SortingNetworkLower

open LeapsInBounds.SortingNetwork

/-- A comparator acting on two wires with equal values changes nothing. -/
lemma applyComparator_of_eq {v : ℕ → ℕ} {c : ℕ × ℕ} (h : v c.1 = v c.2) :
    applyComparator v c = v := by
  have h' : v (min c.1 c.2) = v (max c.1 c.2) := by
    rcases le_total c.1 c.2 with hc | hc
    · rw [min_eq_left hc, max_eq_right hc, h]
    · rw [min_eq_right hc, max_eq_left hc, h]
  funext k
  simp only [applyComparator]
  split_ifs with h1 h2
  · subst h1; rw [h', min_self]
  · subst h2; rw [h', max_self]
  · rfl

/-- A network leaves an input unchanged if each comparator sees equal values. -/
lemma run_of_forall {v : ℕ → ℕ} :
    ∀ {net : List (ℕ × ℕ)}, (∀ c ∈ net, v c.1 = v c.2) → run net v = v
  | [], _ => rfl
  | c :: net, h => by
    simp only [run, List.foldl_cons]
    rw [applyComparator_of_eq (h c (by simp))]
    exact run_of_forall fun c' hc' => h c' (by simp [hc'])

/-- Every sorting network on `n` wires has at least `n - 1` comparators. -/
theorem size_lower (n : ℕ) (net : List (ℕ × ℕ)) (hn : IsNetwork n net) (hs : Sorts n net) :
    n ≤ net.length + 1 := by
  classical
  by_contra hlt
  push Not at hlt
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel fun i j => (i.val, j.val) ∈ net
  -- the graph has at most `net.length` edges
  have hE : Nat.card G.edgeSet ≤ net.length := by
    let T : Finset (Sym2 ℕ) := (net.map fun c => s(c.1, c.2)).toFinset
    have hmem : ∀ e : G.edgeSet, e.1.map Fin.val ∈ T := by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ i j =>
        rw [SimpleGraph.mem_edgeSet] at he
        simp only [G, SimpleGraph.fromRel_adj] at he
        obtain ⟨-, h | h⟩ := he
        · simp only [T, List.mem_toFinset, List.mem_map, Sym2.map_mk]
          exact ⟨_, h, rfl⟩
        · simp only [T, List.mem_toFinset, List.mem_map, Sym2.map_mk]
          exact ⟨_, h, Sym2.eq_swap⟩
    have hinj : Function.Injective fun e : G.edgeSet => (⟨e.1.map Fin.val, hmem e⟩ : T) := by
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Sym2.map.injective Fin.val_injective hab)
    calc Nat.card G.edgeSet ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
      _ = T.card := Nat.card_eq_finsetCard T
      _ ≤ (net.map fun c => s(c.1, c.2)).length := List.toFinset_card_le _
      _ = net.length := List.length_map _
  -- so it is not connected
  have hnc : ¬ G.Preconnected := by
    intro hp
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have := (SimpleGraph.Connected.mk hp).card_vert_le_card_edgeSet_add_one
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    rw [← Nat.card_eq_fintype_card] at this
    omega
  simp only [SimpleGraph.Preconnected, not_forall] at hnc
  obtain ⟨u, w, huw⟩ := hnc
  let A : ℕ → Prop := fun x => ∃ h : x < n, G.Reachable u ⟨x, h⟩
  have hclosed : ∀ c ∈ net, (A c.1 ↔ A c.2) := by
    intro c hc
    obtain ⟨h1, h2, hne⟩ := hn c hc
    have hadj : G.Adj ⟨c.1, h1⟩ ⟨c.2, h2⟩ := by
      simp only [G, SimpleGraph.fromRel_adj]
      exact ⟨fun h => hne (congrArg Fin.val h), Or.inl hc⟩
    exact ⟨fun ⟨_, h⟩ => ⟨h2, h.trans hadj.reachable⟩,
      fun ⟨_, h⟩ => ⟨h1, h.trans hadj.symm.reachable⟩⟩
  have hu : A u.val := ⟨u.isLt, SimpleGraph.Reachable.refl _⟩
  have hw : ¬ A w.val := fun ⟨_, h⟩ => huw h
  let v : ℕ → ℕ := fun x => if A x then 1 else 0
  let v' : ℕ → ℕ := fun x => if A x then 0 else 1
  have hv : run net v = v := run_of_forall fun c hc => by simp only [v, hclosed c hc]
  have hv' : run net v' = v' := run_of_forall fun c hc => by simp only [v', hclosed c hc]
  rcases le_total u.val w.val with h | h
  · have := hs v u.val w.val h w.isLt
    simp [hv, v, hu, hw] at this
  · have := hs v' w.val u.val h u.isLt
    simp [hv', v', hu, hw] at this

/-- `S(n) ≥ n - 1`. -/
theorem sizeLowerBound (n : ℕ) : SizeLowerBound n (n - 1) := fun net hn hs => by
  have := size_lower n net hn hs
  omega

/-- The update of `steps` for one comparator. -/
def stepFn (t : ℕ → ℕ) (c : ℕ × ℕ) : ℕ → ℕ :=
  let s := max (t c.1) (t c.2) + 1
  fun k => if k = c.1 ∨ k = c.2 then s else t k

lemma steps_eq (net : List (ℕ × ℕ)) : steps net = net.foldl stepFn (fun _ => 0) := rfl

/-- The wires whose inputs the value on each wire can depend on, updated for one
comparator. -/
def depFn (D : ℕ → Finset ℕ) (c : ℕ × ℕ) : ℕ → Finset ℕ :=
  fun k => if k = c.1 ∨ k = c.2 then D c.1 ∪ D c.2 else D k

/-- The value on a wire last used at step `s` depends on at most `2^s` inputs. -/
lemma card_le : ∀ (net : List (ℕ × ℕ)) (t : ℕ → ℕ) (D : ℕ → Finset ℕ),
    (∀ k, (D k).card ≤ 2 ^ t k) → ∀ k, (net.foldl depFn D k).card ≤ 2 ^ (net.foldl stepFn t k)
  | [], _, _, h => h
  | c :: net, t, D, h => by
    apply card_le net
    intro k
    simp only [depFn, stepFn]
    split_ifs
    · calc (D c.1 ∪ D c.2).card ≤ (D c.1).card + (D c.2).card := Finset.card_union_le _ _
        _ ≤ 2 ^ t c.1 + 2 ^ t c.2 := Nat.add_le_add (h _) (h _)
        _ ≤ 2 ^ max (t c.1) (t c.2) + 2 ^ max (t c.1) (t c.2) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
            (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
        _ = 2 ^ (max (t c.1) (t c.2) + 1) := by rw [pow_succ]; omega
    · exact h k

/-- The value on each wire depends only on the inputs on the wires in its set. -/
lemma agree (v v' : ℕ → ℕ) : ∀ (net : List (ℕ × ℕ)) (D : ℕ → Finset ℕ) (u u' : ℕ → ℕ),
    (∀ k, (∀ x ∈ D k, v x = v' x) → u k = u' k) →
    ∀ k, (∀ x ∈ net.foldl depFn D k, v x = v' x) →
      net.foldl applyComparator u k = net.foldl applyComparator u' k
  | [], _, _, _, h => h
  | c :: net, D, u, u', h => by
    apply agree v v' net
    intro k hk
    have both : (∀ x ∈ D c.1 ∪ D c.2, v x = v' x) → u c.1 = u' c.1 ∧ u c.2 = u' c.2 :=
      fun hx => ⟨h _ fun x hx' => hx x (Finset.mem_union_left _ hx'),
        h _ fun x hx' => hx x (Finset.mem_union_right _ hx')⟩
    have hmin : min c.1 c.2 = c.1 ∨ min c.1 c.2 = c.2 := min_choice _ _
    have hmax : max c.1 c.2 = c.1 ∨ max c.1 c.2 = c.2 := max_choice _ _
    simp only [depFn] at hk
    simp only [applyComparator]
    split_ifs at hk ⊢ <;>
      first
      | exact h k hk
      | omega
      | (obtain ⟨e1, e2⟩ := both hk
         rcases hmin with e | e <;> rcases hmax with e' | e' <;> rw [e, e'] <;> simp [e1, e2])

/-- If some input on wires `0, …, n - 1` is `0`, then so is some output. -/
lemma exists_zero (n : ℕ) : ∀ (net : List (ℕ × ℕ)), (∀ c ∈ net, c.1 < n ∧ c.2 < n) →
    ∀ u : ℕ → ℕ, (∃ k < n, u k = 0) → ∃ k < n, run net u k = 0
  | [], _, _, h => h
  | c :: net, hn, u, ⟨k, hk, hu⟩ => by
    simp only [run, List.foldl_cons]
    apply exists_zero n net (fun c' hc' => hn c' (by simp [hc']))
    obtain ⟨h1, h2⟩ := hn c (by simp)
    have hmin : min c.1 c.2 = c.1 ∨ min c.1 c.2 = c.2 := min_choice _ _
    have hmax : max c.1 c.2 = c.1 ∨ max c.1 c.2 = c.2 := max_choice _ _
    by_cases hkc : k = min c.1 c.2 ∨ k = max c.1 c.2
    · refine ⟨min c.1 c.2, by omega, ?_⟩
      simp only [applyComparator, ↓reduceIte]
      rcases hkc with e | e
      · rw [← e, hu]; simp
      · rw [← e, hu]; simp
    · refine ⟨k, hk, ?_⟩
      push Not at hkc
      simp [applyComparator, hkc.1, hkc.2, hu]

lemma le_foldr_max : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0
  | b :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max h).trans (le_max_right _ _)

/-- A sorting network on `n` wires has depth `d` with `n ≤ 2^d`. -/
theorem depth_lower (n : ℕ) (net : List (ℕ × ℕ)) (hn : IsNetwork n net) (hs : Sorts n net) :
    n ≤ 2 ^ depth n net := by
  classical
  by_contra hlt
  push Not at hlt
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  let D0 : ℕ → Finset ℕ := fun k => {k}
  have hcard := card_le net (fun _ => 0) D0 (fun k => by simp [D0]) 0
  rw [← steps_eq] at hcard
  have hdep : steps net 0 ≤ depth n net :=
    le_foldr_max (List.mem_map.2 ⟨0, List.mem_range.2 hn0, rfl⟩)
  have hlt' : (net.foldl depFn D0 0).card < (Finset.range n).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (hcard.trans (Nat.pow_le_pow_right (by omega) hdep)) hlt
  obtain ⟨w, hwn, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  rw [Finset.mem_range] at hwn
  let v : ℕ → ℕ := fun x => if x = w then 0 else 1
  let v' : ℕ → ℕ := fun _ => 1
  have h0 : run net v 0 = run net v' 0 := by
    apply agree v v' net D0 v v' (fun k hk => hk k (by simp [D0])) 0
    intro x hx
    have : x ≠ w := fun e => hw (e ▸ hx)
    simp [v, v', this]
  have hv' : run net v' = v' := run_of_forall fun _ _ => rfl
  rw [hv'] at h0
  obtain ⟨k, hk, hk0⟩ := exists_zero n net (fun c hc => ⟨(hn c hc).1, (hn c hc).2.1⟩) v
    ⟨w, hwn, by simp [v]⟩
  have := hs v 0 k (Nat.zero_le _) hk
  simp only [v'] at h0
  omega

/-- `D(n) ≥ L` whenever `2^(L-1) < n`, that is, `D(n) ≥ ⌈log₂ n⌉`. -/
theorem depthLowerBound {n L : ℕ} (h : 2 ^ L < 2 * n) : DepthLowerBound n L :=
  fun net hn hs => by
    have h1 := depth_lower n net hn hs
    by_contra hd
    push Not at hd
    have : 2 ^ (depth n net + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hd
    rw [pow_succ] at this
    omega

theorem size_1 : SizeLowerBound 1 0 := sizeLowerBound 1
theorem size_2 : SizeLowerBound 2 1 := sizeLowerBound 2
theorem size_3 : SizeLowerBound 3 2 := sizeLowerBound 3
theorem size_4 : SizeLowerBound 4 3 := sizeLowerBound 4
theorem size_5 : SizeLowerBound 5 4 := sizeLowerBound 5
theorem size_6 : SizeLowerBound 6 5 := sizeLowerBound 6
theorem size_7 : SizeLowerBound 7 6 := sizeLowerBound 7
theorem size_8 : SizeLowerBound 8 7 := sizeLowerBound 8
theorem size_9 : SizeLowerBound 9 8 := sizeLowerBound 9
theorem size_10 : SizeLowerBound 10 9 := sizeLowerBound 10
theorem size_11 : SizeLowerBound 11 10 := sizeLowerBound 11
theorem size_12 : SizeLowerBound 12 11 := sizeLowerBound 12
theorem size_13 : SizeLowerBound 13 12 := sizeLowerBound 13
theorem size_14 : SizeLowerBound 14 13 := sizeLowerBound 14
theorem size_15 : SizeLowerBound 15 14 := sizeLowerBound 15
theorem size_16 : SizeLowerBound 16 15 := sizeLowerBound 16
theorem size_17 : SizeLowerBound 17 16 := sizeLowerBound 17
theorem size_18 : SizeLowerBound 18 17 := sizeLowerBound 18
theorem size_19 : SizeLowerBound 19 18 := sizeLowerBound 19
theorem size_20 : SizeLowerBound 20 19 := sizeLowerBound 20
theorem size_21 : SizeLowerBound 21 20 := sizeLowerBound 21
theorem size_22 : SizeLowerBound 22 21 := sizeLowerBound 22
theorem size_23 : SizeLowerBound 23 22 := sizeLowerBound 23
theorem size_24 : SizeLowerBound 24 23 := sizeLowerBound 24
theorem size_25 : SizeLowerBound 25 24 := sizeLowerBound 25
theorem size_26 : SizeLowerBound 26 25 := sizeLowerBound 26
theorem size_27 : SizeLowerBound 27 26 := sizeLowerBound 27
theorem size_28 : SizeLowerBound 28 27 := sizeLowerBound 28
theorem size_29 : SizeLowerBound 29 28 := sizeLowerBound 29
theorem size_30 : SizeLowerBound 30 29 := sizeLowerBound 30
theorem size_31 : SizeLowerBound 31 30 := sizeLowerBound 31
theorem size_32 : SizeLowerBound 32 31 := sizeLowerBound 32

theorem depth_1 : DepthLowerBound 1 0 := depthLowerBound (by decide)
theorem depth_2 : DepthLowerBound 2 1 := depthLowerBound (by decide)
theorem depth_3 : DepthLowerBound 3 2 := depthLowerBound (by decide)
theorem depth_4 : DepthLowerBound 4 2 := depthLowerBound (by decide)
theorem depth_5 : DepthLowerBound 5 3 := depthLowerBound (by decide)
theorem depth_6 : DepthLowerBound 6 3 := depthLowerBound (by decide)
theorem depth_7 : DepthLowerBound 7 3 := depthLowerBound (by decide)
theorem depth_8 : DepthLowerBound 8 3 := depthLowerBound (by decide)
theorem depth_9 : DepthLowerBound 9 4 := depthLowerBound (by decide)
theorem depth_10 : DepthLowerBound 10 4 := depthLowerBound (by decide)
theorem depth_11 : DepthLowerBound 11 4 := depthLowerBound (by decide)
theorem depth_12 : DepthLowerBound 12 4 := depthLowerBound (by decide)
theorem depth_13 : DepthLowerBound 13 4 := depthLowerBound (by decide)
theorem depth_14 : DepthLowerBound 14 4 := depthLowerBound (by decide)
theorem depth_15 : DepthLowerBound 15 4 := depthLowerBound (by decide)
theorem depth_16 : DepthLowerBound 16 4 := depthLowerBound (by decide)
theorem depth_17 : DepthLowerBound 17 5 := depthLowerBound (by decide)
theorem depth_18 : DepthLowerBound 18 5 := depthLowerBound (by decide)
theorem depth_19 : DepthLowerBound 19 5 := depthLowerBound (by decide)
theorem depth_20 : DepthLowerBound 20 5 := depthLowerBound (by decide)
theorem depth_21 : DepthLowerBound 21 5 := depthLowerBound (by decide)
theorem depth_22 : DepthLowerBound 22 5 := depthLowerBound (by decide)
theorem depth_23 : DepthLowerBound 23 5 := depthLowerBound (by decide)
theorem depth_24 : DepthLowerBound 24 5 := depthLowerBound (by decide)
theorem depth_25 : DepthLowerBound 25 5 := depthLowerBound (by decide)
theorem depth_26 : DepthLowerBound 26 5 := depthLowerBound (by decide)
theorem depth_27 : DepthLowerBound 27 5 := depthLowerBound (by decide)
theorem depth_28 : DepthLowerBound 28 5 := depthLowerBound (by decide)
theorem depth_29 : DepthLowerBound 29 5 := depthLowerBound (by decide)
theorem depth_30 : DepthLowerBound 30 5 := depthLowerBound (by decide)
theorem depth_31 : DepthLowerBound 31 5 := depthLowerBound (by decide)
theorem depth_32 : DepthLowerBound 32 5 := depthLowerBound (by decide)

end LeapsInBounds.Proofs.SortingNetworkLower
