module

public import LeapsInBounds.Statements.Folding
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the foldings of a few stamps

A folding of a strip of `n` stamps is determined by the levels of its stamps,
`ℓ (0, 0), …, ℓ (0, n - 1)`, a permutation of `0, …, n - 1` in which no two
creases on the same edge cross. So the number of foldings is at most the number
of such permutations, which the kernel counts (`decide +kernel`, no
`native_decide`) by listing all permutations and keeping those whose creases
don't cross. This gives the exact counts as upper bounds for `n ≤ 7`; listing
the `8!` permutations of eight stamps takes too long in the kernel.
-/

@[expose] public section

namespace LeapsInBounds.Proofs.StampFoldingCount

open Folding

/-- The lists obtained by inserting `a` at each position of a list. -/
def insertAll (a : ℕ) : List ℕ → List (List ℕ)
  | [] => [[a]]
  | b :: t => (a :: b :: t) :: (insertAll a t).map (b :: ·)

/-- All permutations of a list, by inserting the head at each position of each
permutation of the tail. -/
def perms : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertAll a)

/-- `Cross` as a boolean. -/
def crossb (a b c d : ℕ) : Bool :=
  (min a b < min c d && min c d < max a b && max a b < max c d) ||
    (min c d < min a b && min a b < max c d && max c d < max a b)

/-- No two creases on the same edge cross, for the stamps at levels `L`: the
crease after stamp `i` and the one after stamp `j` are on the same edge when
`i` and `j` have the same parity. -/
def ok (L : List ℕ) : Bool :=
  (List.range (L.length - 1)).all fun i => (List.range (L.length - 1)).all fun j =>
    i % 2 != j % 2 || !crossb (L.getD i 0) (L.getD (i + 1) 0) (L.getD j 0) (L.getD (j + 1) 0)

theorem crossb_iff {a b c d : ℕ} : crossb a b c d = true ↔ Cross a b c d := by
  simp only [crossb, Cross, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem mem_insertAll_erase {a : ℕ} : ∀ {L : List ℕ}, a ∈ L → L ∈ insertAll a (L.erase a)
  | [], h => by simp at h
  | b :: t, h => by
    by_cases hb : b = a
    · subst hb
      cases t <;> simp [insertAll]
    · have ht : a ∈ t := by simpa [Ne.symm hb] using h
      rw [List.erase_cons_tail (by simpa using hb)]
      simp only [insertAll, List.mem_cons, List.mem_map]
      exact Or.inr ⟨t, mem_insertAll_erase ht, rfl⟩

theorem mem_perms : ∀ {l L : List ℕ}, L.Perm l → L ∈ perms l
  | [], L, h => by simp [perms, h.eq_nil]
  | a :: l, L, h => by
    have ha : a ∈ L := h.symm.subset List.mem_cons_self
    have h' : (L.erase a).Perm l := ((List.perm_cons_erase ha).symm.trans h).cons_inv
    simp only [perms, List.mem_flatMap]
    exact ⟨L.erase a, mem_perms h', mem_insertAll_erase ha⟩

variable {n : ℕ}

/-- The levels of the stamps of a stack. -/
def levels (ℓ : Fin 1 × Fin n ≃ Fin (1 * n)) : List ℕ :=
  List.ofFn fun i : Fin n => (ℓ (0, i) : ℕ)

theorem levels_perm (ℓ : Fin 1 × Fin n ≃ Fin (1 * n)) : (levels ℓ).Perm (List.range n) := by
  have hinj : Function.Injective fun i : Fin n => (ℓ (0, i) : ℕ) := by
    intro i j h
    have := ℓ.injective (Fin.ext h)
    simpa using this
  unfold levels
  rw [List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr hinj) List.nodup_range]
  intro a
  simp only [List.mem_ofFn, List.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    simpa using (ℓ (0, i)).isLt
  · intro ha
    refine ⟨(ℓ.symm ⟨a, by simpa using ha⟩).2, ?_⟩
    have : ((0 : Fin 1), (ℓ.symm ⟨a, by simpa using ha⟩).2) = ℓ.symm ⟨a, by simpa using ha⟩ :=
      Prod.ext (Subsingleton.elim _ _) rfl
    rw [this, ℓ.apply_symm_apply]

theorem levels_injective : Function.Injective (levels (n := n)) := by
  intro ℓ ℓ' h
  have h' := List.ofFn_injective h
  ext x
  have hx : x = ((0 : Fin 1), x.2) := Prod.ext (Subsingleton.elim _ _) rfl
  rw [hx]
  exact congrFun h' x.2

theorem ok_levels {ℓ : Fin 1 × Fin n ≃ Fin (1 * n)} (h : IsFolding ℓ) : ok (levels ℓ) = true := by
  have hlen : (levels ℓ).length = n := by simp [levels]
  simp only [ok, hlen, List.all_eq_true, List.mem_range]
  intro i hi j hj
  by_cases hp : i % 2 = j % 2
  · have hc : ¬crossb ((levels ℓ).getD i 0) ((levels ℓ).getD (i + 1) 0)
        ((levels ℓ).getD j 0) ((levels ℓ).getD (j + 1) 0) = true := by
      rw [crossb_iff]
      have := h.2 (0, ⟨i, by omega⟩) (0, ⟨i + 1, by omega⟩) (0, ⟨j, by omega⟩) (0, ⟨j + 1, by omega⟩)
        rfl rfl rfl rfl hp
      simpa [levels, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, hj,
        show i < n by omega, show j < n by omega, show i + 1 < n by omega,
        show j + 1 < n by omega] using this
    cases hcb : crossb ((levels ℓ).getD i 0) ((levels ℓ).getD (i + 1) 0)
        ((levels ℓ).getD j 0) ((levels ℓ).getD (j + 1) 0)
    · simp only [hp, bne_self_eq_false, Bool.not_false, Bool.or_true]
    · exact absurd hcb hc
  · simp [hp]

/-- The number of foldings of `n` stamps is at most the number of permutations
of their levels whose creases don't cross. -/
theorem upper_of_count (n N : ℕ) (hN : ((perms (List.range n)).filter ok).length ≤ N) :
    StampUpperBound n N := by
  unfold StampUpperBound UpperBound count
  let S : Finset (List ℕ) := ((perms (List.range n)).filter ok).toFinset
  let f : {ℓ : Fin 1 × Fin n ≃ Fin (1 * n) // IsFolding ℓ} → S := fun ℓ =>
    ⟨levels ℓ.1, by
      simp only [S, List.mem_toFinset, List.mem_filter]
      exact ⟨mem_perms (levels_perm ℓ.1), ok_levels ℓ.2⟩⟩
  have hf : Function.Injective f := by
    intro ℓ ℓ' h
    exact Subtype.ext (levels_injective (congrArg Subtype.val h))
  calc Nat.card {ℓ : Fin 1 × Fin n ≃ Fin (1 * n) // IsFolding ℓ}
      ≤ Nat.card S := Nat.card_le_card_of_injective f hf
    _ = S.card := Nat.card_eq_finsetCard S
    _ ≤ ((perms (List.range n)).filter ok).length := List.toFinset_card_le _
    _ ≤ N := hN

set_option maxRecDepth 100000

theorem upper_four : StampUpperBound 4 16 := upper_of_count 4 16 (by decide +kernel)

theorem upper_five : StampUpperBound 5 50 := upper_of_count 5 50 (by decide +kernel)

theorem upper_six : StampUpperBound 6 144 := upper_of_count 6 144 (by decide +kernel)

theorem upper_seven : StampUpperBound 7 462 := upper_of_count 7 462 (by decide +kernel)

end LeapsInBounds.Proofs.StampFoldingCount
