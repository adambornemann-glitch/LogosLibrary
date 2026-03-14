/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/Merge.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Unique

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc
/-! ### Common refinement (merge) of two partitions -/

section Merge

/-- The combined point set of two partitions. -/
private noncomputable def mergeFinset {s t : ℝ} (P₁ P₂ : Partition s t) : Finset ℝ :=
  Finset.image P₁.pts Finset.univ ∪ Finset.image P₂.pts Finset.univ

private theorem s_mem_mergeFinset {s t : ℝ} (P₁ P₂ : Partition s t) :
    s ∈ mergeFinset P₁ P₂ := by
  unfold mergeFinset
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  exact ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, P₁.first⟩

private theorem t_mem_mergeFinset {s t : ℝ} (P₁ P₂ : Partition s t) :
    t ∈ mergeFinset P₁ P₂ := by
  unfold mergeFinset
  apply Finset.mem_union_left
  rw [Finset.mem_image]
  exact ⟨⟨P₁.n, Nat.lt_succ_self _⟩, Finset.mem_univ _, P₁.last⟩

private theorem mergeFinset_nonempty {s t : ℝ} (P₁ P₂ : Partition s t) :
    (mergeFinset P₁ P₂).Nonempty :=
  ⟨s, s_mem_mergeFinset P₁ P₂⟩

private theorem s_le_mergeFinset {s t : ℝ} (P₁ P₂ : Partition s t) :
    ∀ x ∈ mergeFinset P₁ P₂, s ≤ x := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h <;> {
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    calc s = Partition.pts _ ⟨0, by omega⟩ := Partition.first .. |>.symm
      _ ≤ _ := Partition.mono _ (Fin.zero_le i) }

private theorem mergeFinset_le_t {s t : ℝ} (P₁ P₂ : Partition s t) :
    ∀ x ∈ mergeFinset P₁ P₂, x ≤ t := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h <;> {
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    calc _ ≤ Partition.pts _ ⟨Partition.n _, by omega⟩ := Partition.mono _ (Fin.le_last i)
      _ = t := Partition.last _ }

/-- The sorted list of merged partition points. -/
private noncomputable def mergeSorted {s t : ℝ} (P₁ P₂ : Partition s t) : List ℝ :=
  (mergeFinset P₁ P₂).sort (· ≤ ·)

private theorem mergeSorted_length {s t : ℝ} (P₁ P₂ : Partition s t) :
    (mergeSorted P₁ P₂).length = (mergeFinset P₁ P₂).card :=
  Finset.length_sort _

private theorem mergeSorted_pos {s t : ℝ} (P₁ P₂ : Partition s t) :
    0 < (mergeSorted P₁ P₂).length := by
  rw [mergeSorted_length]
  exact Finset.card_pos.mpr (mergeFinset_nonempty P₁ P₂)

private theorem mergeSorted_sorted {s t : ℝ} (P₁ P₂ : Partition s t) :
    List.SortedLT (mergeSorted P₁ P₂) :=
  Finset.sortedLT_sort _

private theorem mem_mergeSorted_iff {s t : ℝ} (P₁ P₂ : Partition s t) (x : ℝ) :
    x ∈ mergeSorted P₁ P₂ ↔ x ∈ mergeFinset P₁ P₂ :=
  Finset.mem_sort _

/-- The **common refinement** of two partitions: the partition whose points
are the union of both input partitions' points.

Constructed by collecting all points into a `Finset`, sorting, and converting
to a `Fin`-indexed monotone function. -/
noncomputable def Partition.merge {s t : ℝ} (P₁ P₂ : Partition s t) : Partition s t := by
  let L := mergeSorted P₁ P₂
  have hL_pos := mergeSorted_pos P₁ P₂
  exact
  { n := L.length - 1
    pts := fun i => L.get ⟨i.val, by lia⟩
    mono := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ (hij : i ≤ j)
      show L.get ⟨i, by lia⟩ ≤ L.get ⟨j, by lia⟩
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · exact le_of_lt (List.Pairwise.rel_get_of_lt (mergeSorted_sorted P₁ P₂).pairwise
          (Fin.mk_lt_mk.mpr hlt))
    first := by
      show L.get ⟨0, by omega⟩ = s
      apply le_antisymm
      · -- L[0] ≤ s: s is in L at some index j, and L[0] ≤ L[j] = s
        have hs_mem : s ∈ L := (Finset.mem_sort (· ≤ ·)).mpr (s_mem_mergeFinset P₁ P₂)
        obtain ⟨⟨j, hj⟩, hget⟩ := List.mem_iff_get.mp hs_mem
        rcases Nat.eq_or_lt_of_le (Nat.zero_le j) with rfl | hlt
        · exact le_of_eq hget
        · exact le_of_lt ((List.Pairwise.rel_get_of_lt (mergeSorted_sorted P₁ P₂).pairwise
              (Fin.mk_lt_mk.mpr hlt)).trans_eq hget)
      · -- s ≤ L[0]: every element of mergeFinset is ≥ s, and L[0] ∈ mergeFinset
        apply s_le_mergeFinset
        rw [← Finset.mem_sort (· ≤ ·)]
        exact List.get_mem ((mergeFinset P₁ P₂).sort fun x1 x2 => x1 ≤ x2) ⟨0, hL_pos⟩
    last := by
      show L.get ⟨L.length - 1, by lia⟩ = t
      apply le_antisymm
      · -- L[last] ≤ t: all elements of L are ≤ t
        apply mergeFinset_le_t
        rw [← Finset.mem_sort (· ≤ ·)]
        exact
          List.get_mem ((mergeFinset P₁ P₂).sort fun x1 x2 => x1 ≤ x2)
            ⟨L.length - 1, merge._proof_5 P₁ P₂ hL_pos⟩
      · -- t ≤ L[last]: t is in L at index j, and L[j] ≤ L[last]
        have ht_mem : t ∈ L := (Finset.mem_sort (· ≤ ·)).mpr (t_mem_mergeFinset P₁ P₂)
        obtain ⟨⟨j, hj⟩, hget⟩ := List.mem_iff_get.mp ht_mem
        rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hj) with rfl | hlt
        · exact le_of_eq hget.symm
        · exact hget.symm.le.trans (le_of_lt (List.Pairwise.rel_get_of_lt
          (mergeSorted_sorted P₁ P₂).pairwise
          (Fin.mk_lt_mk.mpr hlt)))}

/-- The merge refines the first partition. -/
theorem Partition.merge_refines_left {s t : ℝ}
    (P₁ P₂ : Partition s t) :
    (P₁.merge P₂).IsRefinement P₁ := by
  intro i
  -- P₁.pts i ∈ mergeFinset, hence ∈ mergeSorted, hence = some merge point
  have hmem : P₁.pts i ∈ mergeSorted P₁ P₂ :=
    (mem_mergeSorted_iff P₁ P₂ _).mpr
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  obtain ⟨⟨j, hj⟩, hval⟩ := List.mem_iff_get.mp hmem
  exact ⟨⟨j, by simp only [Partition.merge]; omega⟩, by
    simp only [Partition.merge]; exact hval⟩

/-- The merge refines the second partition. -/
theorem Partition.merge_refines_right {s t : ℝ}
    (P₁ P₂ : Partition s t) :
    (P₁.merge P₂).IsRefinement P₂ := by
  intro i
  have hmem : P₂.pts i ∈ mergeSorted P₁ P₂ :=
    (mem_mergeSorted_iff P₁ P₂ _).mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  obtain ⟨⟨j, hj⟩, hval⟩ := List.mem_iff_get.mp hmem
  exact ⟨⟨j, by simp only [Partition.merge]; omega⟩, by
    simp only [Partition.merge]; exact hval⟩

/-- **Point count bound for merge**: the merge has at most `P₁.n + P₂.n + 1` sub-intervals.

The merge's point set is the union of two Finsets of sizes `P₁.n + 1` and `P₂.n + 1`.
After deduplication and sorting, the number of distinct points is at most
`(P₁.n + 1) + (P₂.n + 1) = P₁.n + P₂.n + 2`, giving at most `P₁.n + P₂.n + 1`
sub-intervals. -/
theorem Partition.n_merge_le {s t : ℝ} (P₁ P₂ : Partition s t) :
    (P₁.merge P₂).n ≤ P₁.n + P₂.n + 1 := by
  show (mergeSorted P₁ P₂).length - 1 ≤ P₁.n + P₂.n + 1
  rw [mergeSorted_length]
  have hcard : (mergeFinset P₁ P₂).card ≤ (P₁.n + 1) + (P₂.n + 1) := by
    calc (mergeFinset P₁ P₂).card
        ≤ (Finset.image P₁.pts Finset.univ).card +
          (Finset.image P₂.pts Finset.univ).card :=
          Finset.card_union_le _ _
      _ ≤ (P₁.n + 1) + (P₂.n + 1) := by
          apply Nat.add_le_add
          · calc (Finset.image P₁.pts Finset.univ).card
                ≤ Finset.univ.card := Finset.card_image_le
              _ = P₁.n + 1 := Finset.card_fin _
          · calc (Finset.image P₂.pts Finset.univ).card
                ≤ Finset.univ.card := Finset.card_image_le
              _ = P₂.n + 1 := Finset.card_fin _
  omega

end Merge

end StochCalc
