/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/MinSpacing.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.RefiCo
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Insert
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Merge
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerOne.Map

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc


/-- In an interval of length L, a set of points with pairwise spacing ≥ h
contains at most ⌊L/h⌋ + 1 points. Proved by injecting into Finset.range
via x ↦ ⌊x/h⌋: separation ≥ h ensures injectivity, and x ≤ L ensures
all images land in {0, ..., ⌊L/h⌋}. -/
lemma points_in_interval_le {L h : ℝ} (hh : 0 < h) (_hL : 0 ≤ L)
    {pts : Finset ℝ}
    (hpts_in : ∀ x ∈ pts, 0 ≤ x ∧ x ≤ L)
    (hpts_sep : ∀ x y, x ∈ pts → y ∈ pts → x < y → h ≤ y - x) :
    pts.card ≤ Nat.floor (L / h) + 1 := by
  set N := Nat.floor (L / h) + 1
  set f := fun x => Nat.floor (x / h)
  -- f maps pts into range N
  have hf_mem : ∀ x ∈ pts, f x ∈ Finset.range N := by
    intro x hx
    simp only [f, N, Finset.mem_range]
    exact Nat.lt_succ_of_le
      (Nat.floor_le_floor (div_le_div_of_nonneg_right (hpts_in x hx).2 hh.le))
  -- f is injective on pts (separation ≥ h ⟹ distinct floors)
  have hf_inj : Set.InjOn f ↑pts := by
    intro x hx y hy heq
    by_contra hne
    have hlt : x < y ∨ y < x := lt_or_gt_of_ne hne
    rcases hlt with hlt | hlt
    · have hsep := hpts_sep x y hx hy hlt
      have hx_nn : 0 ≤ x / h := div_nonneg (hpts_in x hx).1 hh.le
      have : Nat.floor (x / h) + 1 ≤ Nat.floor (y / h) := by
        rw [← Nat.floor_add_one hx_nn]
        apply Nat.floor_le_floor
        rw [div_add_one hh.ne']
        exact div_le_div_of_nonneg_right (by linarith) hh.le
      linarith
    · have hsep := hpts_sep y x hy hx hlt
      have hy_nn : 0 ≤ y / h := div_nonneg (hpts_in y hy).1 hh.le
      have : Nat.floor (y / h) + 1 ≤ Nat.floor (x / h) := by
        rw [← Nat.floor_add_one hy_nn]
        apply Nat.floor_le_floor
        rw [div_add_one hh.ne']
        exact div_le_div_of_nonneg_right (by linarith) hh.le
      linarith
  -- Conclude: card(pts) = card(image f) ≤ card(range N) = N
  calc pts.card
      = (pts.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (Finset.range N).card := Finset.card_le_card
        (Finset.image_subset_iff.mpr hf_mem)
    _ = N := Finset.card_range N


/-- Like merge_gap_of_min_spacing but takes strict step only at index k. -/
theorem merge_gap_of_min_spacing {s t : ℝ} (P₁ P₂ : Partition s t)
    (hP₁n : 0 < P₁.n)
    (φ : Fin (P₁.n + 1) → Fin ((P₁.merge P₂).n + 1))
    (hφ_val : ∀ i, (P₁.merge P₂).pts (φ i) = P₁.pts i)
    (hφ_mono : Monotone φ)
    (_hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (_hφ_end : φ ⟨P₁.n, by omega⟩ = ⟨(P₁.merge P₂).n, by omega⟩)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (hP₂_sep : ∀ i j : Fin (P₂.n + 1), P₂.pts i < P₂.pts j →
      h ≤ P₂.pts j - P₂.pts i)
    (hP₁_block : ∀ k : Fin P₁.n, P₁.right k - P₁.left k ≤ L)
    (k : Fin P₁.n)
    (hk_strict : (φ ⟨k.val, by omega⟩).val < (φ ⟨k.val + 1, by omega⟩).val) :
    (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤
      Nat.floor (L / h) + 2 := by

  have hlo_le_j : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      (φ ⟨k.val, by omega⟩).val ≤ min j (P₁.merge P₂).n := by
    intro j hj; have := (Finset.mem_Ico.mp hj).1; omega

  have hj_le_hi : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      min j (P₁.merge P₂).n ≤ (φ ⟨k.val + 1, by omega⟩).val := by
    intro j hj
    have := (Finset.mem_Ico.mp hj).2
    have := (φ ⟨k.val + 1, by omega⟩).isLt
    omega

  have hS_left : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      P₁.left k ≤ (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩ := by
    intro j hj
    calc P₁.left k
        = (P₁.merge P₂).pts (φ ⟨k.val, by omega⟩) := (hφ_val _).symm
      _ ≤ (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩ :=
          (P₁.merge P₂).mono (Fin.mk_le_mk.mpr (hlo_le_j j hj))

  have hS_right : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩ ≤ P₁.right k := by
    intro j hj
    calc (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩
        ≤ (P₁.merge P₂).pts (φ ⟨k.val + 1, by omega⟩) :=
          (P₁.merge P₂).mono (Fin.mk_le_mk.mpr (hj_le_hi j hj))
      _ = P₁.right k := hφ_val _

  have hlo_lt_hi : (φ ⟨k.val, by omega⟩).val < (φ ⟨k.val + 1, by omega⟩).val :=
    hk_strict

  have hS_P₂ : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      ∃ i : Fin (P₂.n + 1),
        (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩ = P₂.pts i := by
    intro j hj_mem
    have hj_range := Finset.mem_Ico.mp hj_mem
    have hj_lt : j < (P₁.merge P₂).n + 1 := by
      have := (φ ⟨k.val + 1, by omega⟩).isLt; omega
    have hj_eq : min j (P₁.merge P₂).n = j := Nat.min_eq_left (by omega)
    rcases Partition.merge_pts_mem_union P₁ P₂ ⟨j, hj_lt⟩ with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- Impossible: merge.pts j = P₁.pts i means φ(i) maps to j
      exfalso
      have hφi : (P₁.merge P₂).pts (φ i) = (P₁.merge P₂).pts ⟨j, hj_lt⟩ := by
        rw [hφ_val]; exact hi.symm
      -- φ(i).val = j by strict mono injectivity
      have hφi_eq : (φ i).val = j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd hφi (ne_of_lt (Partition.merge_pts_strict_mono P₁ P₂
            (Fin.mk_lt_mk.mpr hlt)))
        · exact absurd hφi (ne_of_gt (Partition.merge_pts_strict_mono P₁ P₂
            (Fin.mk_lt_mk.mpr hlt)))
      -- lo < φ(i) < hi, so k < i < k+1, impossible
      have : (φ ⟨k.val, by omega⟩).val < (φ i).val := by omega
      have : (φ i).val < (φ ⟨k.val + 1, by omega⟩).val := by omega
      have hk_lt_i : k.val < i.val := by
        by_contra h; push_neg at h
        have := hφ_mono (show i ≤ ⟨k.val, by omega⟩ from Fin.mk_le_mk.mpr h)
        omega
      have hi_lt_k1 : i.val < k.val + 1 := by
        by_contra h; push_neg at h
        have := hφ_mono (show ⟨k.val + 1, by omega⟩ ≤ i from Fin.mk_le_mk.mpr h)
        omega
      omega
    · refine ⟨i, ?_⟩
      convert hi using 2
      simp [Nat.min_eq_left (by omega : j ≤ (P₁.merge P₂).n)]

  set lo := (φ ⟨k.val, by omega⟩).val
  set hi := (φ ⟨k.val + 1, by omega⟩).val
  have hhi_lt : hi < (P₁.merge P₂).n + 1 := (φ ⟨k.val + 1, by omega⟩).isLt
  set M := P₁.merge P₂

  have hM_inj : ∀ j₁ j₂ : ℕ, (hj₁ : j₁ < M.n + 1) → (hj₂ : j₂ < M.n + 1) →
      M.pts ⟨j₁, hj₁⟩ = M.pts ⟨j₂, hj₂⟩ → j₁ = j₂ := by
    intro j₁ j₂ hj₁ hj₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq (ne_of_lt (Partition.merge_pts_strict_mono P₁ P₂
        (Fin.mk_lt_mk.mpr hlt)))
    · exact absurd heq (ne_of_gt (Partition.merge_pts_strict_mono P₁ P₂
        (Fin.mk_lt_mk.mpr hlt)))
  let S := (Finset.Ico (lo + 1) hi).image
    (fun j => (P₁.merge P₂).pts ⟨min j (P₁.merge P₂).n, by omega⟩)

  have hS_card : S.card = hi - lo - 1 := by
    show ((Finset.Ico (lo + 1) hi).image _).card = _
    rw [Finset.card_image_of_injOn]
    · have := hlo_lt_hi;
        exact Nat.card_Ico (lo + 1) hi
    · intro j₁ hj₁ j₂ hj₂ heq
      have h₁ := (Finset.mem_Ico.mp hj₁).2
      have h₂ := (Finset.mem_Ico.mp hj₂).2
      have hj₁_eq : min j₁ (P₁.merge P₂).n = j₁ := Nat.min_eq_left (by omega)
      have hj₂_eq : min j₂ (P₁.merge P₂).n = j₂ := Nat.min_eq_left (by omega)
      have : j₁ = j₂ := hM_inj j₁ j₂ (by omega) (by omega) (by
        simp only [hj₁_eq, hj₂_eq] at heq; exact heq)
      exact this

  -- S elements lie in [P₁.left k, P₁.right k]
  have hS_in : ∀ x ∈ S, P₁.left k ≤ x ∧ x ≤ P₁.right k := by
    intro x hx
    obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hS_left j hj_mem, hS_right j hj_mem⟩

  -- S elements are P₂ points (not P₁ points, by strict mono of φ)
  -- After set lo/hi/S:
  have hS_is_P₂ : ∀ x ∈ S, ∃ i : Fin (P₂.n + 1), x = P₂.pts i := by
    intro x hx
    obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hx
    exact hS_P₂ j hj_mem

  -- S elements have pairwise distance ≥ h
  have hS_sep : ∀ x y, x ∈ S → y ∈ S → x < y → h ≤ y - x := by
    intro x y hx hy hxy
    obtain ⟨jx, hjx_mem, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨jy, hjy_mem, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨ix, hix⟩ := hS_P₂ jx hjx_mem
    obtain ⟨iy, hiy⟩ := hS_P₂ jy hjy_mem
    rw [hix, hiy] at hxy ⊢
    exact hP₂_sep ix iy hxy
  -- Shift to [0, L] for points_in_interval_le
  set S' := S.image (fun x => x - P₁.left k)
  have hS'_card : S'.card = S.card := by
    apply Finset.card_image_of_injective
    intro a b hab; linarith

  have hS'_in : ∀ x ∈ S', 0 ≤ x ∧ x ≤ L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨by linarith [(hS_in y hy).1], by linarith [(hS_in y hy).2, hP₁_block k]⟩

  have hS'_sep : ∀ x y, x ∈ S' → y ∈ S' → x < y → h ≤ y - x := by
    intro x y hx hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    have : x' < y' := by linarith
    have := hS_sep x' y' hx' hy' this
    linarith

  -- Apply points_in_interval_le
  have hcount := points_in_interval_le hh hL hS'_in hS'_sep
  -- gap - 1 = S.card ≤ ⌊L/h⌋ + 1
  rw [hS'_card, hS_card] at hcount
  omega





  end StochCalc
