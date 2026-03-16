/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Additive.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.MinSpacing

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc


lemma points_in_interval_le_with_exceptions {L h : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    {good bad : Finset ℝ}
    (hgood_in : ∀ x ∈ good, 0 ≤ x ∧ x ≤ L)
    (hgood_sep : ∀ x y, x ∈ good → y ∈ good → x < y → h ≤ y - x)
    (_hbad_in : ∀ x ∈ bad, 0 ≤ x ∧ x ≤ L) :
    (good ∪ bad).card ≤ Nat.floor (L / h) + 1 + bad.card := by
  calc (good ∪ bad).card
      ≤ good.card + bad.card := Finset.card_union_le good bad
    _ ≤ (Nat.floor (L / h) + 1) + bad.card :=
        Nat.add_le_add_right (points_in_interval_le hh hL hgood_in hgood_sep) _


/-- Triangle through common refinement: the RS difference of two partitions
is bounded by the refinement costs to their merge. -/
theorem riemannSum_comparison_bound
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hub : u ≤ b)
    (P₁ P₂ : Partition s u)
    (hP₁n : 0 < P₁.n) (hP₂n : 0 < P₂.n)
    (φ₁ : Fin (P₁.n + 1) → Fin ((P₁.merge P₂).n + 1))
    (hφ₁_val : ∀ i, (P₁.merge P₂).pts (φ₁ i) = P₁.pts i)
    (hφ₁_mono : Monotone φ₁)
    (hφ₁_start : φ₁ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hφ₁_end : φ₁ ⟨P₁.n, by omega⟩ = ⟨(P₁.merge P₂).n, by omega⟩)
    {M₁ : ℕ} (hM₁ : ∀ k : Fin P₁.n,
      (φ₁ ⟨k.val + 1, by omega⟩).val - (φ₁ ⟨k.val, by omega⟩).val ≤ M₁)
    (φ₂ : Fin (P₂.n + 1) → Fin ((P₁.merge P₂).n + 1))
    (hφ₂_val : ∀ i, (P₁.merge P₂).pts (φ₂ i) = P₂.pts i)
    (hφ₂_mono : Monotone φ₂)
    (hφ₂_start : φ₂ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (hφ₂_end : φ₂ ⟨P₂.n, by omega⟩ = ⟨(P₁.merge P₂).n, by omega⟩)
    {M₂ : ℕ} (hM₂ : ∀ k : Fin P₂.n,
      (φ₂ ⟨k.val + 1, by omega⟩).val - (φ₂ ⟨k.val, by omega⟩).val ≤ M₂) :
    ‖riemannSum Ξ P₁ - riemannSum Ξ P₂‖ ≤
      ↑(M₁ - 1) * (K * thetaEnergy ω θ P₁) +
      ↑(M₂ - 1) * (K * thetaEnergy ω θ P₂) := by
  calc ‖riemannSum Ξ P₁ - riemannSum Ξ P₂‖
      ≤ ‖riemannSum Ξ P₁ - riemannSum Ξ (P₁.merge P₂)‖ +
        ‖riemannSum Ξ (P₁.merge P₂) - riemannSum Ξ P₂‖ := by
        rw [show riemannSum Ξ P₁ - riemannSum Ξ P₂ =
          (riemannSum Ξ P₁ - riemannSum Ξ (P₁.merge P₂)) +
          (riemannSum Ξ (P₁.merge P₂) - riemannSum Ξ P₂) from by abel]
        exact norm_add_le _ _
    _ ≤ ↑(M₁ - 1) * (K * thetaEnergy ω θ P₁) +
        ↑(M₂ - 1) * (K * thetaEnergy ω θ P₂) := by
        apply add_le_add
        · exact riemannSum_refinement_bound₃ hΞ has hsu hub hP₁n
            φ₁ hφ₁_val hφ₁_mono hφ₁_start hφ₁_end hM₁
        · rw [norm_sub_rev]
          exact riemannSum_refinement_bound₃ hΞ has hsu hub hP₂n
            φ₂ hφ₂_val hφ₂_mono hφ₂_start hφ₂_end hM₂

/-- Generalized gap bound: works for any refinement P' with strict monotone
pts and the union-source property. -/
theorem refinement_gap_with_exceptions
    {s t : ℝ} {P₁ P₂ P' : Partition s t}
    (hP₁n : 0 < P₁.n)
    (hP'_strict : ∀ {i j : Fin (P'.n + 1)}, i < j → P'.pts i < P'.pts j)
    (hP'_union : ∀ j : Fin (P'.n + 1),
      (∃ i : Fin (P₁.n + 1), P'.pts j = P₁.pts i) ∨
      (∃ i : Fin (P₂.n + 1), P'.pts j = P₂.pts i))
    (φ : Fin (P₁.n + 1) → Fin (P'.n + 1))
    (hφ_val : ∀ i, P'.pts (φ i) = P₁.pts i)
    (hφ_mono : Monotone φ)
    (_hφ_start : φ ⟨0, by omega⟩ = ⟨0, by omega⟩)
    (_hφ_end : φ ⟨P₁.n, by omega⟩ = ⟨P'.n, by omega⟩)
    {h L : ℝ} (hh : 0 < h) (hL : 0 ≤ L)
    (good : Finset (Fin (P₂.n + 1)))
    (hgood_sep : ∀ i ∈ good, ∀ j ∈ good, P₂.pts i < P₂.pts j →
      h ≤ P₂.pts j - P₂.pts i)
    {m : ℕ} (hbad : (Finset.univ \ good).card ≤ m)
    (hP₁_block : ∀ k : Fin P₁.n, P₁.right k - P₁.left k ≤ L)
    (k : Fin P₁.n)
    (hk_strict : (φ ⟨k.val, by omega⟩).val < (φ ⟨k.val + 1, by omega⟩).val) :
    (φ ⟨k.val + 1, by omega⟩).val - (φ ⟨k.val, by omega⟩).val ≤
      Nat.floor (L / h) + m + 2 := by

    -- All helpers BEFORE set, using raw expressions
  have hlo_lt_hi : (φ ⟨k.val, by omega⟩).val < (φ ⟨k.val + 1, by omega⟩).val :=
    hk_strict

  have hhi_lt : (φ ⟨k.val + 1, by omega⟩).val < P'.n + 1 :=
    (φ ⟨k.val + 1, by omega⟩).isLt

  have hJ_le : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val → j ≤ P'.n := by
    intro j hj; have := (Finset.mem_Ico.mp hj).2; have := hhi_lt; omega

  have hJ_left : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      P₁.left k ≤ P'.pts ⟨min j P'.n, by omega⟩ := by
    intro j hj
    have hj_eq : min j P'.n = j := Nat.min_eq_left (by
      have := (Finset.mem_Ico.mp hj).2; have := hhi_lt; omega)
    rw [show (⟨min j P'.n, _⟩ : Fin _) = ⟨j, by have := hhi_lt; omega⟩ from
      Fin.ext hj_eq]
    calc P₁.left k
        = P'.pts (φ ⟨k.val, by omega⟩) := (hφ_val _).symm
      _ ≤ P'.pts ⟨j, by have := hhi_lt; omega⟩ :=
          P'.mono (Fin.mk_le_mk.mpr
            (by have := (Finset.mem_Ico.mp hj).1; omega))

  have hJ_right : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      P'.pts ⟨min j P'.n, by omega⟩ ≤ P₁.right k := by
    intro j hj
    have hj_eq : min j P'.n = j := Nat.min_eq_left (by
      have := (Finset.mem_Ico.mp hj).2; have := hhi_lt; omega)
    rw [show (⟨min j P'.n, _⟩ : Fin _) = ⟨j, by omega⟩ from
      Fin.ext hj_eq]
    calc P'.pts ⟨j, by omega⟩
        ≤ P'.pts (φ ⟨k.val + 1, by omega⟩) :=
          P'.mono (Fin.mk_le_mk.mpr
            (by have := (Finset.mem_Ico.mp hj).2; omega))
      _ = P₁.right k := hφ_val _

  -- Merge pts injective
  have hM_inj : ∀ j₁ j₂, j₁ ≤ P'.n → j₂ ≤ P'.n →
      P'.pts ⟨min j₁ P'.n, by omega⟩ =
      P'.pts ⟨min j₂ P'.n, by omega⟩ →
      j₁ = j₂ := by
    intro j₁ j₂ h₁ h₂ heq
    have hj₁_eq : min j₁ P'.n = j₁ := Nat.min_eq_left h₁
    have hj₂_eq : min j₂ P'.n = j₂ := Nat.min_eq_left h₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq (ne_of_lt (hP'_strict
        (Fin.mk_lt_mk.mpr (by omega))))
    · exact absurd heq (ne_of_gt (hP'_strict
        (Fin.mk_lt_mk.mpr (by omega))))

  -- Every j ∈ J maps to a P₂ point
  have hJ_P₂ : ∀ j, j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val →
      ∃ i : Fin (P₂.n + 1),
        P'.pts ⟨min j P'.n, by omega⟩ = P₂.pts i := by
    intro j hj_mem
    have hj_range := Finset.mem_Ico.mp hj_mem
    have hj_le : j ≤ P'.n := by omega
    have hj_eq : min j P'.n = j := Nat.min_eq_left hj_le
    have hj_lt : j < P'.n + 1 := by omega
    rw [show (⟨min j P'.n, _⟩ : Fin _) = ⟨j, hj_lt⟩ from Fin.ext hj_eq]
    rcases hP'_union ⟨j, hj_lt⟩ with ⟨i, hi⟩ | ⟨i, hi⟩
    · exfalso
      have hφi : P'.pts (φ i) = P'.pts ⟨j, hj_lt⟩ := by
        rw [hφ_val]; exact hi.symm
      have hφi_eq : (φ i).val = j := by
        by_contra hne; rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd hφi (ne_of_lt (hP'_strict
            (Fin.mk_lt_mk.mpr hlt)))
        · exact absurd hφi (ne_of_gt (hP'_strict
            (Fin.mk_lt_mk.mpr hlt)))
      have hk_lt_i : k.val < i.val := by
        by_contra hh; push_neg at hh
        have := hφ_mono (show i ≤ ⟨k.val, by omega⟩ from Fin.mk_le_mk.mpr hh); omega
      have hi_lt_k1 : i.val < k.val + 1 := by
        by_contra hh; push_neg at hh
        have := hφ_mono (show ⟨k.val + 1, by omega⟩ ≤ i from Fin.mk_le_mk.mpr hh); omega
      omega
    · exact ⟨i, hi⟩

  -- Choose P₂ index function (before set)
  have hJ_P₂_choice : ∀ j, (hj : j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val) →
      P'.pts ⟨min j P'.n, by omega⟩ =
        P₂.pts (hJ_P₂ j hj).choose := by
    intro j hj; exact (hJ_P₂ j hj).choose_spec
  -- ι: choose P₂ index (BEFORE set M/lo/hi)
  set ι : ℕ → Fin (P₂.n + 1) := fun j =>
    if hj : j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
        (φ ⟨k.val + 1, by omega⟩).val
    then (hJ_P₂ j hj).choose else ⟨0, Nat.zero_lt_succ _⟩

  have hι_spec : ∀ j, (hj : j ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1)
      (φ ⟨k.val + 1, by omega⟩).val) →
      P'.pts ⟨min j P'.n, by omega⟩ = P₂.pts (ι j) := by
    intro j hj; simp only [ι, dif_pos hj]; exact (hJ_P₂ j hj).choose_spec

  have hι_inj_raw : ∀ j₁ j₂,
      j₁ ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1) (φ ⟨k.val + 1, by omega⟩).val →
      j₂ ∈ Finset.Ico ((φ ⟨k.val, by omega⟩).val + 1) (φ ⟨k.val + 1, by omega⟩).val →
      ι j₁ = ι j₂ → j₁ = j₂ := by
    intro j₁ j₂ hj₁ hj₂ heq
    have h₁ := hJ_le j₁ hj₁
    have h₂ := hJ_le j₂ hj₂
    exact hM_inj j₁ j₂ h₁ h₂ (by rw [hι_spec j₁ hj₁, hι_spec j₂ hj₂, heq])

  -- Now set abbreviations
  --
  set lo := (φ ⟨k.val, by omega⟩).val
  set hi := (φ ⟨k.val + 1, by omega⟩).val
  set J := Finset.Ico (lo + 1) hi

  -- J.card
  have hJ_card : J.card = hi - lo - 1 := by
    show (Finset.Ico (lo + 1) hi).card = _
    rw [Nat.card_Ico]
    omega

  -- ι injective on J
  have hι_inj : Set.InjOn ι ↑J := by
    intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_coe, J, lo, hi] at hj₁ hj₂
    exact hι_inj_raw j₁ j₂ hj₁ hj₂ heq

  -- Split J into good and bad
  set J_good := J.filter (fun j => ι j ∈ good)
  set J_bad := J.filter (fun j => ι j ∉ good)

  have hJ_le_split : J.card ≤ J_good.card + J_bad.card :=
    calc J.card ≤ (J_good ∪ J_bad).card := Finset.card_le_card (by
            intro j hj; simp only [J_good, J_bad, Finset.mem_union, Finset.mem_filter]
            by_cases hg : ι j ∈ good
            · exact Or.inl ⟨hj, hg⟩
            · exact Or.inr ⟨hj, hg⟩)
      _ ≤ J_good.card + J_bad.card := Finset.card_union_le _ _

  set M := P₁.merge P₂
  -- Bound J_good via points_in_interval_le
  have hJ_good_bound : J_good.card ≤ Nat.floor (L / h) + 1 := by
    set img := J_good.image (fun j =>
      P'.pts ⟨min j P'.n, by omega⟩ - P₁.left k)
    have himg_card : img.card = J_good.card := by
      apply Finset.card_image_of_injOn
      intro j₁ hj₁ j₂ hj₂ heq
      have h1 : j₁ ∈ J := (Finset.mem_filter.mp hj₁).1
      have h2 : j₂ ∈ J := (Finset.mem_filter.mp hj₂).1
      simp only [J, lo, hi] at h1 h2
      have hle1 := hJ_le j₁ h1
      have hle2 := hJ_le j₂ h2
      exact hM_inj j₁ j₂ hle1 hle2 (by linarith)
    have himg_in : ∀ x ∈ img, 0 ≤ x ∧ x ≤ L := by
      intro x hx; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
      simp only [J, lo, hi] at hjJ
      exact ⟨by linarith [hJ_left j hjJ], by linarith [hJ_right j hjJ, hP₁_block k]⟩
    have himg_sep : ∀ x y, x ∈ img → y ∈ img → x < y → h ≤ y - x := by
      intro x y hx hy hxy
      obtain ⟨jx, hjx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨jy, hjy, rfl⟩ := Finset.mem_image.mp hy
      have hjxJ : jx ∈ J := (Finset.mem_filter.mp hjx).1
      have hjyJ : jy ∈ J := (Finset.mem_filter.mp hjy).1
      have hjx_good : ι jx ∈ good := (Finset.mem_filter.mp hjx).2
      have hjy_good : ι jy ∈ good := (Finset.mem_filter.mp hjy).2
      simp only [J, lo, hi] at hjxJ hjyJ
      have hgx := hι_spec jx hjxJ
      have hgy := hι_spec jy hjyJ
      have hlt : P₂.pts (ι jx) < P₂.pts (ι jy) := by linarith
      have hsep := hgood_sep _ hjx_good _ hjy_good hlt
      linarith
    rw [← himg_card]; exact points_in_interval_le hh hL himg_in himg_sep

  -- Bound J_bad via injection into bad P₂ indices
  have hJ_bad_bound : J_bad.card ≤ m := by
    have himg_sub : J_bad.image ι ⊆ Finset.univ \ good := by
      intro i hi; obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have himg_card : (J_bad.image ι).card = J_bad.card :=
      Finset.card_image_of_injOn (hι_inj.mono (fun j hj =>
        (Finset.mem_filter.mp hj).1))
    calc J_bad.card = (J_bad.image ι).card := himg_card.symm
      _ ≤ (Finset.univ \ good).card := Finset.card_le_card himg_sub
      _ ≤ m := hbad
  -- Conclude
  show hi - lo ≤ Nat.floor (L / h) + m + 2
  have : hi - lo - 1 ≤ Nat.floor (L / h) + 1 + m := by rw [← hJ_card]; linarith
  omega


end StochCalc
