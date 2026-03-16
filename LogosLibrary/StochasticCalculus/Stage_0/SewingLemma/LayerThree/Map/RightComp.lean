/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map/RightComp.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.LeftComp

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc
section Right


/-- Right restriction at a known index. -/
def Partition.restrictRightAt {s t : ℝ} (P : Partition s t)
    (j : Fin (P.n + 1)) (u : ℝ) (hu : P.pts j = u) (_hut : u ≤ t) :
    Partition u t where
  n := P.n - j.val
  pts := fun i => P.pts ⟨i.val + j.val, by omega⟩
  mono := fun a b hab => P.mono (by have := j.isLt; simp; omega)
  first := by simp [hu]
  last := by convert P.last using 2; have := j.isLt; simp; omega


/-- Splitting at a known index. -/
theorem riemannSum_splitAt {Ξ : ℝ → ℝ → E} {s t : ℝ}
    (P : Partition s t) (j : Fin (P.n + 1)) (u : ℝ)
    (hsu : s ≤ u) (hu : P.pts j = u) (hut : u ≤ t) :
    riemannSum Ξ P =
      riemannSum Ξ (P.restrictLeftAt j u hu hsu) +
      riemannSum Ξ (P.restrictRightAt j u hu hut) := by
  simp only [riemannSum]
  -- Clamped F
  set F : ℕ → E := fun i =>
    Ξ (P.pts ⟨min i P.n, by omega⟩) (P.pts ⟨min (i + 1) P.n, by omega⟩)
  have hF_val : ∀ i (hi : i < P.n), F i =
      Ξ (P.pts ⟨i, by omega⟩) (P.pts ⟨i + 1, by omega⟩) := by
    intro i hi; simp [F]; grind only [= min_def]
  have hP_eq : ∑ i : Fin P.n, Ξ (P.left i) (P.right i) =
      ∑ i ∈ Finset.range P.n, F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [Partition.left, Partition.right]; exact (hF_val i hi).symm
  have hL_eq : ∑ i : Fin (P.restrictLeftAt j u hu hsu).n,
      Ξ ((P.restrictLeftAt j u hu hsu).left i)
        ((P.restrictLeftAt j u hu hsu).right i) =
      ∑ i ∈ Finset.range j.val, F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [Partition.left, Partition.right, Partition.restrictLeftAt]
      grind only [usr Fin.isLt]
  have hR_eq : ∑ i : Fin (P.restrictRightAt j u hu hut).n,
      Ξ ((P.restrictRightAt j u hu hut).left i)
        ((P.restrictRightAt j u hu hut).right i) =
      ∑ i ∈ Finset.range (P.n - j.val), F (j.val + i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun ⟨i, hi⟩ _ => by
      simp only [Partition.left, Partition.right, Partition.restrictRightAt]
      grind only [= min_def]
  rw [hP_eq, hL_eq, hR_eq]
  have := Finset.sum_range_add F j.val (P.n - j.val)
  rwa [show j.val + (P.n - j.val) = P.n from by omega] at this



  /-- Structural lemma for restrictRightAt of insertAt. -/
lemma insertAt_restrictRightAt_sep_bad
    {s t : ℝ} (hst : s ≤ t) (_hst_strict : s < t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let hl := D.findBlock_left_le u hsu hut hDn
    let hr := D.findBlock_right_ge u hsu hut hDn
    let Q := D.insertAt k u hl hr
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u hl hr
    let QR := Q.restrictRightAt idx u hu_spec hut
    let good := Finset.univ.filter (fun i : Fin (QR.n + 1) => 0 < i.val)
    (∀ i ∈ good, ∀ j ∈ good, QR.pts i < QR.pts j →
      (t - s) / 2 ^ n ≤ QR.pts j - QR.pts i) ∧
    (Finset.univ \ good).card ≤ 1 := by
  intro D hDn k hl hr Q idx hu_spec QR good
  -- QR.pts(i) = Q.pts(i + k.val + 1)
  have hQR_n : QR.n = D.n - k.val := by
    simp only [QR, Partition.restrictRightAt, Q, Partition.insertAt, idx, insertAt_u_index]
    exact Nat.add_sub_add_right D.n 1 ↑k
  have hQ_n : Q.n = D.n + 1 := rfl
  have hQR_pts : ∀ (i : ℕ) (hi : i < QR.n + 1),
      QR.pts ⟨i, hi⟩ = Q.pts ⟨i + k.val + 1, by omega⟩ := by
    intro i hi; rfl
  -- For i > 0: i + k + 1 > k + 1, so insertAt_pts_gt applies
  have hQR_is_D : ∀ (i : ℕ) (hi : i < QR.n + 1) (hi_pos : 0 < i),
      QR.pts ⟨i, hi⟩ = D.pts ⟨i + k.val, by
        have := k.isLt; show i + k.val < D.n + 1; omega⟩ := by
    intro i hi hi_pos
    rw [hQR_pts i hi,
        insertAt_pts_gt D k u hl hr (by omega) (by simp; omega)]
    congr 1
  refine ⟨?_, ?_⟩
  · -- Separation: good QR-points are D-points
    intro i hi j hj hlt
    have hi_pos := (Finset.mem_filter.mp hi).2
    have hj_pos := (Finset.mem_filter.mp hj).2
    have hdi := hQR_is_D i.val i.isLt hi_pos
    have hdj := hQR_is_D j.val j.isLt hj_pos
    rw [hdi, hdj] at hlt ⊢
    have hD_eq : D.n = (dyadicPartition s t hst n).n := rfl
    have hk_lt_D : k.val < D.n := k.isLt
    exact dyadicPartition_min_spacing hst n
      ⟨i.val + k.val, by omega⟩
      ⟨j.val + k.val, by omega⟩ hlt
  · -- Bad count ≤ 1
    have : Finset.univ \ good ⊆ ({⟨0, by omega⟩} : Finset (Fin (QR.n + 1))) := by
      intro i hi
      simp only [good, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hi
      exact Finset.mem_singleton.mpr (Fin.ext hi)
    calc (Finset.univ \ good).card
        ≤ ({⟨0, by omega⟩} : Finset (Fin (QR.n + 1))).card :=
          Finset.card_le_card this
      _ = 1 := Finset.card_singleton _


theorem Partition.mesh_restrictRightAt_le {s t : ℝ} (P : Partition s t)
    (j : Fin (P.n + 1)) (u : ℝ) (hu : P.pts j = u) (hut : u ≤ t) :
    (P.restrictRightAt j u hu hut).mesh ≤ P.mesh := by
  set PR := P.restrictRightAt j u hu hut
  have hPR_n : PR.n = P.n - j.val := rfl
  have hi_bound : ∀ i : Fin PR.n, i.val + j.val < P.n := by
    intro i; have := i.isLt; have := j.isLt; omega
  have hinterval : ∀ i : Fin PR.n,
      PR.right i - PR.left i =
        P.right ⟨i.val + j.val, hi_bound i⟩ - P.left ⟨i.val + j.val, hi_bound i⟩ := by
    intro i
    simp only [Partition.right, Partition.left, PR, Partition.restrictRightAt]
    show P.pts ⟨i.val + 1 + j.val, _⟩ - P.pts ⟨i.val + j.val, _⟩ =
         P.pts ⟨i.val + j.val + 1, _⟩ - P.pts ⟨i.val + j.val, _⟩
    congr 2; ext; simp only; omega
  by_cases hPRn : PR.n = 0
  · simp only [Partition.mesh, dif_pos hPRn]
    split_ifs with hPn
    · exact le_refl 0
    · exact le_trans (sub_nonneg.mpr (P.left_le_right ⟨0, Nat.pos_of_ne_zero hPn⟩))
        (Finset.le_sup' (fun i : Fin P.n => P.right i - P.left i)
          (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero hPn⟩ : Fin P.n)))
  · have hPn : P.n ≠ 0 := by have := hi_bound ⟨0, Nat.pos_of_ne_zero hPRn⟩; omega
    simp only [Partition.mesh, dif_neg hPRn, dif_neg hPn]
    apply Finset.sup'_le; intro i _
    rw [hinterval i]
    exact Finset.le_sup' (fun i : Fin P.n => P.right i - P.left i)
      (Finset.mem_univ (⟨i.val + j.val, hi_bound i⟩ : Fin P.n))

theorem insertAt_restrictRightAt_mesh_le {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u _ _
    (Q.restrictRightAt idx u hu_spec hut).mesh ≤ (t - s) / 2 ^ n := by
  intro D hDn k Q idx hu_spec
  calc (Q.restrictRightAt idx u hu_spec hut).mesh
      ≤ Q.mesh := Partition.mesh_restrictRightAt_le Q idx u hu_spec hut
    _ ≤ D.mesh := insertAt_mesh_le D k u _ _
    _ = (t - s) / 2 ^ n := dyadicPartition_mesh s t hst n

theorem insertAt_restrictRightAt_n_pos {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) (_hut_strict : u < t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u _ _
    0 < (Q.restrictRightAt idx u hu_spec hut).n := by
  intro D hDn k Q idx hu_spec
  show 0 < Q.n - idx.val
  have hQ_n : Q.n = D.n + 1 := rfl
  have hidx_val : idx.val = k.val + 1 := rfl
  have := k.isLt
  omega

/-- Per-n comparison bound for right restriction vs dyadic of [u,t]. -/
lemma right_comparison_bound
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hut_strict : u < t) (n : ℕ) :
    let hst := hsu.trans hut
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let hl := D.findBlock_left_le u hsu hut hDn
    let hr := D.findBlock_right_ge u hsu hut hDn
    let Q := D.insertAt k u hl hr
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u hl hr
    let QR := Q.restrictRightAt idx u hu_spec hut
    let DR := dyadicPartition u t hut n
    ‖riemannSum Ξ QR - riemannSum Ξ DR‖ ≤
      ↑(Nat.floor ((t - s) / (t - u)) + 2 - 1) *
        (K * thetaEnergy ω θ QR) +
      ↑(Nat.floor ((t - u) / (t - s)) + 1 + 2 - 1) *
        (K * thetaEnergy ω θ DR) := by
  intro hst D hDn k hl hr Q idx hu_spec QR DR
  have htu_pos : 0 < t - u := sub_pos.mpr hut_strict
  have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_lt hsu hut_strict)
  have hQRn := insertAt_restrictRightAt_n_pos hst n hsu hut hut_strict
  have hDRn : 0 < DR.n := by show 0 < 2 ^ n; positivity
  -- Common refinement
  set C := QR.merge DR
  -- Direction 1: C refines QR, P₂ = DR (uniform spacing)
  obtain ⟨φ₁, hφ₁_val, hφ₁_mono, hφ₁_start, hφ₁_end⟩ :=
    (Partition.merge_refines_left QR DR).mono_embed hQRn
  have hQR_sub_le_mesh : ∀ i : Fin QR.n, QR.right i - QR.left i ≤ QR.mesh :=
    fun i => Partition.sub_le_mesh QR i
  have hQR_mesh_le : QR.mesh ≤ (t - s) / 2 ^ n :=
    insertAt_restrictRightAt_mesh_le hst n hsu hut
  have hM₁ : ∀ i : Fin QR.n,
      (φ₁ ⟨i.val + 1, by omega⟩).val - (φ₁ ⟨i.val, by omega⟩).val ≤
        Nat.floor ((t - s) / (t - u)) + 2 := by
    intro i
    have := merge_gap_of_min_spacing_mono QR DR hQRn φ₁ hφ₁_val hφ₁_mono
      hφ₁_start hφ₁_end
      (h := (t - u) / 2 ^ n) (L := (t - s) / 2 ^ n)
      (div_pos htu_pos (by positivity))
      (div_nonneg hts_pos.le (by positivity : (0:ℝ) ≤ 2 ^ n))
      (fun i j hij => dyadicPartition_min_spacing hut n i j hij)
      (fun i => (hQR_sub_le_mesh i).trans hQR_mesh_le)
      i
    rwa [show (t - s) / 2 ^ n / ((t - u) / 2 ^ n) = (t - s) / (t - u) from by
      field_simp] at this
  -- Direction 2: C refines DR, P₂ = QR (good + 1 bad)
  obtain ⟨φ₂, hφ₂_val, hφ₂_mono, hφ₂_start, hφ₂_end⟩ :=
    (Partition.merge_refines_right QR DR).mono_embed hDRn
  have hst_strict : s < t := lt_of_le_of_lt hsu hut_strict
  obtain ⟨hgood_sep, hbad_card⟩ :=
    insertAt_restrictRightAt_sep_bad hst hst_strict n hsu hut
  set good := Finset.univ.filter (fun i : Fin (QR.n + 1) => 0 < i.val)
  have hDR_sub_le : ∀ i : Fin DR.n, DR.right i - DR.left i ≤ (t - u) / 2 ^ n := by
    intro i
    calc DR.right i - DR.left i ≤ DR.mesh := Partition.sub_le_mesh DR i
      _ = (t - u) / 2 ^ n := dyadicPartition_mesh u t hut n
  have hM₂ : ∀ i : Fin DR.n,
      (φ₂ ⟨i.val + 1, by omega⟩).val - (φ₂ ⟨i.val, by omega⟩).val ≤
        Nat.floor ((t - u) / (t - s)) + 1 + 2 := by
    intro i
    have := refinement_gap_with_exceptions_mono hDRn
      (fun hij => Partition.merge_pts_strict_mono QR DR hij)
      (fun j => Or.comm.mp (Partition.merge_pts_mem_union QR DR j))
      φ₂ hφ₂_val hφ₂_mono hφ₂_start hφ₂_end
      (h := (t - s) / 2 ^ n) (L := (t - u) / 2 ^ n)
      (div_pos hts_pos (by positivity))
      (div_nonneg htu_pos.le (by positivity : (0:ℝ) ≤ 2 ^ n))
      good hgood_sep hbad_card
      hDR_sub_le
      i
    rwa [show (t - u) / 2 ^ n / ((t - s) / 2 ^ n) = (t - u) / (t - s) from by
      field_simp] at this
  -- Triangle
  calc ‖riemannSum Ξ QR - riemannSum Ξ DR‖
      ≤ ‖riemannSum Ξ QR - riemannSum Ξ C‖ +
        ‖riemannSum Ξ C - riemannSum Ξ DR‖ := by
        rw [show riemannSum Ξ QR - riemannSum Ξ DR =
          (riemannSum Ξ QR - riemannSum Ξ C) +
          (riemannSum Ξ C - riemannSum Ξ DR) from by abel]
        exact norm_add_le _ _
    _ ≤ ↑(Nat.floor ((t - s) / (t - u)) + 2 - 1) *
          (K * thetaEnergy ω θ QR) +
        ↑(Nat.floor ((t - u) / (t - s)) + 1 + 2 - 1) *
          (K * thetaEnergy ω θ DR) := by
        apply add_le_add
        · exact riemannSum_refinement_bound₃ hΞ (has.trans hsu) hut htb hQRn
            φ₁ hφ₁_val hφ₁_mono hφ₁_start hφ₁_end hM₁
        · rw [norm_sub_rev]
          exact riemannSum_refinement_bound₃ hΞ (has.trans hsu) hut htb hDRn
            φ₂ hφ₂_val hφ₂_mono hφ₂_start hφ₂_end hM₂

/-! ### Symmetric: right comparison -/

theorem right_comparison_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hut_strict : u < t) :
    Tendsto (fun n =>
      let hst := hsu.trans hut
      let D := dyadicPartition s t hst n
      let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
      let k := D.findBlock u hsu hut hDn
      let hl := D.findBlock_left_le u hsu hut hDn
      let hr := D.findBlock_right_ge u hsu hut hDn
      let Q := D.insertAt k u hl hr
      let idx := insertAt_u_index D k
      let hu_spec := insertAt_u_index_spec D k u hl hr
      riemannSum Ξ (Q.restrictRightAt idx u hu_spec hut) -
        dyadicSum₁ Ξ u t n) atTop (nhds 0) := by
  have hst := hsu.trans hut
  have hau := has.trans hsu
  have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_lt hsu hut_strict)
  have htu_pos : 0 < t - u := sub_pos.mpr hut_strict
  set C₁ := (Nat.floor ((t - s) / (t - u)) + 2 - 1 : ℕ)
  set C₂ := (Nat.floor ((t - u) / (t - s)) + 1 + 2 - 1 : ℕ)
  set C := (↑C₁ + ↑C₂) * K + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ (↑C₁ + ↑C₂) * K := mul_nonneg (by positivity) hΞ.K_nonneg
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    thetaEnergy_tendsto_zero hΞ.omega_cont hΞ.one_lt_theta hau htb hut
      (ε / C) (div_pos hε hC_pos)
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → (t - s) / 2 ^ n < δ := by
    by_cases hts_eq : t = s
    · exact ⟨0, fun n _ => by rw [show t - s = 0 from by linarith, zero_div]; exact hδ_pos⟩
    · obtain ⟨N, hN'⟩ := exists_pow_lt_of_lt_one (div_pos hδ_pos hts_pos)
        (by norm_num : (2:ℝ)⁻¹ < 1)
      exact ⟨N, fun n hn => by
        calc (t - s) / 2 ^ n = (t - s) * (2⁻¹ ^ n) := by rw [div_eq_mul_inv, inv_pow]
          _ ≤ (t - s) * (2⁻¹ ^ N) := by
              apply mul_le_mul_of_nonneg_left _ hts_pos.le
              exact pow_le_pow_of_le_one (by positivity) (by norm_num) hn
          _ < (t - s) * (δ / (t - s)) := by gcongr
          _ = δ := by field_simp⟩
  use N; intro n hn
  rw [dist_eq_norm, sub_zero]
  have hQR_mesh_lt :
      (fun n =>
        let D := dyadicPartition s t hst n
        let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
        let k := D.findBlock u hsu hut hDn
        let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
          (D.findBlock_right_ge u hsu hut hDn)
        (Q.restrictRightAt (insertAt_u_index D k) u
          (insertAt_u_index_spec D k u _ _) hut).mesh) n < δ :=
    lt_of_le_of_lt (insertAt_restrictRightAt_mesh_le hst n hsu hut) (hN n hn)
  have hDR_mesh_lt : (dyadicPartition u t hut n).mesh < δ := by
    rw [dyadicPartition_mesh]
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_right (by linarith : t - u ≤ t - s) (by positivity))
      (hN n hn)
  rw [← dyadicPartition_riemannSum Ξ u t hut n]
  have hbound := right_comparison_bound hΞ has hsu hut htb hut_strict n
  calc ‖riemannSum Ξ _ - riemannSum Ξ _‖
      ≤ ↑C₁ * (K * thetaEnergy ω θ _) + ↑C₂ * (K * thetaEnergy ω θ _) := hbound
    _ ≤ ↑C₁ * (K * (ε / C)) + ↑C₂ * (K * (ε / C)) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hδ _ hQR_mesh_lt).le hΞ.K_nonneg
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hδ _ hDR_mesh_lt).le hΞ.K_nonneg
    _ = (↑C₁ + ↑C₂) * K * (ε / C) := by ring
    _ < ((↑C₁ + ↑C₂) * K + 1) * (ε / C) := by
        apply mul_lt_mul_of_pos_right _ (div_pos hε hC_pos)
        linarith
    _ = ε := by field_simp [show C ≠ 0 from ne_of_gt hC_pos]; exact (add_left_inj 1).mpr rfl

end Right
end StochCalc
