/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/Map/LeftComp.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.RefiCo
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Insert
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.MinSpacing
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.MultiBlock
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map.Wrappers


noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

section Left

/-- Each sub-interval length is ≤ the mesh. -/
theorem Partition.sub_le_mesh {s t : ℝ} (P : Partition s t) (i : Fin P.n) :
    P.right i - P.left i ≤ P.mesh := by
  have hPn : P.n ≠ 0 := by rw [@Nat.ne_zero_iff_zero_lt]; exact Fin.pos i
  simp only [Partition.mesh, dif_neg hPn]
  exact Finset.le_sup' (α := ℝ) (fun j : Fin P.n => P.right j - P.left j)
    (Finset.mem_univ i)

/-- Left restriction at a known index. -/
def Partition.restrictLeftAt {s t : ℝ} (P : Partition s t)
    (j : Fin (P.n + 1)) (u : ℝ) (hu : P.pts j = u) (_hsu : s ≤ u) :
    Partition s u where
  n := j.val
  pts := fun i => P.pts ⟨i.val, by have := j.isLt; have := i.isLt; omega⟩
  mono := fun a b hab => P.mono (by omega)
  first := P.first
  last := hu

theorem Partition.mesh_restrictLeftAt_le {s t : ℝ} (P : Partition s t)
    (j : Fin (P.n + 1)) (u : ℝ) (hu : P.pts j = u) (hsu : s ≤ u) :
    (P.restrictLeftAt j u hu hsu).mesh ≤ P.mesh := by
  set PL := P.restrictLeftAt j u hu hsu
  have hPL_n : PL.n = j.val := rfl
  have hi_bound : ∀ i : Fin PL.n, i.val < P.n := by
    intro i
    have h1 : i.val < PL.n := i.isLt
    have h2 : PL.n = j.val := hPL_n
    have h3 : j.val < P.n + 1 := j.isLt
    omega
  have hinterval : ∀ i : Fin PL.n,
      PL.right i - PL.left i =
        P.right ⟨i.val, hi_bound i⟩ - P.left ⟨i.val, hi_bound i⟩ := by
    intro i; simp only [Partition.right, Partition.left, PL, Partition.restrictLeftAt]
  by_cases hPLn : PL.n = 0
  · simp only [Partition.mesh, dif_pos hPLn]
    split_ifs with hPn
    · exact le_refl 0
    · exact le_trans (sub_nonneg.mpr (P.left_le_right ⟨0, Nat.pos_of_ne_zero hPn⟩))
        (Finset.le_sup' (fun i : Fin P.n => P.right i - P.left i)
          (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero hPn⟩ : Fin P.n)))
  · have hPn : P.n ≠ 0 := by have := hi_bound ⟨0, Nat.pos_of_ne_zero hPLn⟩; omega
    simp only [Partition.mesh, dif_neg hPLn, dif_neg hPn]
    apply Finset.sup'_le; intro i _
    rw [hinterval i]
    exact Finset.le_sup' (fun j : Fin P.n => P.right j - P.left j)
      (Finset.mem_univ (⟨i.val, hi_bound i⟩ : Fin P.n))

theorem insertAt_restrictLeftAt_mesh_le {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u _ _
    (Q.restrictLeftAt idx u hu_spec hsu).mesh ≤ (t - s) / 2 ^ n := by
  intro D hDn k Q idx hu_spec
  calc (Q.restrictLeftAt idx u hu_spec hsu).mesh
      ≤ Q.mesh := Partition.mesh_restrictLeftAt_le Q idx u hu_spec hsu
    _ ≤ D.mesh := insertAt_mesh_le D k u _ _
    _ = (t - s) / 2 ^ n := dyadicPartition_mesh s t hst n

theorem insertAt_restrictLeftAt_n_pos {s t : ℝ} (hst : s ≤ t) (n : ℕ)
    {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) (_hsu_strict : s < u) :
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
        (D.findBlock_right_ge u hsu hut hDn)
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u _ _
    0 < (Q.restrictLeftAt idx u hu_spec hsu).n := by
  intro D hDn k Q idx hu_spec
  have hidx : idx.val = k.val + 1 := rfl
  exact Nat.zero_lt_succ ↑k

/-- Structural lemma for restrictLeftAt of insertAt. -/
lemma insertAt_restrictLeftAt_sep_bad
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
    let QL := Q.restrictLeftAt idx u hu_spec hsu
    let good := Finset.univ.filter (fun i : Fin (QL.n + 1) => i.val ≠ k.val + 1)
    (∀ i ∈ good, ∀ j ∈ good, QL.pts i < QL.pts j →
      (t - s) / 2 ^ n ≤ QL.pts j - QL.pts i) ∧
    (Finset.univ \ good).card ≤ 1 := by
  intro D hDn k hl hr Q idx hu_spec QL good
  -- QL.n = idx.val = k.val + 1
  have hQL_n : QL.n = k.val + 1 := rfl
  -- QL.pts(i) = Q.pts(i) for i ≤ k+1
  have hQ_n : Q.n = D.n + 1 := rfl
  have hQL_n : QL.n = k.val + 1 := rfl
  have hQL_pts : ∀ (i : ℕ) (hi : i < QL.n + 1),
      QL.pts ⟨i, hi⟩ = Q.pts ⟨i, by
        have := k.isLt; rw [hQL_n] at hi; rw [hQ_n]; omega⟩ := by
    intro i hi; rfl
  -- Good QL points are D-points
  have hgood_is_D : ∀ i : Fin (QL.n + 1), i.val ≠ k.val + 1 →
      ∃ di : Fin (D.n + 1), QL.pts i = D.pts di := by
    intro i hi_ne
    rw [hQL_pts i.val i.isLt]
    rcases Nat.lt_or_ge i.val (k.val + 1) with h | h
    · have : i.val ≤ k.val := by omega
      rw [insertAt_pts_le D k u hl hr this (by omega)]
      exact ⟨⟨i.val, by have := k.isLt; omega⟩, rfl⟩
    · -- i.val ≥ k.val + 1 and ≠ k.val + 1 means i.val ≥ k.val + 2
      have : k.val + 1 < i.val := by omega
      rw [insertAt_pts_gt D k u hl hr this (by omega)]
      exact ⟨⟨i.val - 1, by omega⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · intro i hi j hj hlt
    have hi_ne := (Finset.mem_filter.mp hi).2
    have hj_ne := (Finset.mem_filter.mp hj).2
    obtain ⟨di, hdi⟩ := hgood_is_D i hi_ne
    obtain ⟨dj, hdj⟩ := hgood_is_D j hj_ne
    rw [hdi, hdj] at hlt ⊢
    exact dyadicPartition_min_spacing hst n di dj hlt
  · calc (Finset.univ \ good).card
        ≤ (Finset.univ.filter
            (fun i : Fin (QL.n + 1) => i.val = k.val + 1)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [good, Finset.mem_sdiff, Finset.mem_filter,
                      Finset.mem_univ, true_and, not_not] at hi ⊢
          exact hi
      _ ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)

/-- Per-n comparison bound for left restriction vs dyadic of [s,u]. -/
lemma left_comparison_bound
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hsu_strict : s < u) (n : ℕ) :
    let hst := hsu.trans hut
    let _hub := hut.trans htb
    let D := dyadicPartition s t hst n
    let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
    let k := D.findBlock u hsu hut hDn
    let hl := D.findBlock_left_le u hsu hut hDn
    let hr := D.findBlock_right_ge u hsu hut hDn
    let Q := D.insertAt k u hl hr
    let idx := insertAt_u_index D k
    let hu_spec := insertAt_u_index_spec D k u hl hr
    let QL := Q.restrictLeftAt idx u hu_spec hsu
    let DL := dyadicPartition s u hsu n
    ‖riemannSum Ξ QL - riemannSum Ξ DL‖ ≤
      ↑(Nat.floor ((t - s) / (u - s)) + 2 - 1) *
        (K * thetaEnergy ω θ QL) +
      ↑(Nat.floor ((u - s) / (t - s)) + 1 + 2 - 1) *
        (K * thetaEnergy ω θ DL) := by
  intro hst hub D hDn k hl hr Q idx hu_spec QL DL
  have hsu_pos : 0 < u - s := sub_pos.mpr hsu_strict
  have hts_pos : 0 < t - s := sub_pos.mpr (hsu_strict.trans_le hut)
  have hQLn := insertAt_restrictLeftAt_n_pos hst n hsu hut hsu_strict
  have hDLn : 0 < DL.n := by show 0 < 2 ^ n; positivity
  set C := QL.merge DL
  -- Direction 1: C refines QL, P₂ = DL (uniform spacing)
  obtain ⟨φ₁, hφ₁_val, hφ₁_mono, hφ₁_start, hφ₁_end⟩ :=
    (Partition.merge_refines_left QL DL).mono_embed hQLn
  have hQL_mesh_le : QL.mesh ≤ (t - s) / 2 ^ n :=
    insertAt_restrictLeftAt_mesh_le hst n hsu hut
  have hM₁ : ∀ i : Fin QL.n,
      (φ₁ ⟨i.val + 1, by omega⟩).val - (φ₁ ⟨i.val, by omega⟩).val ≤
        Nat.floor ((t - s) / (u - s)) + 2 := by
    intro i
    have := merge_gap_of_min_spacing_mono QL DL hQLn φ₁ hφ₁_val hφ₁_mono
      hφ₁_start hφ₁_end
      (h := (u - s) / 2 ^ n) (L := (t - s) / 2 ^ n)
      (div_pos hsu_pos (by positivity))
      (div_nonneg hts_pos.le (by positivity : (0:ℝ) ≤ 2 ^ n))
      (fun i j hij => dyadicPartition_min_spacing hsu n i j hij)
      (fun i => (Partition.sub_le_mesh QL i).trans hQL_mesh_le)
      i
    rwa [show (t - s) / 2 ^ n / ((u - s) / 2 ^ n) = (t - s) / (u - s) from by
      field_simp] at this
  -- Direction 2: C refines DL, P₂ = QL (good + 1 bad)
  obtain ⟨φ₂, hφ₂_val, hφ₂_mono, hφ₂_start, hφ₂_end⟩ :=
    (Partition.merge_refines_right QL DL).mono_embed hDLn
  obtain ⟨hgood_sep, hbad_card⟩ :=
    insertAt_restrictLeftAt_sep_bad hst (hsu_strict.trans_le hut) n hsu hut
  set good := Finset.univ.filter (fun i : Fin (QL.n + 1) => i.val ≠ k.val + 1)
  have hDL_sub_le : ∀ i : Fin DL.n, DL.right i - DL.left i ≤ (u - s) / 2 ^ n := by
    intro i
    calc DL.right i - DL.left i ≤ DL.mesh := Partition.sub_le_mesh DL i
      _ = (u - s) / 2 ^ n := dyadicPartition_mesh s u hsu n
  have hM₂ : ∀ i : Fin DL.n,
      (φ₂ ⟨i.val + 1, by omega⟩).val - (φ₂ ⟨i.val, by omega⟩).val ≤
        Nat.floor ((u - s) / (t - s)) + 1 + 2 := by
    intro i
    have := refinement_gap_with_exceptions_mono hDLn
      (fun hij => Partition.merge_pts_strict_mono QL DL hij)
      (fun j => Or.comm.mp (Partition.merge_pts_mem_union QL DL j))
      φ₂ hφ₂_val hφ₂_mono hφ₂_start hφ₂_end
      (h := (t - s) / 2 ^ n) (L := (u - s) / 2 ^ n)
      (div_pos hts_pos (by positivity))
      (div_nonneg hsu_pos.le (by positivity : (0:ℝ) ≤ 2 ^ n))
      good hgood_sep hbad_card
      hDL_sub_le
      i
    rwa [show (u - s) / 2 ^ n / ((t - s) / 2 ^ n) = (u - s) / (t - s) from by
      field_simp] at this
  -- Triangle
  calc ‖riemannSum Ξ QL - riemannSum Ξ DL‖
      ≤ ‖riemannSum Ξ QL - riemannSum Ξ C‖ +
        ‖riemannSum Ξ C - riemannSum Ξ DL‖ := by
        rw [show riemannSum Ξ QL - riemannSum Ξ DL =
          (riemannSum Ξ QL - riemannSum Ξ C) +
          (riemannSum Ξ C - riemannSum Ξ DL) from by abel]
        exact norm_add_le _ _
    _ ≤ ↑(Nat.floor ((t - s) / (u - s)) + 2 - 1) *
          (K * thetaEnergy ω θ QL) +
        ↑(Nat.floor ((u - s) / (t - s)) + 1 + 2 - 1) *
          (K * thetaEnergy ω θ DL) := by
        apply add_le_add
        · exact riemannSum_refinement_bound₃ hΞ has hsu hub hQLn
            φ₁ hφ₁_val hφ₁_mono hφ₁_start hφ₁_end hM₁
        · rw [norm_sub_rev]
          exact riemannSum_refinement_bound₃ hΞ has hsu hub hDLn
            φ₂ hφ₂_val hφ₂_mono hφ₂_start hφ₂_end hM₂

theorem left_comparison_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hsu_strict : s < u) :
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
      riemannSum Ξ (Q.restrictLeftAt idx u hu_spec hsu) -
        dyadicSum₁ Ξ s u n) atTop (nhds 0) := by
  have hst := hsu.trans hut
  have hub := hut.trans htb
  have hts_pos : 0 < t - s := sub_pos.mpr (hsu_strict.trans_le hut)
  set C₁ := (Nat.floor ((t - s) / (u - s)) + 2 - 1 : ℕ)
  set C₂ := (Nat.floor ((u - s) / (t - s)) + 1 + 2 - 1 : ℕ)
  set C := (↑C₁ + ↑C₂) * K + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ (↑C₁ + ↑C₂) * K := mul_nonneg (by positivity) hΞ.K_nonneg
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    thetaEnergy_tendsto_zero hΞ.omega_cont hΞ.one_lt_theta has hub hsu
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
  have hQL_mesh_lt :
      (fun n =>
        let D := dyadicPartition s t hst n
        let hDn : 0 < D.n := by show 0 < 2 ^ n; positivity
        let k := D.findBlock u hsu hut hDn
        let Q := D.insertAt k u (D.findBlock_left_le u hsu hut hDn)
          (D.findBlock_right_ge u hsu hut hDn)
        (Q.restrictLeftAt (insertAt_u_index D k) u
          (insertAt_u_index_spec D k u _ _) hsu).mesh) n < δ :=
    lt_of_le_of_lt (insertAt_restrictLeftAt_mesh_le hst n hsu hut) (hN n hn)
  have hDL_mesh_lt : (dyadicPartition s u hsu n).mesh < δ := by
    rw [dyadicPartition_mesh]
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_right (by linarith : u - s ≤ t - s) (by positivity))
      (hN n hn)
  rw [← dyadicPartition_riemannSum Ξ s u hsu n]
  have hbound := left_comparison_bound hΞ has hsu hut htb hsu_strict n
  calc ‖riemannSum Ξ _ - riemannSum Ξ _‖
      ≤ ↑C₁ * (K * thetaEnergy ω θ _) + ↑C₂ * (K * thetaEnergy ω θ _) := hbound
    _ ≤ ↑C₁ * (K * (ε / C)) + ↑C₂ * (K * (ε / C)) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hδ _ hQL_mesh_lt).le hΞ.K_nonneg
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hδ _ hDL_mesh_lt).le hΞ.K_nonneg
    _ = (↑C₁ + ↑C₂) * K * (ε / C) := by ring
    _ < ((↑C₁ + ↑C₂) * K + 1) * (ε / C) := by
        apply mul_lt_mul_of_pos_right _ (div_pos hε hC_pos)
        linarith
    _ = ε := by field_simp [show C ≠ 0 from ne_of_gt hC_pos]; exact (add_left_inj 1).mpr rfl

end StochCalc.Left
