/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: LayerTwo/Map/Additive.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.RightPe
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.RefiCo
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map.Partition

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Additivity (Layer 2) -/

section Additive₂

/-- The dyadic sums converge to the sewing map (Layer 2). -/
theorem sewingMap₂_tendsto [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b) {s t : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Tendsto (fun n => dyadicSum₁ Ξ s t n) atTop
      (nhds (sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t)) := by
  have : sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t =
      limUnder atTop (fun n => dyadicSum₁ Ξ s t n) := by
    simp only [sewingMap₂]
    grind only
  rw [this]
  exact (dyadicSum₂_cauchy hΞ has hst htb).tendsto_limUnder


/-- **Additivity (Layer 2)**: `I(s,t) = I(s,u) + I(u,t)` for all `u ∈ [s,t]`.

Proof outline:
1. Let `Mₙ = Dₙ.merge({s,u,t})`. Then `Mₙ` contains `u` and refines `Dₙ`.
2. `‖RS(Dₙ) - RS(Mₙ)‖ ≤ K · CE(Dₙ) → 0` by refinement cost + CE vanishing.
3. So `RS(Mₙ) → I(s,t)`.
4. `RS(Mₙ) = RS(Mₙ|_[s,u]) + RS(Mₙ|_[u,t])` by splitting at `u`.
5. `Mₙ|_[s,u]` is a partition of `[s,u]` with mesh → 0, so `RS → I(s,u)`.
6. Similarly `RS(Mₙ|_[u,t]) → I(u,t)`.
7. By uniqueness of limits: `I(s,t) = I(s,u) + I(u,t)`. -/
theorem sewingMap₂_additive [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t =
      sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s u +
      sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ u t := by
  set I := sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ
  have hst : s ≤ t := hsu.trans hut
  -- Merged partitions: D_n(s,t) ∪ {s,u,t}
  set T := Partition.twoPoint s u t hsu hut
  set M := fun n => (dyadicPartition s t hst n).merge T
  have hM_u : ∀ n, ∃ i : Fin ((M n).n + 1), (M n).pts i = u :=
    fun n => merge_contains_u hst hsu hut n
  -- Splitting at u
  have hRS_split : ∀ n, riemannSum Ξ (M n) =
      riemannSum Ξ ((M n).restrictLeft u hsu (hM_u n)) +
      riemannSum Ξ ((M n).restrictRight u hut (hM_u n)) :=
    fun n => riemannSum_split (M n) u hsu hut (hM_u n)
  -- Constants
  set C := K * L₁ ^ α * L₂ ^ β
  set r := sewingRatio₂ α β
  have hC_nn : 0 ≤ C := mul_nonneg
    (mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _))
    (rpow_nonneg hΞ.L₂_nonneg _)
  have hr₀ : 0 ≤ r := le_of_lt (sewingRatio₂_pos hΞ.one_lt_exp)
  have hr₁ : r < 1 := sewingRatio₂_lt_one hΞ.one_lt_exp
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  -- M_n refines D_n
  have hM_ref : ∀ n, (M n).IsRefinement (dyadicPartition s t hst n) :=
    fun n => Partition.merge_refines_left _ T
  -- Point count: (M n).n ≤ 4 * 2^n
  have hM_n_le : ∀ n, (M n).n ≤ 4 * 2 ^ n := by
    intro n
    have h := Partition.n_merge_le (dyadicPartition s t hst n) T
    have h1 : (dyadicPartition s t hst n).n = 2 ^ n := rfl
    have h2 : T.n = 2 := rfl
    have h3 : (M n).n = ((dyadicPartition s t hst n).merge T).n := rfl
    rw [h1, h2] at h
    rw [h3]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  -- Uniform bound: refinement error ≤ B * r^n
  set B := 4 * C * (t - s) ^ (α + β)
  have hB_nn : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) hC_nn) (rpow_nonneg hts _)
  have hrefine_bound : ∀ n,
      ‖riemannSum Ξ (dyadicPartition s t hst n) - riemannSum Ξ (M n)‖ ≤
        B * r ^ n := by
    intro n
    have hd_nn : 0 ≤ (t - s) / (2 : ℝ) ^ n := div_nonneg hts (by positivity)
    calc ‖riemannSum Ξ (dyadicPartition s t hst n) - riemannSum Ξ (M n)‖
        ≤ ↑(M n).n * (C * (dyadicPartition s t hst n).mesh ^ (α + β)) :=
          riemannSum_refinement_bound₂ hΞ has hst htb _ _ (hM_ref n)
      _ = ↑(M n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
          rw [dyadicPartition_mesh]
      _ ≤ ↑(4 * 2 ^ n) * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC_nn (rpow_nonneg hd_nn _))
          exact_mod_cast hM_n_le n
      _ = 4 * (C * ((2 : ℝ) ^ n * ((t - s) / (2 : ℝ) ^ n) ^ (α + β))) := by
          ring
      _ = 4 * (C * ((t - s) ^ (α + β) * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)))) := by
          congr 2; exact dyadic_geometric_factor hts n
      _ = B * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) := by unfold B; ring
      _ = B * r ^ n := by
          congr 1
          simp only [r, sewingRatio₂]
          rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (α + β - 1)) n,
              ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
          congr 1; ring
  /-
  **Step 1**: RS(M_n) → I(s,t).
  Triangle: ‖RS(M_n) - I(s,t)‖ ≤ ‖RS(M_n) - RS(D_n)‖ + ‖RS(D_n) - I(s,t)‖
  First term ≤ B·r^n → 0. Second term → 0 by sewingMap₂_tendsto.
  -/
  have hRS_M_tendsto :
      Tendsto (fun n => riemannSum Ξ (M n)) atTop (nhds (I s t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp
      (sewingMap₂_tendsto hΞ has hst htb)) (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, B * r ^ N₂ < ε / 2 := by
      by_cases hB : B ≤ 0
      · exact ⟨0, by linarith [mul_nonpos_of_nonpos_of_nonneg hB (pow_nonneg hr₀ 0)]⟩
      · push_neg at hB
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) hB) hr₁
        exact ⟨N, by
          calc B * r ^ N = r ^ N * B := mul_comm _ _
            _ < (ε / 2 / B) * B := mul_lt_mul_of_pos_right hN hB
            _ = ε / 2 := div_mul_cancel₀ _ (ne_of_gt hB)⟩
    use max N₁ N₂
    intro n hn
    calc dist (riemannSum Ξ (M n)) (I s t)
        ≤ dist (riemannSum Ξ (M n)) (dyadicSum₁ Ξ s t n) +
          dist (dyadicSum₁ Ξ s t n) (I s t) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · rw [dist_comm, dist_eq_norm, ← dyadicPartition_riemannSum]
            calc ‖riemannSum Ξ (dyadicPartition s t hst n) - riemannSum Ξ (M n)‖
                ≤ B * r ^ n := hrefine_bound n
              _ ≤ B * r ^ N₂ := by
                  apply mul_le_mul_of_nonneg_left
                    (pow_le_pow_of_le_one hr₀ hr₁.le (le_of_max_le_right hn)) hB_nn
              _ < ε / 2 := hN₂
            exact RCLike.ofReal_le_ofReal.mp hst
          · exact hN₁ n (le_of_max_le_left hn)
      _ = ε := add_halves ε
  have hRS_L_tendsto :
      Tendsto (fun n => riemannSum Ξ
        ((M n).restrictLeft u hsu (hM_u n))) atTop (nhds (I s u)) := by
    set ML := fun n => (M n).restrictLeft u hsu (hM_u n)
    set DL := fun n => dyadicPartition s u hsu n
    set RL := fun n => (ML n).merge (DL n)
    have hub : u ≤ b := hut.trans htb
    have mesh_nonneg : ∀ {s' t' : ℝ} (Q : Partition s' t'), 0 ≤ Q.mesh := by
      intro s' t' Q; simp only [Partition.mesh]; split_ifs with h
      · exact le_refl 0
      · exact le_trans (sub_nonneg.mpr (Q.left_le_right ⟨0, Nat.pos_of_ne_zero h⟩))
          (Finset.le_sup' (fun i : Fin Q.n => Q.right i - Q.left i)
            (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero h⟩ : Fin Q.n)))
    have hαβ_nn : 0 ≤ α + β := by linarith [hΞ.α_nonneg, hΞ.β_nonneg]
    have hML_mesh : ∀ n, (ML n).mesh ≤ (t - s) / (2 : ℝ) ^ n := by
      intro n
      calc (ML n).mesh ≤ (M n).mesh :=
            Partition.mesh_restrictLeft_le _ u hsu (hM_u n)
        _ ≤ (dyadicPartition s t hst n).mesh :=
            Partition.mesh_refinement_le (hM_ref n)
        _ = (t - s) / (2 : ℝ) ^ n := dyadicPartition_mesh s t hst n
    have hDL_mesh : ∀ n, (DL n).mesh ≤ (t - s) / (2 : ℝ) ^ n := by
      intro n
      calc (DL n).mesh = (u - s) / (2 : ℝ) ^ n := dyadicPartition_mesh s u hsu n
        _ ≤ (t - s) / (2 : ℝ) ^ n := by
            apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2 ^ n).le; linarith
    have hRL_n_le : ∀ n, (RL n).n ≤ 6 * 2 ^ n := by
      intro n
      have h := Partition.n_merge_le (ML n) (DL n)
      have : (ML n).n ≤ (M n).n :=
        Nat.lt_succ_iff.mp ((M n).findPoint u (hM_u n)).isLt
      have : (DL n).n = 2 ^ n := rfl
      have : (M n).n ≤ 4 * 2 ^ n := hM_n_le n
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      lia
    set BL := 12 * C * (t - s) ^ (α + β)
    have hBL_nn : 0 ≤ BL :=
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 12) hC_nn) (rpow_nonneg hts _)
    have hcomp : ∀ n,
        ‖riemannSum Ξ (ML n) - dyadicSum₁ Ξ s u n‖ ≤ BL * r ^ n := by
      intro n
      rw [← dyadicPartition_riemannSum Ξ s u hsu n]
      have hd_nn : 0 ≤ (t - s) / (2 : ℝ) ^ n := div_nonneg hts (by positivity)
      have h_left : ‖riemannSum Ξ (ML n) - riemannSum Ξ (RL n)‖ ≤
          ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) :=
        calc ‖riemannSum Ξ (ML n) - riemannSum Ξ (RL n)‖
            ≤ ↑(RL n).n * (C * (ML n).mesh ^ (α + β)) :=
              riemannSum_refinement_bound₂ hΞ has hsu hub _ _
                (Partition.merge_refines_left _ _)
          _ ≤ ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              apply mul_le_mul_of_nonneg_left _ hC_nn
              exact rpow_le_rpow (mesh_nonneg _) (hML_mesh n) hαβ_nn
      have h_right : ‖riemannSum Ξ (RL n) - riemannSum Ξ (DL n)‖ ≤
          ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
        rw [norm_sub_rev]
        calc ‖riemannSum Ξ (DL n) - riemannSum Ξ (RL n)‖
            ≤ ↑(RL n).n * (C * (DL n).mesh ^ (α + β)) :=
              riemannSum_refinement_bound₂ hΞ has hsu hub _ _
                (Partition.merge_refines_right _ _)
          _ ≤ ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              apply mul_le_mul_of_nonneg_left _ hC_nn
              exact rpow_le_rpow (mesh_nonneg _) (hDL_mesh n) hαβ_nn
      calc ‖riemannSum Ξ (ML n) - riemannSum Ξ (DL n)‖
          ≤ ‖riemannSum Ξ (ML n) - riemannSum Ξ (RL n)‖ +
            ‖riemannSum Ξ (RL n) - riemannSum Ξ (DL n)‖ := by
              rw [show riemannSum Ξ (ML n) - riemannSum Ξ (DL n) =
                (riemannSum Ξ (ML n) - riemannSum Ξ (RL n)) +
                (riemannSum Ξ (RL n) - riemannSum Ξ (DL n)) from by abel]
              exact norm_add_le _ _
        _ ≤ ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) +
            ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) :=
            add_le_add h_left h_right
        _ = 2 * ↑(RL n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by ring
        _ ≤ 2 * ↑(6 * 2 ^ n) * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC_nn (rpow_nonneg hd_nn _))
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2)
            exact_mod_cast hRL_n_le n
        _ = 12 * (C * ((2 : ℝ) ^ n * ((t - s) / (2 : ℝ) ^ n) ^ (α + β))) := by
            ring
        _ = 12 * (C * ((t - s) ^ (α + β) * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)))) := by
            congr 2; exact dyadic_geometric_factor hts n
        _ = BL * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) := by unfold BL; ring
        _ = BL * r ^ n := by
            congr 1; simp only [r, sewingRatio₂]
            rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (α + β - 1)) n,
                ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
            congr 1; ring
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp
      (sewingMap₂_tendsto hΞ has hsu hub)) (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, BL * r ^ N₂ < ε / 2 := by
      by_cases hBL : BL ≤ 0
      · exact ⟨0, by linarith [mul_nonpos_of_nonpos_of_nonneg hBL (pow_nonneg hr₀ 0)]⟩
      · push_neg at hBL
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) hBL) hr₁
        exact ⟨N, by
          calc BL * r ^ N = r ^ N * BL := mul_comm _ _
            _ < (ε / 2 / BL) * BL := mul_lt_mul_of_pos_right hN hBL
            _ = ε / 2 := div_mul_cancel₀ _ (ne_of_gt hBL)⟩
    use max N₁ N₂
    intro n hn
    calc dist (riemannSum Ξ (ML n)) (I s u)
        ≤ dist (riemannSum Ξ (ML n)) (dyadicSum₁ Ξ s u n) +
          dist (dyadicSum₁ Ξ s u n) (I s u) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · rw [dist_eq_norm]
            calc ‖riemannSum Ξ (ML n) - dyadicSum₁ Ξ s u n‖
                ≤ BL * r ^ n := hcomp n
              _ ≤ BL * r ^ N₂ := by
                  apply mul_le_mul_of_nonneg_left
                    (pow_le_pow_of_le_one hr₀ hr₁.le (le_of_max_le_right hn)) hBL_nn
              _ < ε / 2 := hN₂
          · exact hN₁ n (le_of_max_le_left hn)
      _ = ε := add_halves ε
  /- Step 3: RS(M_n|_R) → I(u,t). Symmetric to Step 2. -/
  have hRS_R_tendsto :
      Tendsto (fun n => riemannSum Ξ
        ((M n).restrictRight u hut (hM_u n))) atTop (nhds (I u t)) := by
    set MR := fun n => (M n).restrictRight u hut (hM_u n)
    set DR := fun n => dyadicPartition u t hut n
    set RR := fun n => (MR n).merge (DR n)
    have hau : a ≤ u := has.trans hsu
    have mesh_nonneg : ∀ {s' t' : ℝ} (Q : Partition s' t'), 0 ≤ Q.mesh := by
      intro s' t' Q; simp only [Partition.mesh]; split_ifs with h
      · exact le_refl 0
      · exact le_trans (sub_nonneg.mpr (Q.left_le_right ⟨0, Nat.pos_of_ne_zero h⟩))
          (Finset.le_sup' (fun i : Fin Q.n => Q.right i - Q.left i)
            (Finset.mem_univ (⟨0, Nat.pos_of_ne_zero h⟩ : Fin Q.n)))
    have hαβ_nn : 0 ≤ α + β := by linarith [hΞ.α_nonneg, hΞ.β_nonneg]
    have hMR_mesh : ∀ n, (MR n).mesh ≤ (t - s) / (2 : ℝ) ^ n := by
      intro n
      calc (MR n).mesh ≤ (M n).mesh :=
            Partition.mesh_restrictRight_le _ u hut (hM_u n)
        _ ≤ (dyadicPartition s t hst n).mesh :=
            Partition.mesh_refinement_le (hM_ref n)
        _ = (t - s) / (2 : ℝ) ^ n := dyadicPartition_mesh s t hst n
    have hDR_mesh : ∀ n, (DR n).mesh ≤ (t - s) / (2 : ℝ) ^ n := by
      intro n
      calc (DR n).mesh = (t - u) / (2 : ℝ) ^ n := dyadicPartition_mesh u t hut n
        _ ≤ (t - s) / (2 : ℝ) ^ n := by
            apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2 ^ n).le; linarith
    have hRR_n_le : ∀ n, (RR n).n ≤ 6 * 2 ^ n := by
      intro n
      have h := Partition.n_merge_le (MR n) (DR n)
      have : (MR n).n ≤ (M n).n := Nat.sub_le _ _
      have : (DR n).n = 2 ^ n := rfl
      have : (M n).n ≤ 4 * 2 ^ n := hM_n_le n
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      lia
    set BR := 12 * C * (t - s) ^ (α + β)
    have hBR_nn : 0 ≤ BR :=
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 12) hC_nn) (rpow_nonneg hts _)
    have hcomp : ∀ n,
        ‖riemannSum Ξ (MR n) - dyadicSum₁ Ξ u t n‖ ≤ BR * r ^ n := by
      intro n
      rw [← dyadicPartition_riemannSum Ξ u t hut n]
      have hd_nn : 0 ≤ (t - s) / (2 : ℝ) ^ n := div_nonneg hts (by positivity)
      have h_left : ‖riemannSum Ξ (MR n) - riemannSum Ξ (RR n)‖ ≤
          ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) :=
        calc ‖riemannSum Ξ (MR n) - riemannSum Ξ (RR n)‖
            ≤ ↑(RR n).n * (C * (MR n).mesh ^ (α + β)) :=
              riemannSum_refinement_bound₂ hΞ hau hut htb _ _
                (Partition.merge_refines_left _ _)
          _ ≤ ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              apply mul_le_mul_of_nonneg_left _ hC_nn
              exact rpow_le_rpow (mesh_nonneg _) (hMR_mesh n) hαβ_nn
      have h_right : ‖riemannSum Ξ (RR n) - riemannSum Ξ (DR n)‖ ≤
          ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
        rw [norm_sub_rev]
        calc ‖riemannSum Ξ (DR n) - riemannSum Ξ (RR n)‖
            ≤ ↑(RR n).n * (C * (DR n).mesh ^ (α + β)) :=
              riemannSum_refinement_bound₂ hΞ hau hut htb _ _
                (Partition.merge_refines_right _ _)
          _ ≤ ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              apply mul_le_mul_of_nonneg_left _ hC_nn
              exact rpow_le_rpow (mesh_nonneg _) (hDR_mesh n) hαβ_nn
      calc ‖riemannSum Ξ (MR n) - riemannSum Ξ (DR n)‖
          ≤ ‖riemannSum Ξ (MR n) - riemannSum Ξ (RR n)‖ +
            ‖riemannSum Ξ (RR n) - riemannSum Ξ (DR n)‖ := by
              rw [show riemannSum Ξ (MR n) - riemannSum Ξ (DR n) =
                (riemannSum Ξ (MR n) - riemannSum Ξ (RR n)) +
                (riemannSum Ξ (RR n) - riemannSum Ξ (DR n)) from by abel]
              exact norm_add_le _ _
        _ ≤ ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) +
            ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) :=
            add_le_add h_left h_right
        _ = 2 * ↑(RR n).n * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by ring
        _ ≤ 2 * ↑(6 * 2 ^ n) * (C * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC_nn (rpow_nonneg hd_nn _))
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 2)
            exact_mod_cast hRR_n_le n
        _ = 12 * (C * ((2 : ℝ) ^ n * ((t - s) / (2 : ℝ) ^ n) ^ (α + β))) := by
            ring
        _ = 12 * (C * ((t - s) ^ (α + β) * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)))) := by
            congr 2; exact dyadic_geometric_factor hts n
        _ = BR * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) := by unfold BR; ring
        _ = BR * r ^ n := by
            congr 1; simp only [r, sewingRatio₂]
            rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (α + β - 1)) n,
                ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
            congr 1; ring
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp
      (sewingMap₂_tendsto hΞ hau hut htb)) (ε / 2) (half_pos hε)
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, BR * r ^ N₂ < ε / 2 := by
      by_cases hBR : BR ≤ 0
      · exact ⟨0, by linarith [mul_nonpos_of_nonpos_of_nonneg hBR (pow_nonneg hr₀ 0)]⟩
      · push_neg at hBR
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) hBR) hr₁
        exact ⟨N, by
          calc BR * r ^ N = r ^ N * BR := mul_comm _ _
            _ < (ε / 2 / BR) * BR := mul_lt_mul_of_pos_right hN hBR
            _ = ε / 2 := div_mul_cancel₀ _ (ne_of_gt hBR)⟩
    use max N₁ N₂
    intro n hn
    calc dist (riemannSum Ξ (MR n)) (I u t)
        ≤ dist (riemannSum Ξ (MR n)) (dyadicSum₁ Ξ u t n) +
          dist (dyadicSum₁ Ξ u t n) (I u t) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · rw [dist_eq_norm]
            calc ‖riemannSum Ξ (MR n) - dyadicSum₁ Ξ u t n‖
                ≤ BR * r ^ n := hcomp n
              _ ≤ BR * r ^ N₂ := by
                  apply mul_le_mul_of_nonneg_left
                    (pow_le_pow_of_le_one hr₀ hr₁.le (le_of_max_le_right hn)) hBR_nn
              _ < ε / 2 := hN₂
          · exact hN₁ n (le_of_max_le_left hn)
      _ = ε := add_halves ε
  -- Step 4: RS(M_n) = RS(M_n|_L) + RS(M_n|_R) → I(s,u) + I(u,t)
  have hRS_sum_tendsto :
      Tendsto (fun n => riemannSum Ξ (M n)) atTop (nhds (I s u + I u t)) := by
    have : (fun n => riemannSum Ξ (M n)) = fun n =>
        riemannSum Ξ ((M n).restrictLeft u hsu (hM_u n)) +
        riemannSum Ξ ((M n).restrictRight u hut (hM_u n)) := funext hRS_split
    rw [this]
    exact Tendsto.add hRS_L_tendsto hRS_R_tendsto
  -- Step 5: Uniqueness of limits
  exact tendsto_nhds_unique hRS_M_tendsto hRS_sum_tendsto
end Additive₂

end StochCalc
