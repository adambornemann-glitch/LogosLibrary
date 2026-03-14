/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/Unique.lean
-/

import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Properties

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Uniqueness -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniqueness of the Young integral**: any additive functional `J` satisfying
the same approximation bound as the Young integral must equal it.

More precisely: if `J` is additive on `[a,b]`, `J(s,s) = 0`, and
  `‖J(s,t) - (X(t) - X(s)) • Y(s)‖ ≤ M · |t-s|^θ`
for some `M ≥ 0` and `θ > 1`, then `J = ∫ Y dX`.

This is a corollary of `sewingMap₂_unique`. -/
theorem youngIntegral_unique
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {J : ℝ → ℝ → E}
    (_hJ_diag : ∀ s, J s s = 0)
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    {M : ℝ} (_hM : 0 ≤ M) {θ : ℝ} (hθ : 1 < θ)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - (X t - X s) • Y s‖ ≤ M * |t - s| ^ θ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      J s t = youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t := by
  intro s t has hst htb
  unfold youngIntegral
  set Ξ := youngApprox X Y
  set hcond := youngApprox_sewingCondition₂ hX hY hγδ
  set S := fun n => dyadicSum₁ Ξ s t n
  have hmap : sewingMap₂ Ξ (fun s t => |t - s|) (fun s t => |t - s|)
      δ γ (C_X * C_Y) 1 1 a b hcond s t = limUnder atTop S := by
    unfold sewingMap₂; exact dif_pos ⟨has, hst, htb⟩
  rw [hmap]
  -- Show S_n → J(s,t), then conclude by uniqueness of limits
  suffices h : Tendsto S atTop (nhds (J s t)) from
    tendsto_nhds_unique h (dyadicSum₂_cauchy hcond has hst htb).tendsto_limUnder
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- J telescopes over dyadic partitions by additivity
  have hJ_tel : ∀ n, J s t = ∑ k ∈ range (2 ^ n),
      J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) := by
    intro n; induction n with
    | zero => simp [dyadicPt]
    | succ n ih =>
      rw [ih, show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_lt : k < 2 ^ n := Finset.mem_range.mp hk
      rw [dyadicPt_double, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
          dyadicPt_double]
      exact hJ_add _ _ _
        (has.trans (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
        (dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega))
        (by rw [← dyadicPt_double s t n (k + 1)];
            exact dyadicPt_mono hst (n + 1) (by omega))
        ((dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2.trans htb)
  -- Geometric ratio for exponent θ
  set r := (2 : ℝ)⁻¹ ^ (θ - 1)
  have hr₀ : 0 ≤ r := rpow_nonneg (by positivity) _
  have hr₁ : r < 1 := rpow_lt_one (by positivity) (by norm_num) (by linarith)
  -- Choose N with M · |t-s|^θ · r^N < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M * |t - s| ^ θ * r ^ N < ε := by
    by_cases hMt : M * |t - s| ^ θ ≤ 0
    · exact ⟨0, by linarith [pow_nonneg hr₀ 0]⟩
    · push_neg at hMt
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hMt) hr₁
      exact ⟨N, by
        have := mul_lt_mul_of_pos_left hN hMt
        rwa [mul_div_cancel₀ ε (ne_of_gt hMt)] at this⟩
  use N; intro n hn
  rw [dist_comm, dist_eq_norm, hJ_tel n]
  simp only [S, dyadicSum₁]
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ range (2 ^ n), (J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n),
          M * |dyadicPt s t n (k + 1) - dyadicPt s t n k| ^ θ := by
        gcongr with k hk
        have hk_lt := Finset.mem_range.mp hk
        simp only [Ξ, youngApprox]
        exact hJ_bound _ _
          (has.trans (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
          (dyadicPt_mono hst n (by omega))
          ((dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2.trans htb)
    _ = ∑ _k ∈ range (2 ^ n), M * (|t - s| / 2 ^ n) ^ θ := by
        congr 1; ext k; rw [abs_dyadicPt_sub]
    _ = (2 : ℝ) ^ n * (M * (|t - s| / 2 ^ n) ^ θ) := by
        rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = M * ((2 : ℝ) ^ n * (|t - s| / 2 ^ n) ^ θ) := by ring
    _ = M * (|t - s| ^ θ * (2⁻¹) ^ (↑n * (θ - 1))) := by
        congr 1; exact dyadic_geometric_factor (abs_nonneg _) n
    _ = M * |t - s| ^ θ * r ^ n := by
        rw [show (2⁻¹ : ℝ) ^ (↑n * (θ - 1)) = r ^ n from by
          simp only [r]
          rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (θ - 1)) n,
              ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
          congr 1; ring]
        ring
    _ < ε := by
        by_cases h : M * |t - s| ^ θ ≤ 0
        · linarith [mul_nonpos_of_nonpos_of_nonneg h (pow_nonneg hr₀ n)]
        · push_neg at h
          calc M * |t - s| ^ θ * r ^ n
              ≤ M * |t - s| ^ θ * r ^ N :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_of_le_one hr₀ hr₁.le hn) h.le
            _ < ε := hN

end Uniqueness
