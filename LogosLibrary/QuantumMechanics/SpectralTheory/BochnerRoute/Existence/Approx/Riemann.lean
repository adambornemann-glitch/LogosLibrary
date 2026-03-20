/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/Approx.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.Approx.Integral

namespace SpectralBridge.Bochner.BochnerExistence

open SpectralBridge.Bochner
open Complex MeasureTheory Filter Topology Set Real Function

variable {f : ℝ → ℂ}


/-- Decompose an interval integral into a sum over equispaced sub-intervals:
    `∫_a^{a+NΔ} g = ∑_{j<N} ∫_{a+jΔ}^{a+(j+1)Δ} g`. -/
private lemma integral_eq_sum_adjacent {g : ℝ → ℂ} (hg : Continuous g) (a Δ : ℝ) :
    ∀ N : ℕ, ∫ t in a..(a + ↑N * Δ), g t =
      ∑ j ∈ Finset.range N, ∫ t in (a + ↑j * Δ)..(a + (↑j + 1) * Δ), g t
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← integral_eq_sum_adjacent hg a Δ n,
        show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm

/-- 1D equispaced left-endpoint Riemann sums converge to the interval integral.

Proof via uniform continuity on the compact interval `[0, T]`:
the error per sub-interval is `O(ε' · Δ)` where `ε'` is the modulus
of continuity at scale `Δ = T/N`, giving total error `T · ε' → 0`. -/
private lemma riemann1d_tendsto {g : ℝ → ℂ} (hg : Continuous g)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun M : ℕ => ((↑T : ℂ) / (↑(M + 1) : ℂ)) *
      ∑ j ∈ Finset.range (M + 1), g (↑j * T / ↑(M + 1)))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- ── Step 1: Uniform continuity on [0, T] gives δ for tolerance ε/(2T) ──
  set ε' := ε / (2 * T) with hε'_def
  have hε' : 0 < ε' := by positivity
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc 0 T) hg.continuousOn
  obtain ⟨δ, hδ, hδ_uc⟩ := Metric.uniformContinuousOn_iff.mp huc ε' hε'
  -- ── Step 2: Choose threshold so T/(M+1) < δ ──
  obtain ⟨K, hK⟩ := exists_nat_gt (T / δ)
  refine ⟨K, fun M hM => ?_⟩
  set N := M + 1 with hN_def
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (Nat.succ_pos M)
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  set Δ := T / ↑N with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos hT hN_pos
  have hNΔ : ↑N * Δ = T := mul_div_cancel₀ T hN_ne
  have hΔ_lt_δ : Δ < δ := by
    rw [hΔ_def, div_lt_iff₀ hN_pos, mul_comm]
    calc T = T / δ * δ := by rw [div_mul_cancel₀ T (ne_of_gt hδ)]
    _ < ↑K * δ := by exact mul_lt_mul_of_pos_right hK hδ
    _ ≤ ↑M * δ := by exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hM) hδ.le
    _ < ↑N * δ := by rw [hN_def]; push_cast; linarith
  -- ── Step 3: Rewrite Riemann sum as ∑_j ↑Δ * g(jΔ) ──
  have hpts : ∀ j : ℕ, (↑j : ℝ) * T / ↑N = ↑j * Δ := fun j => by
    rw [hΔ_def]; ring
  simp_rw [hpts]
  rw [show (↑T : ℂ) / (↑N : ℂ) = (↑Δ : ℂ) from by
    rw [hΔ_def]; push_cast; rw [hN_def]]
  rw [Finset.mul_sum]
  -- ── Step 4: Decompose integral via sub-intervals ──
  have hdecomp : ∫ t in (0 : ℝ)..T, g t =
      ∑ j ∈ Finset.range N, ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t := by
    have h := integral_eq_sum_adjacent hg 0 Δ N
    simp only [zero_add, mul_comm 1 Δ] at h ⊢
    grind only
  rw [hdecomp]
  -- ── Step 5: Bound dist = ‖∑_j (↑Δ·g(jΔ) - ∫_{jΔ}^{(j+1)Δ} g)‖ ──
  rw [dist_eq_norm]
  -- Rewrite as norm of sum of differences
  rw [← Finset.sum_sub_distrib]
  -- ── Step 6: Triangle inequality + per-term bound ──
  calc ‖∑ j ∈ Finset.range N,
        ((↑Δ : ℂ) * g (↑j * Δ) - ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t)‖
      ≤ ∑ j ∈ Finset.range N,
          ‖(↑Δ : ℂ) * g (↑j * Δ) - ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ε' * Δ := by
        apply Finset.sum_le_sum; intro j hj
        -- Key: ↑Δ * g(jΔ) = ∫ const, so the difference = ∫ (g(jΔ) - g(t)) dt
        rw [show (↑Δ : ℂ) * g (↑j * Δ) =
            ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g (↑j * Δ) from by
          rw [intervalIntegral.integral_const]; ring_nf; exact Eq.symm real_smul,
          show (∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g (↑j * Δ)) -
               (∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), g t) =
               ∫ t in (↑j * Δ)..(↑j * Δ + 1 * Δ), (g (↑j * Δ) - g t) from
            (intervalIntegral.integral_sub
              intervalIntegrable_const (hg.intervalIntegrable _ _)).symm]
        -- ‖∫ (g(jΔ) - g(t)) dt‖ ≤ ε' * |Δ|
        refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
          fun t ht => ?_) (by
          have : |↑j * Δ + 1 * Δ - ↑j * Δ| = Δ := by
            rw [show ↑j * Δ + 1 * Δ - ↑j * Δ = Δ from by ring]
            exact abs_of_pos hΔ_pos
          nlinarith)
        -- Uniform continuity: ‖g(jΔ) - g(t)‖ < ε' for |jΔ - t| < δ
        rw [Set.uIoc_of_le (by linarith : ↑j * Δ ≤ ↑j * Δ + 1 * Δ)] at ht
        obtain ⟨ht_lo, ht_hi⟩ := Set.mem_Ioc.mp ht
        have hj_mem : ↑j * Δ ∈ Set.Icc 0 T := by
          constructor
          · exact mul_nonneg (Nat.cast_nonneg j) hΔ_pos.le
          · have := Finset.mem_range.mp hj
            calc ↑j * Δ ≤ ↑N * Δ :=
                mul_le_mul_of_nonneg_right
                  (by exact_mod_cast (Finset.mem_range.mp hj).le) hΔ_pos.le
            _ = T := hNΔ
        have ht_mem : t ∈ Set.Icc 0 T := by
          constructor
          · linarith [mul_nonneg (Nat.cast_nonneg j) hΔ_pos.le]
          · have := Finset.mem_range.mp hj
            linarith [show ↑j * Δ + 1 * Δ ≤ T from by
              calc ↑j * Δ + 1 * Δ = (↑j + 1) * Δ := by ring
                _ ≤ ↑N * Δ := by
                    exact mul_le_mul_of_nonneg_right
                      (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj))
                      hΔ_pos.le
                _ = T := hNΔ]
        have hdist : dist (↑j * Δ) t < δ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith
        rw [← dist_eq_norm]
        exact le_of_lt (hδ_uc (↑j * Δ) hj_mem t ht_mem hdist)
    _ = T * ε' := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring_nf; nlinarith [hNΔ]
    _ < ε := by rw [hε'_def]; field_simp; linarith

/-- Parametric interval integral of a jointly continuous function is continuous. -/
private lemma continuous_parametric_intervalIntegral {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous (fun u => ∫ v in a..b, F u v) := by
  have hFu : ∀ u, Continuous (F u) := fun u =>
    hF.comp (continuous_const.prodMk continuous_id)
  apply continuous_iff_continuousAt.mpr; intro u₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Degenerate case
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨1, one_pos, fun _ _ => by simp [intervalIntegral.integral_same, dist_self, hε]⟩
  -- Uniform continuity on [u₀-1, u₀+1] × [[a, b]]
  have hba : (0 : ℝ) < |b - a| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have huc := (isCompact_Icc.prod isCompact_uIcc :
    IsCompact (Set.Icc (u₀ - 1) (u₀ + 1) ×ˢ Set.uIcc a b)).uniformContinuousOn_of_continuous
    hF.continuousOn
  obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc
    (ε / (2 * |b - a|)) (by positivity)
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun u hu => ?_⟩
  have hu_δ : dist u u₀ < δ₀ := lt_of_lt_of_le hu (min_le_left _ _)
  have hu_1 : dist u u₀ < 1 := lt_of_lt_of_le hu (min_le_right _ _)
  have hu_mem : u ∈ Set.Icc (u₀ - 1) (u₀ + 1) := by
    have h := abs_lt.mp (show |u - u₀| < 1 from by rwa [← Real.dist_eq])
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hu₀_mem : u₀ ∈ Set.Icc (u₀ - 1) (u₀ + 1) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  rw [dist_eq_norm, ← intervalIntegral.integral_sub
    ((hFu u).intervalIntegrable a b) ((hFu u₀).intervalIntegrable a b)]
  calc ‖∫ v in a..b, (F u v - F u₀ v)‖
      ≤ (ε / (2 * |b - a|)) * |b - a| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const
          fun v hv => ?_
        have hv_uIcc : v ∈ Set.uIcc a b := Ioc_subset_Icc_self hv
        have h1 : (u, v) ∈ Set.Icc (u₀ - 1) (u₀ + 1) ×ˢ Set.uIcc a b :=
          ⟨hu_mem, hv_uIcc⟩
        have h2 : (u₀, v) ∈ Set.Icc (u₀ - 1) (u₀ + 1) ×ˢ Set.uIcc a b :=
          ⟨hu₀_mem, hv_uIcc⟩
        have hdist : dist (u, v) (u₀, v) < δ₀ := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hu_δ
        rw [← dist_eq_norm]
        exact le_of_lt (hmod (u, v) h1 (u₀, v) h2 hdist)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith


/-- Riemann sums converge to the double integral for continuous functions on [0,T]².

This is the standard result: for `F` continuous on a compact rectangle,
the equispaced Riemann sum converges to the integral. -/
lemma riemannDoubleSum_tendsto {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun N => riemannDoubleSum F T (N + 1)) atTop
      (𝓝 (∫ u in (0:ℝ)..T, ∫ v in (0:ℝ)..T, F u v)) := by
  rw [Metric.tendsto_atTop]; intro ε hε
  -- ── Setup ──
  set G : ℝ → ℂ := fun u => ∫ v in (0:ℝ)..T, F u v
  have hG : Continuous G := continuous_parametric_intervalIntegral hF 0 T
  have hFu : ∀ u, Continuous (F u) := fun u =>
    hF.comp (continuous_const.prodMk continuous_id)
  -- ── Outer convergence: 1D Riemann for G gives N₁ ──
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (riemann1d_tendsto hG hT) (ε / 2) (by positivity)
  -- ── Inner uniform bound: uniform continuity of F on [0,T]² gives N₂ ──
  set η := ε / (4 * T ^ 2 + 1) with hη_def
  have hη : 0 < η := by positivity
  have huc := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc 0 T ×ˢ Set.Icc 0 T)).uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (T / δ)
  -- ── Choose threshold ──
  refine ⟨max N₁ K, fun M hM => ?_⟩
  set N := M + 1 with hN_def
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (Nat.succ_pos M)
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hN_Cne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set Δ := T / (↑N : ℝ) with hΔ_def
  have hΔ_pos : 0 < Δ := div_pos hT hN_pos
  have hNΔ : ↑N * Δ = T := mul_div_cancel₀ T hN_ne
  have hΔ_lt_δ : Δ < δ := by
    rw [hΔ_def, div_lt_iff₀ hN_pos, mul_comm]
    calc T = T / δ * δ := by rw [div_mul_cancel₀ T (ne_of_gt hδ)]
      _ < ↑K * δ := mul_lt_mul_of_pos_right hK hδ
      _ ≤ ↑M * δ := mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (le_trans (le_max_right N₁ K) hM)) hδ.le
      _ < ↑N * δ := by rw [hN_def]; push_cast; linarith
  -- ── Factor the double sum ──
  have h_factor : riemannDoubleSum F T N =
      ((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N,
        ((↑T : ℂ) / ↑N) * ∑ k ∈ Finset.range N, F (↑j * T / ↑N) (↑k * T / ↑N) := by
    unfold riemannDoubleSum; rw [sq, mul_assoc, Finset.mul_sum]
  -- ── Outer Riemann sum of G ──
  set outerR := ((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N, G (↑j * T / ↑N)
  -- ── Triangle inequality ──
  rw [h_factor]
  calc dist (((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N,
            ((↑T : ℂ) / ↑N) * ∑ k ∈ Finset.range N, F (↑j * T / ↑N) (↑k * T / ↑N))
          (∫ u in (0:ℝ)..T, G u)
      ≤ dist (((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N,
              ((↑T : ℂ) / ↑N) * ∑ k ∈ Finset.range N, F (↑j * T / ↑N) (↑k * T / ↑N))
            outerR +
        dist outerR (∫ u in (0:ℝ)..T, G u) := dist_triangle _ outerR _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · -- ── Term 1: inner Riemann error ──
          rw [dist_eq_norm, show ((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N,
              ((↑T : ℂ) / ↑N) * ∑ k ∈ Finset.range N, F (↑j * T / ↑N) (↑k * T / ↑N) -
              outerR = ((↑T : ℂ) / ↑N) * ∑ j ∈ Finset.range N,
              (((↑T : ℂ) / ↑N) * ∑ k ∈ Finset.range N, F (↑j * T / ↑N) (↑k * T / ↑N) -
               G (↑j * T / ↑N)) from by
            simp only [outerR]; rw [← mul_sub, Finset.sum_sub_distrib]]
          -- Factor out the real prefactor T/N
          rw [show (↑T : ℂ) / ↑N = (↑Δ : ℂ) from by push_cast [hΔ_def]; rfl]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ_pos]
          -- Bound the sum using triangle inequality
          calc Δ * ‖∑ j ∈ Finset.range N, _‖
              ≤ Δ * ∑ j ∈ Finset.range N,
                  ‖((↑Δ : ℂ)) * ∑ k ∈ Finset.range N,
                      F (↑j * T / ↑N) (↑k * T / ↑N) -
                    G (↑j * T / ↑N)‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _) hΔ_pos.le
            _ ≤ Δ * ∑ j ∈ Finset.range N, T * η := by
                apply mul_le_mul_of_nonneg_left _ hΔ_pos.le
                apply Finset.sum_le_sum; intro j hj
                -- ── Inner 1D error for v ↦ F(jΔ, v) ──
                set u := (↑j : ℝ) * T / ↑N
                -- Rewrite using integral decomposition
                have hpts_k : ∀ k : ℕ, (↑k : ℝ) * T / ↑N = ↑k * Δ := fun k => by
                  rw [hΔ_def]; ring
                simp_rw [hpts_k]
                rw [show (↑Δ : ℂ) = ((↑T : ℂ) / ↑N) from by push_cast [hΔ_def]; rfl]
                rw [Finset.mul_sum]
                -- Decompose G(u) = ∫₀ᵀ F(u,v) dv into sub-intervals
                have hdecomp : G u = ∑ k ∈ Finset.range N,
                    ∫ v in (↑k * Δ)..(↑k * Δ + 1 * Δ), F u v := by
                  simp only [G]
                  have h := integral_eq_sum_adjacent (hFu u) 0 Δ N
                  simp only [zero_add] at h; rw [hNΔ] at h
                  convert h using 2
                  ring_nf
                rw [hdecomp, ← Finset.sum_sub_distrib]
                -- Triangle inequality + per-cell bound
                calc ‖∑ k ∈ Finset.range N, _‖
                    ≤ ∑ k ∈ Finset.range N,
                      ‖(↑T / ↑N : ℂ) * F u (↑k * Δ) -
                       ∫ v in (↑k * Δ)..(↑k * Δ + 1 * Δ), F u v‖ := norm_sum_le _ _
                  _ ≤ ∑ k ∈ Finset.range N, η * Δ := by
                      apply Finset.sum_le_sum; intro k hk
                      rw [show (↑T / ↑N : ℂ) * F u (↑k * Δ) =
                          ∫ v in (↑k * Δ)..(↑k * Δ + 1 * Δ), F u (↑k * Δ) from by
                        rw [intervalIntegral.integral_const,
                            show ↑k * Δ + 1 * Δ - ↑k * Δ = Δ from by ring]
                        show (↑T / ↑N : ℂ) * F u (↑k * Δ) = Δ • F u (↑k * Δ)
                        rw [show (↑T / ↑N : ℂ) = (↑Δ : ℂ) from by push_cast [hΔ_def]; rfl]
                        exact Eq.symm real_smul,
                        ← intervalIntegral.integral_sub
                          intervalIntegrable_const
                          ((hFu u).intervalIntegrable _ _)]
                      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
                        fun v hv => ?_) (by
                        rw [show |↑k * Δ + 1 * Δ - ↑k * Δ| = Δ from by
                          rw [show ↑k * Δ + 1 * Δ - ↑k * Δ = Δ from by ring]
                          exact abs_of_pos hΔ_pos])
                      -- Uniform continuity bound
                      rw [Set.uIoc_of_le (by linarith : ↑k * Δ ≤ ↑k * Δ + 1 * Δ)] at hv
                      obtain ⟨hv_lo, hv_hi⟩ := Set.mem_Ioc.mp hv
                      have hu_mem : u ∈ Set.Icc 0 T := by
                        constructor
                        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg j) hT.le) hN_pos.le
                        · calc u = ↑j * (T / ↑N) := by ring
                            _ ≤ ↑N * (T / ↑N) := mul_le_mul_of_nonneg_right
                                (Nat.cast_le.mpr (by grind only [= Finset.mem_range]))
                                (div_nonneg hT.le hN_pos.le)
                            _ = T := hNΔ
                      have hkΔ_mem : (↑k * Δ) ∈ Set.Icc 0 T := by
                        constructor
                        · exact mul_nonneg (Nat.cast_nonneg k) hΔ_pos.le
                        · calc ↑k * Δ ≤ ↑N * Δ :=
                              mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
                              (by grind only [= Finset.mem_range])) hΔ_pos.le
                          _ = T := hNΔ
                      have hv_mem : v ∈ Set.Icc 0 T := by
                        constructor
                        · linarith [mul_nonneg (Nat.cast_nonneg k) hΔ_pos.le]
                        have hkΔ_le : ↑k * Δ + 1 * Δ ≤ T := by
                          calc ↑k * Δ + 1 * Δ = (↑k + 1) * Δ := by ring
                            _ ≤ ↑N * Δ := by
                                apply mul_le_mul_of_nonneg_right _ hΔ_pos.le
                                exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
                            _ = T := hNΔ
                        · linarith [hkΔ_le]
                      have hprod1 : (u, ↑k * Δ) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 T :=
                        ⟨hu_mem, hkΔ_mem⟩
                      have hprod2 : (u, v) ∈ Set.Icc 0 T ×ˢ Set.Icc 0 T :=
                        ⟨hu_mem, hv_mem⟩
                      have hdist : dist (u, ↑k * Δ) (u, v) < δ := by
                        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
                            Real.dist_eq, abs_of_nonpos (by linarith)]
                        linarith
                      rw [← dist_eq_norm, dist_comm]
                      have hmod_app := hmod (u, v) hprod2 (u, ↑k * Δ) hprod1 (by rwa [dist_comm])
                      simp only [Function.uncurry] at hmod_app
                      exact le_of_lt hmod_app
                  _ = T * η := by
                      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                      nlinarith [hNΔ]
            _ = Δ * ↑N * (T * η) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
            _ = T ^ 2 * η := by rw [show Δ * ↑N = T from by linarith [hNΔ]]; ring
            _ < ε / 2 := by
                rw [hη_def, show T ^ 2 * (ε / (4 * T ^ 2 + 1)) =
                  ε * T ^ 2 / (4 * T ^ 2 + 1) from by ring]
                rw [div_lt_iff₀ (by positivity : (0:ℝ) < 4 * T ^ 2 + 1)]
                nlinarith [sq_nonneg T]
        · -- ── Term 2: outer Riemann convergence ──
          exact hN₁ M (le_trans (le_max_left N₁ K) hM)
    _ = ε := by ring



/-- The real part of the Riemann double sum is non-negative, by positive-definiteness.

This is the core algebraic step: the Riemann sum is a PD quadratic form
with coefficients `c_j = exp(I * ω * j*T/N)` at points `t_j = j*T/N`. -/
lemma riemannDoubleSum_re_nonneg (hf : IsContinuous f)
    {T : ℝ} (_hT : 0 < T) (ω : ℝ) (N : ℕ) (_hN : 0 < N) :
    0 ≤ (riemannDoubleSum
      (fun u v => f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v))
      T N).re := by
  unfold riemannDoubleSum
  -- (T/N)² is a non-negative real number
  have hTN : (0:ℝ) ≤ (T / ↑N) ^ 2 := sq_nonneg _
  -- Factor: Re(↑r² * z) = r² * Re(z) for real r
  rw [show ((↑T : ℂ) / ↑N) ^ 2 = (((T / (↑N : ℝ)) ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [re_ofReal_mul]
  apply mul_nonneg hTN
  -- Rewrite the exponential product: e^{-iωu} * e^{iωv} = conj(e^{iωu}) * e^{iωv}
  have h_conj : ∀ (u : ℝ),
      exp (-I * ↑ω * ↑u) = starRingEnd ℂ (exp (I * ↑ω * ↑u)) := by
    intro u; rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal]
  simp_rw [h_conj]
  -- Rearrange each summand: f(tⱼ-tₖ) * conj(e^{iωtⱼ}) * e^{iωtₖ}
  --                        = conj(cⱼ) * cₖ * f(tⱼ - tₖ)
  -- where cⱼ = e^{iω·jT/N}
  -- State the goal in PD-friendly form, then ring out the difference
  suffices h : 0 ≤ (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      starRingEnd ℂ (exp (I * ↑ω * ↑(↑j * T / ↑N))) *
        exp (I * ↑ω * ↑(↑k * T / ↑N)) *
        f (↑j * T / ↑N - ↑k * T / ↑N)).re by
    convert h using 2
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  -- Now apply PD
  have h_pd := hf.pd N
    (fun j => ↑j * T / ↑N)
    (fun j => exp (I * ↑ω * ↑(↑j * T / ↑N)))
  convert h_pd using 2
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro j _
  rw [← Fin.sum_univ_eq_sum_range]


/-- The double integral has non-negative real part: combine Riemann convergence
    with per-sum non-negativity. -/
lemma re_nonneg_of_riemann_limit {T : ℝ} (hT : 0 < T) (ω : ℝ)
    (hf : IsContinuous f) :
    0 ≤ (∫ u in (0:ℝ)..T, ∫ v in (0:ℝ)..T,
      f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v)).re := by
  set F : ℝ → ℝ → ℂ := fun u v =>
    f (u - v) * exp (-I * ↑ω * ↑u) * exp (I * ↑ω * ↑v)
  -- F is continuous (needed for Riemann convergence)
  have hF_cont : Continuous (Function.uncurry F) := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact hf.continuity.comp (continuous_fst.sub continuous_snd)
      · exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
    · exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
  -- Riemann sums converge to the double integral
  have h_lim := riemannDoubleSum_tendsto hF_cont hT
  -- Each Riemann sum has non-negative .re
  have h_nn : ∀ N, 0 ≤ (riemannDoubleSum F T (N + 1)).re :=
    fun N => riemannDoubleSum_re_nonneg hf hT ω (N + 1) (Nat.succ_pos N)
  -- Non-negativity passes to the limit
  exact ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp h_lim)
    (Eventually.of_forall h_nn)



end SpectralBridge.Bochner.BochnerExistence
