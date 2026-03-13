/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/Map.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.Defs
import LogosLibrary.StochasticCalculus.SewingLemma.Condition
import LogosLibrary.StochasticCalculus.SewingLemma.LayerTwo.Decay
/-!
# The Sewing Lemma — Layer 2 (Cross-Controlled)

The **cross-controlled Sewing Lemma** handles the case where the defect of `Ξ` is bounded
by a *product* of two different controls:

  `‖δΞ(s, u, t)‖ ≤ K · ω₁(s, u)^α · ω₂(u, t)^β`

with `α + β > 1`. Each control `ωᵢ` is super-additive and satisfies a **Lipschitz-in-length**
condition: `ωᵢ(s, t) ≤ Lᵢ · (t - s)`.

## Why this version?

Layer 1 uses `|t - s|^θ` as the control, which suffices when both the integrand and
integrator have the same regularity type (e.g., both Hölder). But in many applications,
the two objects have *different* regularity:

* **Young integration**: `X` has finite `p`-variation, `Y` has finite `q`-variation,
  `1/p + 1/q > 1`. The defect `δΞ(s,u,t) = (Y(u) - Y(s))·(X(t) - X(u))` is naturally
  bounded by `‖Y‖_{q-var;[s,u]} · ‖X‖_{p-var;[u,t]}`, a product of two different controls.

* **Rough integration (level 2)**: For a `γ`-Hölder rough path `𝐗 = (X, 𝕏)`,
  the defect of the Taylor approximation `Ξ(s,t) = f(X_s)·X_{s,t} + Df(X_s)·𝕏_{s,t}`
  is bounded by `C · ‖X‖^{2γ}_{[s,u]} · ‖X‖^γ_{[u,t]}` — again a cross product.

The Lipschitz condition `ωᵢ(s,t) ≤ Lᵢ·(t-s)` is satisfied whenever the underlying path
is Hölder continuous, which covers all standard stochastic processes (Brownian motion,
fractional BM, etc.). For a `γ`-Hölder path, `ω(s,t) = ‖X‖_{p-var;[s,t]}^p` satisfies
`ω(s,t) ≤ C^p · |t-s|^{γp}`, which is much better than Lipschitz.

## Relationship to Layer 1

Layer 1 is the special case `ω₁ = ω₂ = |·|`, `α + β = θ`, `L₁ = L₂ = 1`.
Layer 2 strictly generalises Layer 1, but Layer 1's proofs are simpler and serve as
the template. The dyadic proof structure is identical — the Lipschitz condition on the
controls means `ωᵢ(t_k, t_{k+1}) ≤ Lᵢ · (t-s)/2^n`, giving the same geometric decay.

## Main definitions

* `SewingCondition₂`: the cross-controlled hypothesis bundle
* `LipControl`: a super-additive control with a Lipschitz-in-length bound
* `sewingMap₂`: the sewn map (identical construction, different bound)

## Main results

* `dyadicSum₂_diff_bound`: geometric decay with rate `2^{-n(α+β-1)}`
* `sewingMap₂_dist_le`: approximation bound
* `sewingMap₂_additive`: additivity
* `sewingMap₂_unique`: uniqueness

## References

* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]
* [Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*][friz2010]
* [Lyons, T., *Differential equations driven by rough signals*][lyons1998]

## Tags

sewing lemma, cross-controlled, Young integration, rough path, control function
-/

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Cauchy sequence and sewn map (Layer 2) -/

section SewnMap₂

/-- The dyadic sums form a Cauchy sequence under the Layer 2 condition. -/
theorem dyadicSum₂_cauchy {Ξ : ℝ → ℝ → E}
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => dyadicSum₁ Ξ s t n) := by
  apply cauchySeq_of_le_geometric (sewingRatio₂ α β)
    (K * L₁ ^ α * L₂ ^ β *
       |t - s| ^ (α + β) * (2 : ℝ)⁻¹ ^ (α + β))
    (sewingRatio₂_lt_one hΞ.one_lt_exp)
  intro n
  rw [dist_eq_norm, norm_sub_rev]
  exact dyadicSum₂_diff_bound' hΞ has hst htb n

/-- The sewn map vanishes on the diagonal. -/
theorem sewingMap₂_diag [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s s = 0 := by
  unfold sewingMap₂
  rw [dif_pos ⟨has, le_refl s, hsb⟩]
  have hconst : ∀ n, dyadicSum₁ Ξ s s n = 0 := by
    intro n
    simp only [dyadicSum₁, dyadicPt, sub_self, mul_zero, zero_div, add_zero]
    simp [hΞ.vanish_diag]
  simp_rw [hconst]
  exact tendsto_const_nhds.limUnder_eq

/-- **Approximation bound (Layer 2)**. -/
theorem sewingMap₂_dist_le [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ‖sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t - Ξ s t‖ ≤
      K * L₁ ^ α * L₂ ^ β *
        sewingConst₂ α β * (2 : ℝ)⁻¹ ^ (α + β) *
        |t - s| ^ (α + β) := by
  set S := fun n => dyadicSum₁ Ξ s t n
  -- Unfold sewingMap₂ to limUnder, rewrite Ξ s t as S 0
  have hmap : sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t = limUnder atTop S := by
    unfold sewingMap₂; exact dif_pos ⟨has, hst, htb⟩
  rw [hmap, ← dyadicSum₁_zero Ξ s t]
  -- Geometric bound setup
  set r := sewingRatio₂ α β
  set M := K * L₁ ^ α * L₂ ^ β * |t - s| ^ (α + β) * (2 : ℝ)⁻¹ ^ (α + β)
  have hr₀ : 0 ≤ r := le_of_lt (sewingRatio₂_pos hΞ.one_lt_exp)
  have hr₁ : r < 1 := sewingRatio₂_lt_one hΞ.one_lt_exp
  have hM₀ : 0 ≤ M := by
    unfold M
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg hΞ.K_nonneg (rpow_nonneg hΞ.L₁_nonneg _)
        · exact rpow_nonneg hΞ.L₂_nonneg _
      · exact rpow_nonneg (abs_nonneg _) _
    · exact rpow_nonneg (by positivity) _
  -- Each successive difference bounded by M * r^n
  have hd_bound : ∀ n, ‖S (n + 1) - S n‖ ≤ M * r ^ n :=
    fun n => dyadicSum₂_diff_bound' hΞ has hst htb n
  -- Strategy: bound ‖S N - S 0‖ for all N, then pass to the limit
  suffices hbound : ∀ N, ‖S N - S 0‖ ≤
      K * L₁ ^ α * L₂ ^ β * sewingConst₂ α β *
        (2 : ℝ)⁻¹ ^ (α + β) * |t - s| ^ (α + β) from
    le_of_tendsto
      ((dyadicSum₂_cauchy hΞ has hst htb).tendsto_limUnder.sub tendsto_const_nhds).norm
      (Eventually.of_forall hbound)
  intro N
  -- Telescope: S N - S 0 = ∑_{k<N} (S(k+1) - S(k))
  have htel : S N - S 0 = ∑ k ∈ range N, (S (k + 1) - S k) := by
    induction N with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ← ih]; abel
  rw [htel]
  calc ‖∑ k ∈ range N, (S (k + 1) - S k)‖
      ≤ ∑ k ∈ range N, ‖S (k + 1) - S k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range N, M * r ^ k := by
        gcongr with k _; exact hd_bound k
    _ = M * ∑ k ∈ range N, r ^ k := by rw [Finset.mul_sum]
    _ ≤ M * (1 - r)⁻¹ := by
        gcongr
        have hsumm := summable_geometric_of_lt_one hr₀ hr₁
        rw [← tsum_geometric_of_lt_one hr₀ hr₁]
        exact hsumm.sum_le_tsum _ (fun k _ => pow_nonneg hr₀ k)
    _ = K * L₁ ^ α * L₂ ^ β * sewingConst₂ α β *
          (2 : ℝ)⁻¹ ^ (α + β) * |t - s| ^ (α + β) := by
        have : (1 - r)⁻¹ = sewingConst₂ α β := by
          simp [sewingConst₂, one_div]; rfl
        rw [this]; unfold M; ring

/-- **Uniqueness (Layer 2)**. -/
theorem sewingMap₂_unique [CompleteSpace E]
    {Ξ : ℝ → ℝ → E} {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {J : ℝ → ℝ → E} {C' : ℝ}
    (hJ_add : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      J s t = J s u + J u t)
    (hJ_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖J s t - Ξ s t‖ ≤ C' * |t - s| ^ (α + β))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    J s t = sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t := by
  set S := fun n => dyadicSum₁ Ξ s t n
  have hmap : sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ s t = limUnder atTop S := by
    unfold sewingMap₂; exact dif_pos ⟨has, hst, htb⟩
  rw [hmap]
  suffices h : Tendsto S atTop (nhds (J s t)) from
    tendsto_nhds_unique h (dyadicSum₂_cauchy hΞ has hst htb).tendsto_limUnder
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
      rw [dyadicPt_double, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega, dyadicPt_double]
      exact hJ_add _ _ _
        (le_trans has (dyadicPt_mem_Icc hst (by omega : k ≤ 2 ^ n)).1)
        (dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega : 2 * k ≤ 2 * k + 1))
        (by rw [← dyadicPt_double s t n (k + 1)];
            exact dyadicPt_mono hst (n + 1) (by omega : 2 * k + 1 ≤ 2 * (k + 1)))
        (le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb)
  set r := sewingRatio₂ α β
  have hr₀ : 0 ≤ r := le_of_lt (sewingRatio₂_pos hΞ.one_lt_exp)
  have hr₁ : r < 1 := sewingRatio₂_lt_one hΞ.one_lt_exp
  -- Choose N such that C'·|t-s|^{α+β}·r^N < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C' * |t - s| ^ (α + β) * r ^ N < ε := by
    by_cases hC : C' * |t - s| ^ (α + β) ≤ 0
    · exact ⟨0, by linarith [pow_nonneg hr₀ (0 : ℕ)]⟩
    · push_neg at hC
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hr₁
      exact ⟨N, by
        have := mul_lt_mul_of_pos_left hN hC
        rwa [mul_div_cancel₀ ε (ne_of_gt hC)] at this⟩
  use N; intro n hn
  rw [dist_comm, dist_eq_norm, hJ_tel n]
  simp only [S, dyadicSum₁]
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ range (2 ^ n), (J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖J (dyadicPt s t n k) (dyadicPt s t n (k + 1)) -
          Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n), C' * |dyadicPt s t n (k + 1) - dyadicPt s t n k| ^ (α + β) := by
        gcongr with k hk
        exact hJ_bound _ _
          (le_trans has (dyadicPt_mem_Icc hst (le_of_lt (Finset.mem_range.mp hk))).1)
          (dyadicPt_mono hst n (by omega))
          (le_trans (dyadicPt_mem_Icc hst (by simp; apply Finset.mem_range.mp hk : k + 1 ≤ 2 ^ n)).2 htb)
    _ = ∑ _k ∈ range (2 ^ n), C' * (|t - s| / (2 : ℝ) ^ n) ^ (α + β) := by
        congr 1; ext k; rw [abs_dyadicPt_sub]
    _ = (2 : ℝ) ^ n * (C' * (|t - s| / (2 : ℝ) ^ n) ^ (α + β)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = C' * (|t - s| ^ (α + β) * ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1))) := by
        rw [← dyadic_geometric_factor (abs_nonneg _) n]; ring
    _ = C' * |t - s| ^ (α + β) * r ^ n := by
        have hrn : ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) = r ^ n := by
          simp only [r, sewingRatio₂]
          rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (α + β - 1)) n,
              ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
          congr 1; ring
        rw [hrn]; ring
    _ < ε := by
        by_cases h : C' * |t - s| ^ (α + β) ≤ 0
        · linarith [mul_nonpos_of_nonpos_of_nonneg h (pow_nonneg hr₀ n)]
        · push_neg at h
          calc C' * |t - s| ^ (α + β) * r ^ n
              ≤ C' * |t - s| ^ (α + β) * r ^ N :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₀ hr₁.le hn) h.le
            _ < ε := hN

end SewnMap₂

end StochCalc
