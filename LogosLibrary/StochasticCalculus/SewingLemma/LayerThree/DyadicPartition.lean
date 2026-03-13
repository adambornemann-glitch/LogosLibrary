/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerThree/RefinementCost.lean
-/
import LogosLibrary.StochasticCalculus.SewingLemma.LayerThree.ThetaEnergy

noncomputable section

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

/-! ### Refinement cost -/

section DyadicPartition

/-- **Key estimate (Layer 3)**: successive dyadic refinements are bounded by
the sum of `ω`-defects over the coarser partition.

`‖S_{n+1} - Sₙ‖ ≤ K · ∑_{k < 2^n} ω(dₖ, dₖ₊₁)^θ`

The proof is structurally identical to Layer 1 — pair, collapse via `dyadicPt_double`,
extract defects, apply the triangle inequality — but the per-defect bound uses
`K · ω(dₖ, dₖ₊₁)^θ` rather than `K · |t-s|^θ`. The critical payoff is that the
RHS is exactly `K · Φ_θ(Dₙ)`, and `thetaEnergy_tendsto_zero` drives it to zero. -/
theorem dyadicSum₃_diff_bound {Ξ : ℝ → ℝ → E}
    {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖ ≤
      K * ∑ k ∈ Finset.range (2 ^ n),
        ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
  -- Steps 1–4: pair level-(n+1) terms and reduce to sum of negated defects
  simp only [dyadicSum₁]
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring, sum_range_pair]
  simp only [show ∀ k : ℕ, 2 * k + 1 + 1 = 2 * (k + 1) from fun k => by omega]
  simp_rw [dyadicPt_double]
  rw [← Finset.sum_sub_distrib]
  simp_rw [show ∀ k : ℕ,
      Ξ (dyadicPt s t n k) (dyadicPt s t (n + 1) (2 * k + 1)) +
        Ξ (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1)) -
        Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1)) =
      -(sewingDefect₁ Ξ (dyadicPt s t n k) (dyadicPt s t (n + 1) (2 * k + 1))
          (dyadicPt s t n (k + 1)))
    from fun k => by simp only [sewingDefect₁]; abel]
  rw [Finset.sum_neg_distrib, norm_neg]
  -- Step 5: triangle inequality → per-defect bound → factor out K
  calc ‖∑ k ∈ range (2 ^ n), sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n),
          K * ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
        gcongr with k hk
        have hk_lt : k < 2 ^ n := Finset.mem_range.mp hk
        exact hΞ.defect_bound _ _ _
          (le_trans has (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1)
          (dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega))
          (by rw [← dyadicPt_double s t n (k + 1)];
              exact dyadicPt_mono hst (n + 1) (by omega))
          (le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb)
    _ = K * ∑ k ∈ range (2 ^ n),
          ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
        rw [Finset.mul_sum]

/-! ### Dyadic partitions as `Partition` objects -/

/-- The theta-energy of the dyadic partition equals the raw `Finset.range` sum
appearing in `dyadicSum₃_diff_bound`. -/
theorem thetaEnergy_dyadicPartition (ω : ℝ → ℝ → ℝ) (θ : ℝ)
    {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    thetaEnergy ω θ (dyadicPartition s t hst n) =
      ∑ k ∈ Finset.range (2 ^ n),
        ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ^ θ := by
  simp only [thetaEnergy, dyadicPartition, Partition.left, Partition.right]
  exact Eq.symm (sum_range fun i => ω (dyadicPt s t n i) (dyadicPt s t n (i + 1)) ^ θ)

/-- The mesh of the dyadic partition is at most `(t - s) / 2^n`. -/
theorem dyadicPartition_mesh_le {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    (dyadicPartition s t hst n).mesh ≤ (t - s) / (2 : ℝ) ^ n := by
  simp only [Partition.mesh]
  have h2n : (dyadicPartition s t hst n).n ≠ 0 := by
    simp only [dyadicPartition]; exact pow_ne_zero n (by norm_num)
  rw [dif_neg h2n]
  apply Finset.sup'_le
  intro i _
  simp only [dyadicPartition, Partition.right, Partition.left, dyadicPt_sub_succ]
  exact Std.IsPreorder.le_refl ((t - s) / 2 ^ n)

/-- The dyadic sums form a Cauchy sequence under the Layer 3 condition.

Unlike Layers 1–2, we do NOT have a geometric rate. Instead:
  `‖S_{n+1} - Sₙ‖ ≤ K · Φ_θ(Pₙ)`
where `Φ_θ(Pₙ) → 0` by `thetaEnergy_tendsto_zero`.

For Cauchy, we use the fact that `‖Sₘ - Sₙ‖ ≤ K · (Φ_θ(Pₙ) + Φ_θ(Pₘ))`
since the dyadic partition at level `m` refines the dyadic partition at level `n`
when `m ≥ n`. Actually, refinement gives the stronger `‖Sₘ - Sₙ‖ ≤ K · Φ_θ(Pₙ)`.
Since `Φ_θ(Pₙ) → 0`, for any `ε > 0` choose `N` with `K · Φ_θ(Pₙ) < ε` for `n ≥ N`,
then `‖Sₘ - Sₙ‖ < ε` for `m ≥ n ≥ N`. -/
theorem dyadicSum₃_cauchy {Ξ : ℝ → ℝ → E}
    {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    CauchySeq (fun n => dyadicSum₁ Ξ s t n) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => K * thetaEnergy ω θ (dyadicPartition s t hst n))
  · intro n
    rw [dist_eq_norm, norm_sub_rev, thetaEnergy_dyadicPartition]
    exact dyadicSum₃_diff_bound hΞ has hst htb n
  · exact (hΞ.energy_summable s t has hst htb).mul_left K

end DyadicPartition

/-- The theta-energy of dyadic partitions tends to zero: `Φ_θ(Dₙ) → 0`.
This combines `thetaEnergy_tendsto_zero` (ε-δ on mesh) with `dyadicPartition_mesh_le`
(mesh ≤ (t-s)/2^n → 0). -/
theorem thetaEnergy_dyadicPartition_tendsto {ω : ℝ → ℝ → ℝ} {a b : ℝ} {θ : ℝ}
    (hω : ContControl ω a b) (hθ : 1 < θ)
    {s t : ℝ} (has : a ≤ s) (htb : t ≤ b) (hst : s ≤ t) :
    Tendsto (fun n => thetaEnergy ω θ (dyadicPartition s t hst n)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := thetaEnergy_tendsto_zero hω hθ has htb hst ε hε
  -- Choose N so that (t - s) / 2^N < δ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (t - s) / (2 : ℝ) ^ N < δ := by
    by_cases hts : t - s = 0
    · exact ⟨0, by rw [hts, zero_div]; exact hδ_pos⟩
    · have hts_pos : 0 < t - s := lt_of_le_of_ne (sub_nonneg.mpr hst) (Ne.symm hts)
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hδ_pos hts_pos)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
      exact ⟨N, by
        rw [inv_pow] at hN
        rw [show (t - s) / (2:ℝ) ^ N = (2 ^ N)⁻¹ * (t - s) from by ring]
        have := mul_lt_mul_of_pos_right hN hts_pos
        rwa [div_mul_cancel₀ δ hts_pos.ne'] at this⟩
  use N; intro n hn
  rw [Real.dist_0_eq_abs, abs_of_nonneg]
  · exact hδ (dyadicPartition s t hst n)
      (lt_of_le_of_lt (dyadicPartition_mesh_le hst n)
        (lt_of_le_of_lt (div_le_div_of_nonneg_left (sub_nonneg.mpr hst) (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn)) hN))
  · rw [thetaEnergy_dyadicPartition]
    apply Finset.sum_nonneg; intro k _
    exact rpow_nonneg (hω.nonneg _ _
      (has.trans (dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).1)
      (dyadicPt_mono hst n (by omega))
      ((dyadicPt_mem_Icc hst (by grind only [= Finset.mem_range])).2.trans htb)) _

end StochCalc
