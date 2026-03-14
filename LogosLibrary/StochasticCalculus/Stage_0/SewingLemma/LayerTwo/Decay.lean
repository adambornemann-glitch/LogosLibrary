/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/LayerTwo/Decay.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.Defs
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.Condition
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

/-- A Lipschitz control is bounded on sub-intervals by a multiple of the interval length. -/
theorem LipControl.bound_on_dyadic {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : LipControl ω a b) {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (n k : ℕ) (hk : k < 2 ^ n) :
    ω (dyadicPt s t n k) (dyadicPt s t n (k + 1)) ≤
      hω.lip_const * (t - s) / (2 : ℝ) ^ n := by
  calc ω (dyadicPt s t n k) (dyadicPt s t n (k + 1))
      ≤ hω.lip_const * (dyadicPt s t n (k + 1) - dyadicPt s t n k) := by
        apply hω.lip_bound
        · exact le_trans has (dyadicPt_mem_Icc hst (le_of_lt hk)).1
        · exact dyadicPt_mono hst n (by omega)
        · exact le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb
    _ = hω.lip_const * ((t - s) / (2 : ℝ) ^ n) := by
        congr 1; exact dyadicPt_sub_succ s t n k
    _ = hω.lip_const * (t - s) / (2 : ℝ) ^ n := by ring

/-- A Lipschitz control is monotone: `ω(s, t) ≤ ω(s', t')` when `[s, t] ⊆ [s', t']`. -/
theorem LipControl.mono_interval {ω : ℝ → ℝ → ℝ} {a b : ℝ}
    (hω : LipControl ω a b) {s s' t t' : ℝ}
    (has : a ≤ s') (hs : s' ≤ s) (ht : t ≤ t') (htb : t' ≤ b)
    (hst : s ≤ t) :
    ω s t ≤ ω s' t' := by
  -- ω(s', t') ≥ ω(s', s) + ω(s, t') ≥ ω(s, t') ≥ ω(s, t) + ω(t, t') ≥ ω(s, t)
  calc ω s t
      ≤ ω s t + ω t t' := le_add_of_nonneg_right (hω.nonneg t t'
          (le_trans has (le_trans hs hst)) ht htb)
    _ ≤ ω s t' := hω.superadd s t t' (le_trans has hs) hst ht htb
    _ ≤ ω s' s + ω s t' := le_add_of_nonneg_left (hω.nonneg s' s has hs
          (le_trans (le_trans hst ht) htb))
    _ ≤ ω s' t' := hω.superadd s' s t' has hs (le_trans hst ht) htb


/-! ### Geometric decay for Layer 2 -/

section Decay₂

theorem sewingRatio₂_pos {α β : ℝ} (_hαβ : 1 < α + β) : 0 < sewingRatio₂ α β :=
  rpow_pos_of_pos (by positivity : (0 : ℝ) < 2⁻¹) _

theorem sewingRatio₂_lt_one {α β : ℝ} (hαβ : 1 < α + β) : sewingRatio₂ α β < 1 :=
  rpow_lt_one (by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1) (by linarith)

theorem sewingConst₂_pos {α β : ℝ} (hαβ : 1 < α + β) : 0 < sewingConst₂ α β := by
  apply div_pos one_pos; linarith [sewingRatio₂_lt_one hαβ]

/-- **Key estimate (Layer 2)**: successive dyadic refinements decay geometrically.

The proof follows the same structure as Layer 1, but the bound on each defect uses
the product structure:

  `‖δΞ(tₖ, mₖ, tₖ₊₁)‖ ≤ K · ω₁(tₖ, mₖ)^α · ω₂(mₖ, tₖ₊₁)^β`
  `                      ≤ K · (L₁·|t-s|/2^{n+1})^α · (L₂·|t-s|/2^{n+1})^β`
  `                      = K · L₁^α · L₂^β · (|t-s|/2^{n+1})^{α+β}`

Summing `2^n` such terms:
  `2^n · K · L₁^α · L₂^β · (|t-s|/2^{n+1})^{α+β}`
  `= K · L₁^α · L₂^β · |t-s|^{α+β} · 2^n · 2^{-(n+1)(α+β)}`
  `= K · L₁^α · L₂^β · |t-s|^{α+β} · 2^{-(α+β)} · 2^{-n(α+β-1)}`

The factor `2^{-n(α+β-1)}` decays geometrically since `α + β > 1`. -/
theorem dyadicSum₂_diff_bound {Ξ : ℝ → ℝ → E}
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖ ≤
      K * L₁ ^ α * L₂ ^ β *
        |t - s| ^ (α + β) *
        (2 : ℝ)⁻¹ ^ (α + β) *
        ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) := by
  -- Preliminaries
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have h2n1 : (0 : ℝ) < (2 : ℝ) ^ (n + 1 : ℕ) := by positivity
  have hd : 0 ≤ (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) := div_nonneg hts h2n1.le
  have hLd₁ : 0 ≤ L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) :=
    div_nonneg (mul_nonneg hΞ.L₁_nonneg hts) h2n1.le
  have hLd₂ : 0 ≤ L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) :=
    div_nonneg (mul_nonneg hΞ.L₂_nonneg hts) h2n1.le
  -- Steps 1–4: pair level-(n+1) terms and reduce to sum of defects
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
  -- Steps 5+: triangle inequality → per-summand bound → algebra
  calc ‖∑ k ∈ range (2 ^ n), sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖
      ≤ ∑ k ∈ range (2 ^ n), ‖sewingDefect₁ Ξ (dyadicPt s t n k)
          (dyadicPt s t (n + 1) (2 * k + 1)) (dyadicPt s t n (k + 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (2 ^ n),
          K * (L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ α *
            (L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ β := by
        gcongr with k hk
        have hk_lt : k < 2 ^ n := mem_range.mp hk
        -- Interval membership
        have has_dk := le_trans has (dyadicPt_mem_Icc hst (le_of_lt hk_lt)).1
        have hdk_mk : dyadicPt s t n k ≤ dyadicPt s t (n + 1) (2 * k + 1) :=
          dyadicPt_double s t n k ▸ dyadicPt_mono hst (n + 1) (by omega)
        have hmk_dk1 : dyadicPt s t (n + 1) (2 * k + 1) ≤ dyadicPt s t n (k + 1) := by
          rw [← dyadicPt_double s t n (k + 1)]
          exact dyadicPt_mono hst (n + 1) (by omega)
        have hdk1_b := le_trans (dyadicPt_mem_Icc hst (by omega : k + 1 ≤ 2 ^ n)).2 htb
        -- ω₁ Lipschitz bound on left half-interval
        have hω₁_bound : ω₁ (dyadicPt s t n k)
            (dyadicPt s t (n + 1) (2 * k + 1)) ≤
            L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) := by
          rw [← dyadicPt_double s t n k]
          calc ω₁ (dyadicPt s t (n + 1) (2 * k)) (dyadicPt s t (n + 1) (2 * k + 1))
              ≤ L₁ * (dyadicPt s t (n + 1) (2 * k + 1) -
                  dyadicPt s t (n + 1) (2 * k)) :=
                hΞ.ω₁_lip _ _
                  (le_trans has (dyadicPt_mem_Icc hst (by omega : 2 * k ≤ 2 ^ (n + 1))).1)
                  (dyadicPt_mono hst (n + 1) (by omega))
                  (le_trans (dyadicPt_mem_Icc hst
                    (by omega : 2 * k + 1 ≤ 2 ^ (n + 1))).2 htb)
            _ = L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) := by
                rw [dyadicPt_sub_succ]; ring
        -- ω₂ Lipschitz bound on right half-interval
        have hω₂_bound : ω₂ (dyadicPt s t (n + 1) (2 * k + 1))
            (dyadicPt s t n (k + 1)) ≤
            L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) := by
          rw [← dyadicPt_double s t n (k + 1)]
          calc ω₂ (dyadicPt s t (n + 1) (2 * k + 1))
                  (dyadicPt s t (n + 1) (2 * (k + 1)))
              ≤ L₂ * (dyadicPt s t (n + 1) (2 * (k + 1)) -
                  dyadicPt s t (n + 1) (2 * k + 1)) :=
                hΞ.ω₂_lip _ _
                  (le_trans has (dyadicPt_mem_Icc hst
                    (by omega : 2 * k + 1 ≤ 2 ^ (n + 1))).1)
                  (dyadicPt_mono hst (n + 1) (by omega))
                  (le_trans (dyadicPt_mem_Icc hst
                    (by omega : 2 * (k + 1) ≤ 2 ^ (n + 1))).2 htb)
            _ = L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) := by
                rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega, dyadicPt_sub_succ]
                ring
        -- Combine: defect bound → rpow monotonicity
        calc ‖sewingDefect₁ Ξ _ _ _‖
            ≤ K * ω₁ _ _ ^ α * ω₂ _ _ ^ β :=
              hΞ.defect_bound _ _ _ has_dk hdk_mk hmk_dk1 hdk1_b
          _ ≤ K * (L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ α *
                (L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ β := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left
                  (rpow_le_rpow
                    (hΞ.ω₁_nonneg _ _ has_dk hdk_mk (le_trans hmk_dk1 hdk1_b))
                    hω₁_bound hΞ.α_nonneg)
                  hΞ.K_nonneg
              · exact rpow_le_rpow
                  (hΞ.ω₂_nonneg _ _ (le_trans has_dk hdk_mk) hmk_dk1 hdk1_b)
                  hω₂_bound hΞ.β_nonneg
              · exact rpow_nonneg
                  (hΞ.ω₂_nonneg _ _ (le_trans has_dk hdk_mk) hmk_dk1 hdk1_b) _
              · exact mul_nonneg hΞ.K_nonneg (rpow_nonneg hLd₁ _)
    _ = (2 : ℝ) ^ n * (K * (L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ α *
          (L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ β) := by
        rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ = K * L₁ ^ α * L₂ ^ β * |t - s| ^ (α + β) *
          (2 : ℝ)⁻¹ ^ (α + β) *
          ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) := by
        -- Factor L₁^α, L₂^β out of rpow via mul_rpow
        rw [show L₁ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) =
            L₁ * ((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) from mul_div_assoc _ _ _,
          mul_rpow hΞ.L₁_nonneg hd,
          show L₂ * (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) =
            L₂ * ((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) from mul_div_assoc _ _ _,
          mul_rpow hΞ.L₂_nonneg hd]
        -- Rearrange to group d^α * d^β and combine via rpow_add'
        rw [show (2 : ℝ) ^ n *
            (K * (L₁ ^ α * ((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ α) *
            (L₂ ^ β * ((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ β)) =
            K * L₁ ^ α * L₂ ^ β * ((2 : ℝ) ^ n *
            (((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ α *
            ((t - s) / (2 : ℝ) ^ (n + 1 : ℕ)) ^ β)) from by ring]
        rw [← rpow_add' hd (ne_of_gt (by linarith [hΞ.one_lt_exp] : (0 : ℝ) < α + β))]
        -- Level shift: (t-s)/2^{n+1} = ((t-s)/2^n) * 2⁻¹
        rw [show (t - s) / (2 : ℝ) ^ (n + 1 : ℕ) =
            (t - s) / (2 : ℝ) ^ n * (2 : ℝ)⁻¹ from by rw [pow_succ]; ring]
        -- Split rpow of product
        rw [mul_rpow (div_nonneg hts (by positivity)) (by positivity : (0 : ℝ) ≤ 2⁻¹)]
        -- Rearrange to isolate 2^n * ((t-s)/2^n)^{α+β}
        rw [show K * L₁ ^ α * L₂ ^ β * ((2 : ℝ) ^ n *
            (((t - s) / (2 : ℝ) ^ n) ^ (α + β) * (2 : ℝ)⁻¹ ^ (α + β))) =
            K * L₁ ^ α * L₂ ^ β * (2 : ℝ)⁻¹ ^ (α + β) *
            ((2 : ℝ) ^ n * ((t - s) / (2 : ℝ) ^ n) ^ (α + β)) from by ring]
        -- Apply dyadic_geometric_factor with θ = α + β
        rw [dyadic_geometric_factor hts n]
        -- Replace (t - s)^{α+β} with |t - s|^{α+β}
        rw [show (t - s) ^ (α + β) = |t - s| ^ (α + β) from by
          rw [abs_of_nonneg hts]]
        ring

/-- Simplified form: collect all the constants into one factor times geometric decay. -/
theorem dyadicSum₂_diff_bound' {Ξ : ℝ → ℝ → E}
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (n : ℕ) :
    let M := K * L₁ ^ α * L₂ ^ β *
               |t - s| ^ (α + β) * (2 : ℝ)⁻¹ ^ (α + β)
    let r := sewingRatio₂ α β
    ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖ ≤ M * r ^ n := by
  intro M r
  calc ‖dyadicSum₁ Ξ s t (n + 1) - dyadicSum₁ Ξ s t n‖
      ≤ K * L₁ ^ α * L₂ ^ β * |t - s| ^ (α + β) *
          (2 : ℝ)⁻¹ ^ (α + β) *
          ((2 : ℝ)⁻¹) ^ (↑n * (α + β - 1)) :=
        dyadicSum₂_diff_bound hΞ has hst htb n
    _ = M * r ^ n := by
        congr 1
        simp only [r, sewingRatio₂]
        rw [← rpow_natCast ((2 : ℝ)⁻¹ ^ (α + β - 1)) n,
            ← rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
        congr 1; ring

end Decay₂

end StochCalc
