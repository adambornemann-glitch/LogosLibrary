/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_0/API.lean
-/
import LogosLibrary.StochasticCalculus.Stage_0.PVariation
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerOne.Map
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerTwo.Map
import LogosLibrary.StochasticCalculus.Stage_0.SewingLemma.LayerThree.Map

open Real Set Filter Finset

variable {E : Type*} [NormedAddCommGroup E]

namespace StochCalc

variable [CompleteSpace E]

section API₁



/-! ### Convenience API -/

/-- Bundle: the Sewing Lemma (Layer 1) produces a unique additive functional
satisfying an approximation bound.

Requires both `SewingCondition₁` (for existence, approximation, uniqueness)
and `SewingCondition₂` (for additivity at arbitrary split points). -/
theorem sewing_lemma₁ {Ξ : ℝ → ℝ → E}
    {θ K a b : ℝ}
    (hΞ₁ : SewingCondition₁ Ξ θ K a b)
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K₂ L₁ L₂ : ℝ}
    (hΞ₂ : SewingCondition₂ Ξ ω₁ ω₂ α β K₂ L₁ L₂ a b) :
    ∃ I : ℝ → ℝ → E,
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∀ s t, a ≤ s → s ≤ t → t ≤ b →
        ‖I s t - Ξ s t‖ ≤ K * sewingConst₁ θ * |t - s| ^ θ) ∧
      (∀ (J : ℝ → ℝ → E) (C' : ℝ),
        (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → J s t = J s u + J u t) →
        (∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖J s t - Ξ s t‖ ≤ C' * |t - s| ^ θ) →
        ∀ s t, a ≤ s → s ≤ t → t ≤ b → J s t = I s t) :=
  ⟨sewingMap₁ Ξ θ K a b hΞ₁,
    fun _s has hsb => sewingMap₁_diag hΞ₁ has hsb,
    fun _s _u _t has hsu hut htb => sewingMap₁_additive hΞ₁ hΞ₂ has hsu hut htb,
    fun _s _t has hst htb => sewingMap₁_dist_le hΞ₁ has hst htb,
    fun _J _C' hJ_add hJ_bound _s _t has hst htb =>
      sewingMap₁_unique hΞ₁ hJ_add hJ_bound has hst htb⟩

end API₁

section API₂

/-- Bundle: the Sewing Lemma (Layer 2) produces an additive functional
satisfying an approximation bound. -/
theorem sewing_lemma₂ {Ξ : ℝ → ℝ → E}
    {ω₁ ω₂ : ℝ → ℝ → ℝ} {α β K L₁ L₂ a b : ℝ}
    (hΞ : SewingCondition₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b) :
    ∃ I : ℝ → ℝ → E,
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∀ s t, a ≤ s → s ≤ t → t ≤ b →
        ‖I s t - Ξ s t‖ ≤
          K * L₁ ^ α * L₂ ^ β *
            sewingConst₂ α β * (2 : ℝ)⁻¹ ^ (α + β) *
            |t - s| ^ (α + β)) := by
  exact ⟨sewingMap₂ Ξ ω₁ ω₂ α β K L₁ L₂ a b hΞ,
    fun s has hsb => sewingMap₂_diag hΞ has hsb,
    fun s u t has hsu hut htb => sewingMap₂_additive hΞ has hsu hut htb,
    fun s t has hst htb => sewingMap₂_dist_le hΞ has hst htb⟩

end API₂

section API₃

/-- **The Sewing Lemma (general form)**: given a continuous super-additive control `ω`,
an exponent `θ > 1`, and a two-parameter map `Ξ` whose defect is bounded by
`K · ω(s,t)^θ`, there exists a unique additive functional `I` satisfying:

1. `I(s, s) = 0`
2. `I(s, t) = I(s, u) + I(u, t)` for `s ≤ u ≤ t`
3. `‖I(s, t) - Ξ(s, t)‖ ≤ K · ∑ₙ Φ_θ(Dₙ(s,t))`

For Lipschitz controls (Layers 1–2), the tsum bound reduces to
`K · C · |t-s|^θ` for an explicit geometric constant `C = (1 - 2^{-(θ-1)})⁻¹`.
For general continuous controls, the tsum is finite by `energy_summable`
and vanishes as `t - s → 0` by `energy_vanish`. -/
theorem sewing_lemma₃ {Ξ : ℝ → ℝ → E}
    {ω : ℝ → ℝ → ℝ} {θ K a b : ℝ}
    (hΞ : SewingCondition₃ Ξ ω θ K a b) :
    ∃ I : ℝ → ℝ → E,
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∀ s t, a ≤ s → (hst : s ≤ t) → t ≤ b →
        ‖I s t - Ξ s t‖ ≤ K * ∑' n, thetaEnergy ω θ (dyadicPartition s t hst n)) := by
  exact ⟨sewingMap₃ Ξ ω θ K a b hΞ,
    fun s has hsb => sewingMap₃_diag hΞ has hsb,
    fun s u t has hsu hut htb => sewingMap₃_additive hΞ has hsu hut htb,
    fun s t has hst htb => sewingMap₃_dist_le hΞ has hst htb⟩


end API₃

section YoungIntegration

/-- **Young integration** as an application of the cross-controlled Sewing Lemma.

For `X : ℝ → ℝ` of finite `p`-variation and `Y : ℝ → ℝ` of finite `q`-variation
on `[a, b]` with `1/p + 1/q > 1`, the Young integral `∫ Y dX` exists.

We define `Ξ(s, t) = Y(s) · (X(t) - X(s))`. The defect is:
  `δΞ(s, u, t) = -(Y(u) - Y(s)) · (X(t) - X(u))`

For Hölder-regular `X` and `Y` (γ-Hölder and δ-Hölder with γ + δ > 1):
  `|δΞ(s, u, t)| ≤ C_Y · |u - s|^δ · C_X · |t - u|^γ`

This is exactly the cross-controlled form with:
  `ω₁(s, t) = |t - s|`, `α = δ` (integrand Hölder exponent)
  `ω₂(s, t) = |t - s|`, `β = γ` (integrator Hölder exponent)
  `α + β = δ + γ > 1` ✓ -/
theorem young_integral_holder [NormedSpace ℝ E]
    {X : ℝ → ℝ} {Y : ℝ → E}
    {γ δ : ℝ} {C_X C_Y : ℝ} {a b : ℝ}
    (hγδ : 1 < γ + δ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hab : a ≤ b)
    (hC_X : 0 ≤ C_X) (hC_Y : 0 ≤ C_Y)
    (hX_hold : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      |X t - X s| ≤ C_X * |t - s| ^ γ)
    (hY_hold : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖Y t - Y s‖ ≤ C_Y * |t - s| ^ δ) :
    ∃ I : ℝ → ℝ → E,
      (∀ s, a ≤ s → s ≤ b → I s s = 0) ∧
      (∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b → I s t = I s u + I u t) ∧
      (∃ C, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
        ‖I s t - (X t - X s) • Y s‖ ≤ C * |t - s| ^ (γ + δ)) := by
  -- Define Ξ(s, t) = (X t - X s) • Y s
  set Ξ := fun s t => (X t - X s) • Y s with hΞ_def
  set ω : ℝ → ℝ → ℝ := fun s t => |t - s|
  set κ := C_X * C_Y
  -- Defect identity: δΞ(s, u, t) = (X t - X u) • (Y s - Y u)
  have hdefect_eq : ∀ s u t,
      sewingDefect₁ Ξ s u t = (X t - X u) • (Y s - Y u) := by
    intro s u t; simp only [sewingDefect₁, hΞ_def, sub_smul, smul_sub]; abel
  -- Super-additivity helper for |t - s|
  have hω_superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
      ω s u + ω u t ≤ ω s t := by
    intro s u t _ hsu hut _
    simp only [ω, abs_of_nonneg (sub_nonneg.mpr hsu),
      abs_of_nonneg (sub_nonneg.mpr hut),
      abs_of_nonneg (sub_nonneg.mpr (hsu.trans hut))]
    linarith
  -- Lipschitz helper
  have hω_lip : ∀ s t, a ≤ s → s ≤ t → t ≤ b → ω s t ≤ 1 * (t - s) := by
    intro s t _ hst _
    simp only [ω, abs_of_nonneg (sub_nonneg.mpr hst), one_mul]; rfl
  -- Build SewingCondition₂
  have hcond : SewingCondition₂ Ξ ω ω δ γ κ 1 1 a b := {
    vanish_diag := fun s => by simp [hΞ_def]
    one_lt_exp := by linarith
    α_nonneg := hδ
    β_nonneg := hγ
    K_nonneg := mul_nonneg hC_X hC_Y
    hab := hab
    ω₁_nonneg := fun s t _ _ _ => abs_nonneg _
    ω₁_diag := fun s => by simp [ω]
    ω₁_superadd := hω_superadd
    ω₁_lip := hω_lip
    defect_bound := fun s u t has hsu hut htb => by
      rw [hdefect_eq]
      calc ‖(X t - X u) • (Y s - Y u)‖
          = ‖X t - X u‖ * ‖Y s - Y u‖ := norm_smul _ _
        _ = |X t - X u| * ‖Y s - Y u‖ := by rw [Real.norm_eq_abs]
        _ = |X t - X u| * ‖Y u - Y s‖ := by rw [norm_sub_rev]
        _ ≤ (C_X * |t - u| ^ γ) * (C_Y * |u - s| ^ δ) := by
            apply mul_le_mul
            · exact hX_hold u t (has.trans hsu) hut htb
            · exact hY_hold s u has hsu (hut.trans htb)
            · exact norm_nonneg _
            · exact mul_nonneg hC_X (rpow_nonneg (abs_nonneg _) _)
        _ = κ * |u - s| ^ δ * |t - u| ^ γ := by unfold κ; ring
    L₁_nonneg := zero_le_one
    L₂_nonneg := zero_le_one
    ω₂_nonneg := fun s t _ _ _ => abs_nonneg _
    ω₂_diag := fun s => by simp [ω]
    ω₂_superadd := hω_superadd
    ω₂_lip := hω_lip
  }
  -- The sewn map
  set I := sewingMap₂ Ξ ω ω δ γ κ 1 1 a b hcond
  refine ⟨I, ?_, ?_, ?_⟩
  -- (1) Diagonal: I(s, s) = 0
  · exact fun s has hsb => sewingMap₂_diag hcond has hsb
  -- (2) Additivity: I(s, t) = I(s, u) + I(u, t)
  · exact fun s u t has hsu hut htb => sewingMap₂_additive hcond has hsu hut htb
  -- (3) Approximation bound
  · refine ⟨κ * sewingConst₂ δ γ * (2 : ℝ)⁻¹ ^ (δ + γ), fun s t has' hst' htb' => ?_⟩
    have h := sewingMap₂_dist_le hcond has' hst' htb'
    -- h : ‖I s t - Ξ s t‖ ≤ κ * 1^δ * 1^γ * sewingConst₂ δ γ * 2⁻¹^(δ+γ) * |t-s|^(δ+γ)
    -- Goal: ‖I s t - (X t - X s) • Y s‖ ≤ C * |t-s|^(γ+δ)
    -- Ξ s t = (X t - X s) • Y s definitionally, and δ + γ = γ + δ
    calc ‖I s t - (X t - X s) • Y s‖
        ≤ κ * 1 ^ δ * 1 ^ γ * sewingConst₂ δ γ *
            (2 : ℝ)⁻¹ ^ (δ + γ) * |t - s| ^ (δ + γ) := h
      _ = κ * sewingConst₂ δ γ * (2 : ℝ)⁻¹ ^ (δ + γ) * |t - s| ^ (γ + δ) := by
          simp only [one_rpow, mul_one]
          congr 1; ring_nf

end YoungIntegration

end StochCalc
