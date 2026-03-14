/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/Linear.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Regular
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Unique
noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Linearity -/

section Linearity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Scalar-smul preserves Hölder regularity. -/
theorem IsHolderOn.smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y : ℝ → F} {δ C_Y a b : ℝ} (hY : IsHolderOn Y δ C_Y a b) (c : ℝ) :
    IsHolderOn (c • Y) δ (|c| * C_Y) a b where
  γ_pos := hY.γ_pos
  γ_le_one := hY.γ_le_one
  C_nonneg := mul_nonneg (abs_nonneg c) hY.C_nonneg
  hab := hY.hab
  holder_bound := fun s t has hst htb => by
    simp only [Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hY.holder_bound s t has hst htb) (abs_nonneg c)

/-- **Linearity in the integrand**: `∫ (c • Y) dX = c • ∫ Y dX`.

Proof: `c • I` is additive and approximates `c • Ξ = Ξ_{c•Y}`,
so by uniqueness it equals the Young integral of `c • Y` against `X`. -/
theorem youngIntegral_smul_integrand
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    (c : ℝ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    youngIntegral X (c • Y) γ δ C_X (|c| * C_Y) a b
      hX (hY.smul c) hγδ s t =
    c • youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t := by
  intro s t has hst htb
  symm
  refine (youngIntegral_unique
    (J := fun s t => c • youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t)
    (M := |c| * (sewingConst₂ δ γ * (C_X * C_Y)))
    (θ := γ + δ)
    hX (hY.smul c) hγδ ?_ ?_ ?_ ?_ ?_ s t has hst htb)
  -- Goal 1: ∀ s', (c • I_Y)(s', s') = 0
  · intro s'
    by_cases h : a ≤ s' ∧ s' ≤ b
    · simp only [smul_eq_zero]
      rw [← youngIntegral_diag hX hY hγδ h.1 h.2]
      exact Or.inr rfl
    · simp only [youngIntegral, sewingMap₂]
      rw [dif_neg (fun ⟨h1, _, h3⟩ => h ⟨h1, h3⟩), smul_zero]
  -- Goal 2: additivity of c • I_Y
  · intro s' u' t' has' hsu' hut' htb'
    simp only
    rw [youngIntegral_additive hX hY hγδ has' hsu' hut' htb', smul_add]
  -- Goal 3: 0 ≤ M
  · exact mul_nonneg (abs_nonneg c)
      (mul_nonneg (sewingConst₂_pos (by linarith)).le
        (mul_nonneg hX.C_nonneg hY.C_nonneg))
  -- Goal 4: 1 < θ
  · exact hγδ
  -- Goal 5: ‖c • I(s',t') - (X t' - X s') • (c • Y)(s')‖ ≤ M * |t'-s'|^θ
  · intro s' t' has' hst' htb'
    simp only [Pi.smul_apply]
    rw [smul_comm (X t' - X s') c (Y s'), ← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |c| * ‖youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s' t' -
              (X t' - X s') • Y s'‖
        ≤ |c| * (sewingConst₂ δ γ * (C_X * C_Y) * |t' - s'| ^ (γ + δ)) :=
          mul_le_mul_of_nonneg_left
            (youngIntegral_approx hX hY hγδ has' hst' htb') (abs_nonneg c)
      _ = |c| * (sewingConst₂ δ γ * (C_X * C_Y)) * |t' - s'| ^ (γ + δ) :=
          by ring


/-- Sum of Hölder functions is Hölder. -/
theorem IsHolderOn.add_real {X₁ X₂ : ℝ → ℝ} {γ C₁ C₂ a b : ℝ}
    (h₁ : IsHolderOn X₁ γ C₁ a b) (h₂ : IsHolderOn X₂ γ C₂ a b) :
    IsHolderOn (X₁ + X₂) γ (C₁ + C₂) a b where
  γ_pos := h₁.γ_pos
  γ_le_one := h₁.γ_le_one
  C_nonneg := add_nonneg h₁.C_nonneg h₂.C_nonneg
  hab := h₁.hab
  holder_bound := fun s t has hst htb => by
    simp only [Pi.add_apply]
    calc ‖X₁ t + X₂ t - (X₁ s + X₂ s)‖
        = ‖(X₁ t - X₁ s) + (X₂ t - X₂ s)‖ := by congr 1; ring
      _ ≤ ‖X₁ t - X₁ s‖ + ‖X₂ t - X₂ s‖ := norm_add_le _ _
      _ ≤ C₁ * |t - s| ^ γ + C₂ * |t - s| ^ γ :=
          add_le_add (h₁.holder_bound s t has hst htb) (h₂.holder_bound s t has hst htb)
      _ = (C₁ + C₂) * |t - s| ^ γ := by ring

/-- **Linearity in the integrator**: `∫ Y d(X₁ + X₂) = ∫ Y dX₁ + ∫ Y dX₂`.

Same strategy: the sum is additive and approximates the sum of Ξ-maps. -/
theorem youngIntegral_add_integrator
    {X₁ X₂ : ℝ → ℝ} {Y : ℝ → E} {γ δ C₁ C₂ C_Y a b : ℝ}
    (hX₁ : IsHolderOn X₁ γ C₁ a b)
    (hX₂ : IsHolderOn X₂ γ C₂ a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    youngIntegral (X₁ + X₂) Y γ δ (C₁ + C₂) C_Y a b
      (hX₁.add_real hX₂) hY hγδ s t =
    youngIntegral X₁ Y γ δ C₁ C_Y a b hX₁ hY hγδ s t +
    youngIntegral X₂ Y γ δ C₂ C_Y a b hX₂ hY hγδ s t := by
  intro s t has hst htb
  symm
  refine (youngIntegral_unique
    (J := fun s t =>
      youngIntegral X₁ Y γ δ C₁ C_Y a b hX₁ hY hγδ s t +
      youngIntegral X₂ Y γ δ C₂ C_Y a b hX₂ hY hγδ s t)
    (M := sewingConst₂ δ γ * ((C₁ + C₂) * C_Y))
    (θ := γ + δ)
    (hX₁.add_real hX₂) hY hγδ
    ?_ ?_ ?_ ?_ ?_ s t has hst htb)
  -- J(s,s) = 0: each integral vanishes on the diagonal
  · intro s'
    have diag_zero : ∀ (X : ℝ → ℝ) (C : ℝ) (hX : IsHolderOn X γ C a b),
        youngIntegral X Y γ δ C C_Y a b hX hY hγδ s' s' = 0 := by
      intro X C hX
      simp only [youngIntegral, sewingMap₂]
      split_ifs with h
      · have : ∀ n, dyadicSum₁ (youngApprox X Y) s' s' n = 0 := by
          intro n; simp [dyadicSum₁, dyadicPt, youngApprox]
        simp_rw [this]; exact tendsto_const_nhds.limUnder_eq
      · rfl
    rw [← diag_zero X₁ C₁ hX₁]
    simp only [add_eq_left]
    rw [diag_zero X₂ C₂ hX₂]
  -- J additive
  · intro s' u' t' has' hsu' hut' htb'
    simp only
    rw [youngIntegral_additive hX₁ hY hγδ has' hsu' hut' htb',
        youngIntegral_additive hX₂ hY hγδ has' hsu' hut' htb']
    abel
  -- 0 ≤ M
  · exact mul_nonneg (sewingConst₂_pos (by linarith)).le
      (mul_nonneg (add_nonneg hX₁.C_nonneg hX₂.C_nonneg) hY.C_nonneg)
  -- 1 < θ
  · exact hγδ
  -- Bound: ‖J(s',t') - Ξ_{X₁+X₂}(s',t')‖ ≤ M * |t'-s'|^{γ+δ}
  · intro s' t' has' hst' htb'
    -- Split Ξ_{X₁+X₂} = Ξ_{X₁} + Ξ_{X₂}
    simp only [Pi.add_apply]
    rw [show X₁ t' + X₂ t' - (X₁ s' + X₂ s') =
        (X₁ t' - X₁ s') + (X₂ t' - X₂ s') from by ring, add_smul]
    -- Rearrange: (I₁ + I₂) - (Ξ₁ + Ξ₂) = (I₁ - Ξ₁) + (I₂ - Ξ₂)
    set I₁ := youngIntegral X₁ Y γ δ C₁ C_Y a b hX₁ hY hγδ s' t'
    set I₂ := youngIntegral X₂ Y γ δ C₂ C_Y a b hX₂ hY hγδ s' t'
    rw [show I₁ + I₂ - ((X₁ t' - X₁ s') • Y s' + (X₂ t' - X₂ s') • Y s') =
        (I₁ - (X₁ t' - X₁ s') • Y s') + (I₂ - (X₂ t' - X₂ s') • Y s') from by abel]
    calc ‖(I₁ - (X₁ t' - X₁ s') • Y s') + (I₂ - (X₂ t' - X₂ s') • Y s')‖
        ≤ ‖I₁ - (X₁ t' - X₁ s') • Y s'‖ + ‖I₂ - (X₂ t' - X₂ s') • Y s'‖ :=
          norm_add_le _ _
      _ ≤ sewingConst₂ δ γ * (C₁ * C_Y) * |t' - s'| ^ (γ + δ) +
          sewingConst₂ δ γ * (C₂ * C_Y) * |t' - s'| ^ (γ + δ) :=
          add_le_add (youngIntegral_approx hX₁ hY hγδ has' hst' htb')
                     (youngIntegral_approx hX₂ hY hγδ has' hst' htb')
      _ = sewingConst₂ δ γ * ((C₁ + C₂) * C_Y) * |t' - s'| ^ (γ + δ) := by ring


end Linearity

end StochCalc
