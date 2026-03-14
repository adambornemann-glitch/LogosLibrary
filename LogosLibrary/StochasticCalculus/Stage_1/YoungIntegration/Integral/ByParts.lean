/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Integral/ByParts.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.Integral.Linear

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### Integration by parts (sketch) -/

section IntegrationByParts

/-- **Integration by parts for Young integrals** (scalar case):

  `∫_s^t Y dX + ∫_s^t X dY = X(t)·Y(t) - X(s)·Y(s)`

Proof: Define `J(s,t) = X(t)Y(t) - X(s)Y(s) - ∫ Y dX`. Then:
1. `J` is additive (product is telescoping, integral is additive).
2. `J(s,t) - (Y(t)-Y(s))·X(s) = (X(t)-X(s))·(Y(t)-Y(s)) - (∫YdX - Ξ_{YdX})`,
   so `‖J - Ξ_{XdY}‖ ≤ (1 + sewingConst₂) · C_X · C_Y · |t-s|^{γ+δ}`.
3. By uniqueness, `J = ∫ X dY`. Rearranging gives the result. -/
theorem youngIntegral_by_parts
    {X Y : ℝ → ℝ} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b)
    (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ)
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ s t +
    youngIntegral Y X δ γ C_Y C_X a b hY hX (by linarith) s t =
      X t * Y t - X s * Y s := by
  set I_YdX := youngIntegral X Y γ δ C_X C_Y a b hX hY hγδ
  set I_XdY := youngIntegral Y X δ γ C_Y C_X a b hY hX (by linarith)
  -- Suffices: I_XdY = X·Y - X·Y - I_YdX
  suffices h : I_XdY s t = X t * Y t - X s * Y s - I_YdX s t by linarith
  symm
  exact youngIntegral_unique hY hX (by linarith : 1 < δ + γ)
    (J := fun s t => X t * Y t - X s * Y s - I_YdX s t)
    (M := (1 + sewingConst₂ δ γ) * C_X * C_Y)
    (θ := γ + δ)
    -- Diagonal: J(s',s') = 0
    (fun s' => by
      simp only [I_YdX, youngIntegral, sewingMap₂]
      split_ifs with h
      · have : ∀ n, dyadicSum₁ (youngApprox X Y) s' s' n = 0 := by
          intro n; simp [dyadicSum₁, dyadicPt, youngApprox]
        simp_rw [this]; rw [tendsto_const_nhds.limUnder_eq]; ring
      · ring)
    -- Additivity: J(s',t') = J(s',u') + J(u',t')
    (fun s' u' t' has' hsu' hut' htb' => by
      have : I_YdX s' t' = I_YdX s' u' + I_YdX u' t' :=
        youngIntegral_additive hX hY hγδ has' hsu' hut' htb'
      linarith)
    -- M ≥ 0
    (mul_nonneg (mul_nonneg
      (by linarith [sewingConst₂_pos (show 1 < δ + γ by linarith)])
      hX.C_nonneg) hY.C_nonneg)
    -- θ > 1
    (by linarith)
    -- Bound: ‖J(s',t') - (Y(t')-Y(s'))·X(s')‖ ≤ M · |t'-s'|^{γ+δ}
    (fun s' t' has' hst' htb' => by
      rw [smul_eq_mul]
      -- Algebraic rearrangement:
      -- J - Ξ_{XdY} = (X(t')-X(s'))·(Y(t')-Y(s')) - (I_YdX - (X(t')-X(s'))·Y(s'))
      rw [show X t' * Y t' - X s' * Y s' - I_YdX s' t' - (Y t' - Y s') * X s' =
        (X t' - X s') * (Y t' - Y s') -
        (I_YdX s' t' - (X t' - X s') * Y s') from by ring]
      calc ‖(X t' - X s') * (Y t' - Y s') -
              (I_YdX s' t' - (X t' - X s') * Y s')‖
          ≤ ‖(X t' - X s') * (Y t' - Y s')‖ +
            ‖I_YdX s' t' - (X t' - X s') * Y s'‖ := norm_sub_le _ _
        _ ≤ C_X * C_Y * |t' - s'| ^ (γ + δ) +
            sewingConst₂ δ γ * (C_X * C_Y) * |t' - s'| ^ (γ + δ) := by
            apply add_le_add
            · -- Cross term: |ΔX·ΔY| ≤ C_X·C_Y·|t'-s'|^{γ+δ}
              rw [Real.norm_eq_abs, abs_mul]
              calc |X t' - X s'| * |Y t' - Y s'|
                  ≤ (C_X * |t' - s'| ^ γ) * (C_Y * |t' - s'| ^ δ) :=
                    mul_le_mul
                      (hX.holder_bound s' t' has' hst' htb')
                      (hY.holder_bound s' t' has' hst' htb')
                      (abs_nonneg _)
                      (mul_nonneg hX.C_nonneg (rpow_nonneg (abs_nonneg _) _))
                _ = C_X * C_Y * (|t' - s'| ^ γ * |t' - s'| ^ δ) := by ring
                _ = C_X * C_Y * |t' - s'| ^ (γ + δ) := by
                    congr 1
                    exact (rpow_add' (abs_nonneg _)
                      (by linarith : γ + δ ≠ 0)).symm
            · -- Young–Loève estimate: ‖I - Ξ‖ ≤ sewingConst₂·C_X·C_Y·|Δt|^{γ+δ}
              exact youngIntegral_approx hX hY hγδ has' hst' htb'
        _ = (1 + sewingConst₂ δ γ) * C_X * C_Y * |t' - s'| ^ (γ + δ) := by ring)
    s t has hst htb

end IntegrationByParts

end StochCalc
