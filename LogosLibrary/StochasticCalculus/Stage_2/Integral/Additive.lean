/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: Stage_2/Integral/Additive.lean
-/
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Properties
import LogosLibrary.StochasticCalculus.Stage_2.Integral.Defect
import LogosLibrary.StochasticCalculus.Stage_2.RoughPath.Defs

open NormedTensorSquare StochCalc.TruncTensor₂ StochCalc.GroupLike₂ Real
open StochCalc.RoughPath StochCalc.ControlledPath

noncomputable section

namespace StochCalc

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedTensorSquare V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {γ C a b : ℝ}
variable {X : RoughPath V γ C a b}

section Additivity

theorem roughIntegral_additive -- internal exception #3
    (P : RoughIntegralPairing E V F)
    (cY : ControlledPath E X)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    roughIntegral P cY s t =
      roughIntegral P cY s u + roughIntegral P cY u t := by
  set Ξ := roughApproxMap P cY
  have hSC₁ := roughApprox_sewingCondition₁ P cY
  have h3γ : 1 < 3 * γ := by linarith [X.hγ_lower]
  -- Build SewingCondition₃ with ω(s,t) = |t-s|, θ = 3γ
  have hSC₃ : SewingCondition₃ Ξ (fun s t => |t - s|) (3 * γ)
      (roughSewingConst P cY) a b := {
    vanish_diag := hSC₁.vanish_diag
    one_lt_theta := h3γ
    K_nonneg := roughSewingConst_nonneg P cY
    hab := X.hab
    omega_cont := contControl_of_lipControl (lipControl_abs_sub X.hab)
    defect_bound := hSC₁.defect_bound
    energy_summable := fun s' t' has' hst' htb' => by
      set r := sewingRatio₁ (3 * γ)
      have hr₀ : 0 ≤ r := (sewingRatio₁_pos h3γ).le
      have hr₁ : r < 1 := sewingRatio₁_lt_one h3γ
      suffices h : ∀ n, thetaEnergy (fun s t => |t - s|) (3 * γ)
          (dyadicPartition s' t' hst' n) = |t' - s'| ^ (3 * γ) * r ^ n by
        simp_rw [h]; exact (summable_geometric_of_lt_one hr₀ hr₁).mul_left _
      intro n
      rw [thetaEnergy_dyadicPartition]; simp_rw [abs_dyadicPt_sub]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_pow, Nat.cast_ofNat,
          dyadic_geometric_factor (abs_nonneg _) n]
      congr 1; simp only [r, sewingRatio₁]
      rw [← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ (3 * γ - 1)) n,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2⁻¹)]
      congr 1; ring
  }
  -- Identify roughIntegral with sewingMap₃ (both = limUnder of dyadicSum₁)
  have hst : s ≤ t := hsu.trans hut
  suffices heq : ∀ s' t', a ≤ s' → s' ≤ t' → t' ≤ b →
      roughIntegral P cY s' t' =
        sewingMap₃ Ξ (fun s t => |t - s|) (3 * γ)
          (roughSewingConst P cY) a b hSC₃ s' t' by
    rw [heq s t has hst htb, heq s u has hsu (hut.trans htb),
        heq u t (has.trans hsu) hut htb]
    exact sewingMap₃_additive hSC₃ has hsu hut htb
  -- Both definitions unfold to limUnder atTop (dyadicSum₁ Ξ · ·)
  intro s' t' has' hst' htb'
  have hcond : a ≤ s' ∧ s' ≤ t' ∧ t' ≤ b := ⟨has', hst', htb'⟩
  simp only [roughIntegral, sewingMap₁, sewingMap₃, dif_pos hcond]
  exact
    limUnder.congr_simp Filter.atTop Filter.atTop rfl
      (fun n => dyadicSum₁ (roughApproxMap P cY) s' t' n) (fun n => dyadicSum₁ Ξ s' t' n) rfl

end StochCalc.Additivity
