/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.CramerRao.Cross

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset Metric

open scoped Topology

namespace InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace RegularStatisticalModel

variable (M : RegularStatisticalModel n Ω)


/-! ### Cauchy–Schwarz: equality characterisation -/

/-- Equality in Cauchy–Schwarz holds iff `f` and `g` are
proportional in `L²(P_θ)`: there exist `α, β` not both zero
with `α f + β g = 0` a.e.

Equivalently (when `∫ g²p > 0`): `f = (B/C) · g` a.e.
where `B = ∫ fgp`, `C = ∫ g²p`. -/
theorem integral_mul_sq_eq_iff
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hg : Integrable (fun ω => g ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hfg : Integrable
      (fun ω => f ω * g ω * M.density θ ω)
      M.refMeasure)
    (hC_pos : 0 < ∫ ω, g ω ^ 2 * M.density θ ω
      ∂M.refMeasure) :
    (∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure) ^ 2 =
      (∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure) *
      (∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure) ↔
    ∃ c : ℝ, ∀ᵐ ω ∂M.refMeasure,
      f ω = c * g ω := by
  set A := ∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure
  set B := ∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure
  set C := ∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure
  constructor
  · -- Forward: B² = AC ⟹ f = (B/C)·g a.e.
    intro heq
    use B / C
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    -- Q(−B/C) = A − B²/C = 0
    have hQ_zero : ∫ ω, (f ω + (-B / C) * g ω) ^ 2 *
        M.density θ ω ∂M.refMeasure = 0 := by
      set t := -B / C
      set q₁ : Ω → ℝ := fun ω =>
        f ω ^ 2 * M.density θ ω
      set q₂ : Ω → ℝ := fun ω =>
        2 * t * (f ω * g ω * M.density θ ω)
      set q₃ : Ω → ℝ := fun ω =>
        t ^ 2 * (g ω ^ 2 * M.density θ ω)
      have hq₁ : Integrable q₁ M.refMeasure := hf
      have hq₂ : Integrable q₂ M.refMeasure :=
        hfg.const_mul _
      have hq₃ : Integrable q₃ M.refMeasure :=
        hg.const_mul _
      have h1 : ∫ ω, (f ω + t * g ω) ^ 2 *
          M.density θ ω ∂M.refMeasure =
          ∫ ω, (q₁ ω + q₂ ω + q₃ ω)
            ∂M.refMeasure :=
        integral_congr_ae
          (ae_of_all _ fun ω => by
            simp only [q₁, q₂, q₃]; ring)
      have h2 : ∫ ω, (q₁ ω + q₂ ω + q₃ ω)
          ∂M.refMeasure =
          ∫ ω, (q₁ ω + q₂ ω) ∂M.refMeasure +
          ∫ ω, q₃ ω ∂M.refMeasure :=
        integral_add (hq₁.add hq₂) hq₃
      have h3 : ∫ ω, (q₁ ω + q₂ ω) ∂M.refMeasure =
          ∫ ω, q₁ ω ∂M.refMeasure +
          ∫ ω, q₂ ω ∂M.refMeasure :=
        integral_add hq₁ hq₂
      rw [h1, h2, h3]
      simp only [q₁, q₂, q₃]
      have pull_mid : ∫ ω, 2 * t * (f ω * g ω * M.density θ ω) ∂M.refMeasure = 2 * t * B :=
        MeasureTheory.integral_const_mul (2 * t) _
      have pull_last : ∫ ω, t ^ 2 * (g ω ^ 2 * M.density θ ω) ∂M.refMeasure = t ^ 2 * C :=
        MeasureTheory.integral_const_mul (t ^ 2) _
      -- Goal: A + 2*t*B + t²*C = 0
      have key : A + 2 * t * B + t ^ 2 * C =
          (A * C - B ^ 2) / C := by
        simp only [t]; field_simp; ring
      rw [pull_mid, pull_last, key, heq, sub_self, zero_div]
    -- (f + tg)²p ≥ 0 pointwise and integrates to 0 ⟹ = 0 a.e.
    have hnn : ∀ ω, 0 ≤ (f ω + (-B / C) * g ω) ^ 2 *
        M.density θ ω :=
      fun ω => mul_nonneg (sq_nonneg _)
        (M.density_nonneg θ hθ ω)
    have h_ae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ hnn)
      (by -- integrability of (f + tg)²p
        have : ∀ ω, (f ω + (-B / C) * g ω) ^ 2 *
            M.density θ ω =
          f ω ^ 2 * M.density θ ω +
          (2 * (-B / C) * (f ω * g ω * M.density θ ω) +
           (-B / C) ^ 2 *
            (g ω ^ 2 * M.density θ ω)) :=
          fun ω => by ring
        simp_rw [this]
        exact hf.add
          ((hfg.const_mul _).add (hg.const_mul _)))).mp
      hQ_zero
    -- f + (−B/C)g = 0 a.e. ⟹ f = (B/C)g a.e.
    filter_upwards [h_ae,
      M.toStatisticalModel.density_pos_ae θ hθ]
      with ω hprod hpos
    have hp_ne : M.density θ ω ≠ 0 := ne_of_gt hpos
    have hsq : (f ω + (-B / C) * g ω) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd h hp_ne
    have hsum : f ω + -B / C * g ω = 0 :=
      mul_self_eq_zero.mp (by rw [sq] at hsq; exact hsq)
    linear_combination hsum
  · -- Backward: f = c·g a.e. ⟹ B² = AC
    intro ⟨c, hcg⟩
    have hB : B = c * C := by
      simp only [B, C]
      calc ∫ ω, f ω * g ω * M.density θ ω
            ∂M.refMeasure
          = ∫ ω, c * (g ω ^ 2 * M.density θ ω)
            ∂M.refMeasure :=
            integral_congr_ae
              (hcg.mono fun ω h => by simp; rw [h]; ring)
        _ = c * ∫ ω, g ω ^ 2 * M.density θ ω
            ∂M.refMeasure :=
            MeasureTheory.integral_const_mul c _
    have hA : A = c ^ 2 * C := by
      simp only [A, C]
      calc ∫ ω, f ω ^ 2 * M.density θ ω
            ∂M.refMeasure
          = ∫ ω, c ^ 2 * (g ω ^ 2 * M.density θ ω)
            ∂M.refMeasure :=
            integral_congr_ae
              (hcg.mono fun ω h => by simp; rw [h]; ring)
        _ = c ^ 2 * ∫ ω, g ω ^ 2 * M.density θ ω
            ∂M.refMeasure :=
            MeasureTheory.integral_const_mul (c ^ 2) _
    rw [hB, hA]; ring


/-! ### Cauchy–Schwarz for density-weighted integrals -/

/-- **Cauchy–Schwarz inequality** for density-weighted integrals:
  `(∫ f · g · p dμ)² ≤ (∫ f² · p dμ) · (∫ g² · p dμ)`

**Proof** (discriminant method).
For all `t ∈ ℝ`, `∫ (f + t g)² · p dμ ≥ 0` since the integrand is
pointwise nonneg.  Expanding gives `A + 2tB + t²C ≥ 0` where
`A = ∫ f²p`, `B = ∫ fgp`, `C = ∫ g²p`.  If `C > 0`, specialising
at `t = −B/C` yields `A − B²/C ≥ 0`, hence `B² ≤ AC`.  If `C = 0`,
then `g²p = 0` a.e.; since `p > 0` a.e. this gives `g = 0` a.e.,
hence `B = 0` and `B² = 0 ≤ AC = 0`. -/
theorem integral_mul_sq_le
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hg : Integrable (fun ω => g ω ^ 2 * M.density θ ω)
      M.refMeasure)
    (hfg : Integrable
      (fun ω => f ω * g ω * M.density θ ω)
      M.refMeasure) :
    (∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure) ^ 2 ≤
      (∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure) *
      (∫ ω, g ω ^ 2 * M.density θ ω
        ∂M.refMeasure) := by
  -- Abbreviations
  set A := ∫ ω, f ω ^ 2 * M.density θ ω ∂M.refMeasure
  set B := ∫ ω, f ω * g ω * M.density θ ω ∂M.refMeasure
  set C := ∫ ω, g ω ^ 2 * M.density θ ω ∂M.refMeasure
  -- Show: B² ≤ A · C
  -- Key fact: ∀ t, ∫ (f + t·g)² · p ≥ 0
  have hQ : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := by
    intro t
    have hint : 0 ≤ ∫ ω, (f ω + t * g ω) ^ 2 *
        M.density θ ω ∂M.refMeasure :=
      integral_nonneg (fun ω => mul_nonneg (sq_nonneg _)
        (M.density_nonneg θ hθ ω))
    -- ∫ (f+tg)²·p = A + 2tB + t²C
    have hexpand : ∫ ω, (f ω + t * g ω) ^ 2 *
          M.density θ ω ∂M.refMeasure =
          A + 2 * t * B + t ^ 2 * C := by
        have heq : ∀ ω, (f ω + t * g ω) ^ 2 *
            M.density θ ω =
          f ω ^ 2 * M.density θ ω +
          (2 * t * (f ω * g ω * M.density θ ω) +
           t ^ 2 * (g ω ^ 2 * M.density θ ω)) :=
          fun ω => by ring
        simp_rw [heq]
        have h1 : ∫ ω, f ω ^ 2 * M.density θ ω +
            (2 * t * (f ω * g ω * M.density θ ω) +
            t ^ 2 * (g ω ^ 2 * M.density θ ω))
            ∂M.refMeasure =
            ∫ ω, f ω ^ 2 * M.density θ ω
              ∂M.refMeasure +
            ∫ ω, (2 * t * (f ω * g ω * M.density θ ω) +
              t ^ 2 * (g ω ^ 2 * M.density θ ω))
              ∂M.refMeasure :=
          integral_add hf
            ((hfg.const_mul _).add (hg.const_mul _))
        have h2 : ∫ ω,
            (2 * t * (f ω * g ω * M.density θ ω) +
            t ^ 2 * (g ω ^ 2 * M.density θ ω))
            ∂M.refMeasure =
            ∫ ω, 2 * t * (f ω * g ω * M.density θ ω)
              ∂M.refMeasure +
            ∫ ω, t ^ 2 * (g ω ^ 2 * M.density θ ω)
              ∂M.refMeasure :=
          integral_add (hfg.const_mul _) (hg.const_mul _)
        rw [h1, h2]
        have pull1 : ∫ ω, 2 * t * (f ω * g ω * M.density θ ω) ∂M.refMeasure = 2 * t * B :=
          MeasureTheory.integral_const_mul (2 * t) _
        have pull2 : ∫ ω, t ^ 2 * (g ω ^ 2 * M.density θ ω) ∂M.refMeasure = t ^ 2 * C :=
          MeasureTheory.integral_const_mul (t ^ 2) _
        rw [pull1, pull2]
        ring
    linarith [hexpand ▸ hint]
  -- Case split on C
  by_cases hC : C = 0
  · -- Case C = 0: g²p = 0 a.e., so gp = 0 a.e., so B = 0
    have hg_sq_zero : ∀ᵐ ω ∂M.refMeasure,
        g ω ^ 2 * M.density θ ω = 0 := by
      have hnn : ∀ ω, 0 ≤ g ω ^ 2 * M.density θ ω :=
        fun ω => mul_nonneg (sq_nonneg _)
          (M.density_nonneg θ hθ ω)
      exact (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ hnn) hg).mp hC
    -- g = 0 a.e. (since p > 0 a.e.)
    have hg_zero : ∀ᵐ ω ∂M.refMeasure, g ω = 0 := by
      filter_upwards [hg_sq_zero,
        M.toStatisticalModel.density_pos_ae θ hθ]
        with ω hprod hpos
      have hp_ne : M.density θ ω ≠ 0 := ne_of_gt hpos
      have hsq : g ω ^ 2 = 0 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact h
        · exact absurd h hp_ne
      exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq
    -- B = ∫ f·g·p = ∫ f·0·p = 0
    have hB : B = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hg_zero] with ω hω
      simp [hω]
    rw [hB, hC]; ring_nf; rfl
  · -- Case C > 0
    have hC_pos : 0 < C := lt_of_le_of_ne
      (integral_nonneg fun ω =>
        mul_nonneg (sq_nonneg (g ω)) (M.density_nonneg θ hθ ω))
      (Ne.symm hC)
    -- Specialise Q at t = −B/C
    -- A + 2·(−B/C)·B + (−B/C)²·C ≥ 0
    -- = A − 2B²/C + B²/C = A − B²/C ≥ 0
    -- Hence A·C ≥ B²
    suffices h : B ^ 2 ≤ A * C by linarith
    rw [← sub_nonneg]
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have h_eq : A * C - B ^ 2 =
        C * (A + 2 * (-B / C) * B +
          (-B / C) ^ 2 * C) := by
      field_simp; ring
    linarith [mul_nonneg (le_of_lt hC_pos) (hQ (-B / C))]

end RegularStatisticalModel
end InformationGeometry
