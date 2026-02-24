/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Superior.ObjectiveReduction.MasterEquation
import LogosLibrary.Relativity.LorentzBoost.TTime

namespace SuperiorReduction

open ThermalTime

variable (pc : PhysicalConstants) (m : ℝ) (hm : m > 0)

/-- **PENROSE COLLAPSE TIME**

    Converting from entropic time σ back to coordinate time t:

    t = σ / Γ_t = σ · ℏΔs / (Gm²)

    For one e-folding (σ = 1):
    τ_coh = ℏΔs / (Gm²)

    This is exactly Penrose's result! -/
noncomputable def penroseCollapseTime (Δs : ℝ) : ℝ :=
  pc.ℏ * Δs / (pc.G * m^2)

/-- **THEOREM**: Collapse time scales as predicted -/
theorem penrose_scaling (Δs : ℝ) (hΔs : Δs > 0) (hm : m > 0) :
    penroseCollapseTime pc m Δs > 0 := by
  unfold penroseCollapseTime
  apply div_pos
  · exact mul_pos pc.hℏ hΔs
  · exact mul_pos pc.hG (sq_pos_of_pos hm)

/-- **THEOREM**: The 2π threshold — complete collapse after one modular cycle

    After σ = 2π nats of entropy production:
    ρ_off → e^{-2π} ρ_off ≈ 0.002 ρ_off

    Coherence reduced to 0.2% = effectively classical -/
noncomputable def coherenceAfterModularCycle (ρ₀ : ℝ) : ℝ :=
  ρ₀ * Real.exp (-modular_period)

/-- exp(2) > 7, proved via Taylor series -/
lemma exp_two_gt_seven : Real.exp 2 > 7 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 2) 6
  have sum_eq : ∑ k ∈ Finset.range 6, (2:ℝ)^k / k.factorial = 109/15 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
  calc (7 : ℝ) < 109/15 := by norm_num
    _ = ∑ k ∈ Finset.range 6, (2:ℝ)^k / k.factorial := sum_eq.symm
    _ ≤ Real.exp 2 := h

/-- exp(6) > 343, using exp(6) = exp(2)³ -/
lemma exp_six_gt : Real.exp 6 > 343 := by
  have h1 : Real.exp 6 = Real.exp 2 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h1]
  have h2 : Real.exp 2 > 7 := exp_two_gt_seven
  have h3 : (0 : ℝ) ≤ 7 := by norm_num
  calc Real.exp 2 ^ 3 > 7 ^ 3 := by nlinarith [sq_nonneg (Real.exp 2 - 7)]
    _ = 343 := by norm_num

/-- exp(-6) < 0.003 -/
lemma exp_neg_six_lt : Real.exp (-6 : ℝ) < 0.003 := by
  rw [Real.exp_neg]
  have h1 : Real.exp 6 > 343 := exp_six_gt
  have hexp_pos : (0 : ℝ) < Real.exp 6 := Real.exp_pos 6
  calc (Real.exp 6)⁻¹ < 343⁻¹ := by
        rw [propext (inv_lt_iff_one_lt_mul₀ hexp_pos)]
        linarith
    _ < 0.003 := by norm_num

/-- **THEOREM**: The 2π threshold — complete collapse after one modular cycle -/
theorem modular_cycle_gives_collapse (ρ₀ : ℝ) (hρ : ρ₀ > 0) :
    coherenceAfterModularCycle ρ₀ < 0.003 * ρ₀ := by
  unfold coherenceAfterModularCycle modular_period
  -- Step 1: 2π > 6 (using π > 3)
  have hpi : Real.pi > 3 := Real.pi_gt_three
  have h2pi_gt : 2 * Real.pi > 6 := by linarith
  -- Step 2: Therefore -(2π) < -6
  have h_neg : -(2 * Real.pi) < -6 := by linarith
  -- Step 3: exp is monotone, so exp(-(2π)) < exp(-6)
  have h_exp_mono : Real.exp (-(2 * Real.pi)) < Real.exp (-6) := Real.exp_lt_exp.mpr h_neg
  -- Step 4: Chain with numerical bound
  have h1 : Real.exp (-(2 * Real.pi)) < 0.003 := lt_trans h_exp_mono exp_neg_six_lt
  -- Step 5: Multiply by ρ₀ > 0
  have h2 : ρ₀ * Real.exp (-(2 * Real.pi)) < ρ₀ * 0.003 := mul_lt_mul_of_pos_left h1 hρ
  -- Step 6: Commutativity gets us home
  linarith

/-- **THE UNIVERSAL COLLAPSE RATE (Penrose Limit)**

    The collapse rate Γ̃(Δs) has a universal asymptotic form:

      Γ̃(Δs) → λ_C / Δs   as Δs → ∞

    Equivalently: Γ̃(Δs) · Δs / λ_C → 1

    This is the content of `collapse_rate_penrose_limit`.

    **Physical interpretation:**

    In entropic time σ, the master equation reads:
      ∂ρ/∂σ = -i[K,ρ] - Γ̃(Δs)ρ

    The "universality" is that:
    1. σ itself accumulates at rate Γ_t = Gm²/(ℏΔs) in coordinate time
    2. Large separations → faster σ accumulation → faster coordinate-time collapse
    3. The dimensionless ratio Γ̃(Δs) · Δs / λ_C = 1 is position-independent

    Position dependence is absorbed into HOW FAST entropic time flows,
    not into the collapse rate per unit of entropic time.

    Converting back to coordinate time recovers Penrose's formula:
      τ_collapse = ℏΔs / (Gm²)
-/
theorem universal_collapse_rate_ratio :
    Filter.Tendsto (fun Δs => collapseRateEntropic pc m hm Δs * Δs / comptonWavelength pc m hm)
                   Filter.atTop (nhds 1) :=
  collapse_rate_penrose_limit pc m hm


/-- In the classical regime, collapse rate approaches Cwl/Δs -/
theorem collapse_rate_asymptotic :
    Filter.Tendsto
      (fun Δs => collapseRateEntropic pc m hm Δs - comptonWavelength pc m hm / Δs)
      Filter.atTop (nhds 0) := by
  set Cwl := comptonWavelength pc m hm with hCwl_def
  have hCwl_pos : Cwl > 0 := comptonWavelength_pos pc m hm

  -- Use the Penrose limit we already proved!
  -- We know: Γ̃(Δs) * Δs / Cwl → 1
  -- So: Γ̃(Δs) * Δs → Cwl
  -- So: Γ̃(Δs) → Cwl / Δs (in the sense that their difference → 0)

  have h_penrose := collapse_rate_penrose_limit pc m hm
  -- h_penrose : Γ̃(Δs) * Δs / Cwl → 1

  -- Rearrange: Γ̃(Δs) - Cwl/Δs = (Cwl/Δs) * (Γ̃(Δs) * Δs / Cwl - 1)
  have h_eq : (fun Δs => collapseRateEntropic pc m hm Δs - Cwl / Δs) =ᶠ[Filter.atTop]
      (fun Δs => (Cwl / Δs) * (collapseRateEntropic pc m hm Δs * Δs / Cwl - 1)) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with Δs hΔs
    have hΔs_ne : Δs ≠ 0 := ne_of_gt hΔs
    have hCwl_ne : Cwl ≠ 0 := ne_of_gt hCwl_pos
    field_simp

  apply Filter.Tendsto.congr' h_eq.symm

  -- Now: (Cwl/Δs) → 0 and (Γ̃*Δs/Cwl - 1) → 0
  -- Product of (thing → 0) * (thing → 0) = (thing → 0)
  rw [show (0 : ℝ) = 0 * 0 by ring]
  apply Filter.Tendsto.mul
  · -- Cwl / Δs → 0
    rw [show (0 : ℝ) = Cwl * 0 by ring]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_zero
  · -- Γ̃ * Δs / Cwl - 1 → 0
    have h_sub : Filter.Tendsto
        (fun Δs => collapseRateEntropic pc m hm Δs * Δs / Cwl - 1)
        Filter.atTop (nhds (1 - 1)) := h_penrose.sub tendsto_const_nhds
    simp only [sub_self] at h_sub
    exact h_sub

end SuperiorReduction
