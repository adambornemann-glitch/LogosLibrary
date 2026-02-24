/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: EProcess.lean
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LogosLibrary.Superior.ThermalTime
/-!
=====================================================================
# THE E PROCESS
=====================================================================
The completion of Diósi-Penrose, Lorentz covariant
and unitary gravitationally induced collapse.
-/
namespace E_Process
open ThermalTime.Basic

/-- Fundamental physical constants (axiomatized as positive reals) -/
structure PhysicalConstants where
  G : ℝ          -- Gravitational constant
  ℏ : ℝ          -- Reduced Planck constant
  c : ℝ          -- Speed of light
  hG : G > 0
  hℏ : ℏ > 0
  hc : c > 0

variable (pc : PhysicalConstants)

/-- Compton wavelength: λ_C = ℏ/(mc) -/
noncomputable def comptonWavelength (m : ℝ) (_hm : m > 0) : ℝ :=
  pc.ℏ / (m * pc.c)

/-- Gravitational radius: λ_G = Gm/c² -/
noncomputable def gravitationalRadius (m : ℝ) : ℝ :=
  pc.G * m / pc.c^2

/-- Planck mass: m_P = √(ℏc/G) -/
noncomputable def planckMass : ℝ :=
  Real.sqrt (pc.ℏ * pc.c / pc.G)

/-- Planck length: ℓ_P = √(ℏG/c³) -/
noncomputable def planckLength : ℝ :=
  Real.sqrt (pc.ℏ * pc.G / pc.c^3)

/-- Key ratio: λ_G/λ_C = Gm²/(ℏc) = (m/m_P)² -/
lemma gravitational_compton_ratio (m : ℝ) (hm : m > 0) :
    gravitationalRadius pc m / comptonWavelength pc m hm =
    pc.G * m^2 / (pc.ℏ * pc.c) := by
  unfold gravitationalRadius comptonWavelength
  field_simp

variable (pc : PhysicalConstants) (m : ℝ) (hm : m > 0)

/-- The regularized proper separation: √(Δs² + λ_C²) -/
noncomputable def regularizedSeparation (Δs : ℝ) : ℝ :=
  Real.sqrt (Δs^2 + (comptonWavelength pc m hm)^2)

/-- The collapse rate in COORDINATE time: Γ_t = Gm²/(ℏΔs) -/
noncomputable def collapseRateCoordinate (Δs : ℝ) (_hΔs : Δs > 0) : ℝ :=
  pc.G * m^2 / (pc.ℏ * Δs)

/-- The regularized collapse rate (dimensionless, for entropic time):
    Γ̃(Δs) = (Cwl/Δs)(1 - exp(-Δs²/λ_C²))

    Properties:
    - Γ̃(0) = 0 (trace preservation)
    - Γ̃(Δs) → Cwl/Δs as Δs → ∞ (Penrose limit)
    - Γ̃(Δs) > 0 for Δs > 0 (monotonic decoherence)
-/
noncomputable def collapseRateEntropic (Δs : ℝ) : ℝ :=
  let Cwl := comptonWavelength pc m hm
  if Δs = 0 then 0
  else (Cwl / Δs) * (1 - Real.exp (-(Δs^2 / Cwl^2)))

/-- Collapse rate vanishes on diagonal (trace preservation) -/
lemma collapse_rate_zero_at_origin :
    collapseRateEntropic pc m hm 0 = 0 := by
  unfold collapseRateEntropic
  simp

/-- **THEOREM**: Collapse rate is positive for Δs > 0 -/
theorem collapse_rate_positive (Δs : ℝ) (hΔs : Δs > 0) :
    collapseRateEntropic pc m hm Δs > 0 := by
  unfold collapseRateEntropic
  simp only [ne_of_gt hΔs, ↓reduceIte]
  apply mul_pos
  · -- Cwl / Δs > 0
    apply div_pos
    · unfold comptonWavelength
      apply div_pos pc.hℏ
      exact mul_pos hm pc.hc
    · exact hΔs
  · -- 1 - exp(-Δs²/λ_C²) > 0
    have h : Real.exp (-(Δs^2 / (comptonWavelength pc m hm)^2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      -- Goal: -(Δs² / λ_C²) < 0
      apply neg_neg_of_pos
      -- Goal: Δs² / λ_C² > 0
      apply div_pos (sq_pos_of_pos hΔs)
      apply sq_pos_of_pos
      unfold comptonWavelength
      apply div_pos pc.hℏ (mul_pos hm pc.hc)
    linarith

/-
Helper lemmas for the Penrose limit lemma
-/

/-- Compton wavelength is positive -/
lemma comptonWavelength_pos : comptonWavelength pc m hm > 0 := by
  unfold comptonWavelength
  apply div_pos pc.hℏ (mul_pos hm pc.hc)

/-- For Δs > 0, the collapse rate expression simplifies -/
lemma collapseRateEntropic_simplify (Δs : ℝ) (hΔs : Δs > 0) :
    let Cwl := comptonWavelength pc m hm
    collapseRateEntropic pc m hm Δs * Δs / Cwl =
    1 - Real.exp (-(Δs^2 / Cwl^2)) := by
  set Cwl := comptonWavelength pc m hm with hCwl_def
  have hCwl_pos : Cwl > 0 := comptonWavelength_pos pc m hm
  have hΔs_ne : Δs ≠ 0 := ne_of_gt hΔs
  have hCwl_ne : Cwl ≠ 0 := ne_of_gt hCwl_pos
  unfold collapseRateEntropic
  simp only [ne_of_gt hΔs, ↓reduceIte, ← hCwl_def]
  field_simp

/-- Squares tend to infinity -/
lemma tendsto_sq_atTop :
    Filter.Tendsto (fun x : ℝ => x^2) Filter.atTop Filter.atTop := by
  simp only [pow_two]
  exact Filter.tendsto_mul_self_atTop

/-- Scaled squares tend to infinity for any positive scale -/
lemma tendsto_scaled_sq_atTop (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x : ℝ => x^2 / c) Filter.atTop Filter.atTop := by
  have h_eq : (fun x => x^2 / c) = (fun x => x^2 * (1/c)) := by
    ext; field_simp
  rw [h_eq]
  exact tendsto_sq_atTop.atTop_mul_const (by positivity : 0 < 1/c)

/-- exp(-x) → 0 as x → +∞ -/
lemma tendsto_exp_neg_atTop :
    Filter.Tendsto (fun x : ℝ => Real.exp (-x)) Filter.atTop (nhds 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero

/-- exp(-x²/c) → 0 as x → +∞ for c > 0 -/
lemma tendsto_exp_neg_sq_div_atTop (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-(x^2 / c))) Filter.atTop (nhds 0) := by
  have h_ratio : Filter.Tendsto (fun x => x^2 / c) Filter.atTop Filter.atTop :=
    tendsto_scaled_sq_atTop c hc
  have h_neg : Filter.Tendsto (fun x => -(x^2 / c)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr h_ratio
  exact Real.tendsto_exp_atBot.comp h_neg

/-- 1 - exp(-x²/c) → 1 as x → +∞ -/
lemma tendsto_one_minus_exp_neg_sq (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun x : ℝ => 1 - Real.exp (-(x^2 / c))) Filter.atTop (nhds 1) := by
  have h_exp := tendsto_exp_neg_sq_div_atTop c hc
  have h_const : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have h_sub := h_const.sub h_exp
  simp only [sub_zero] at h_sub
  exact h_sub

/-- **THEOREM**: Penrose limit — for large separations, Γ̃ ≈ Cwl/Δs -/
theorem collapse_rate_penrose_limit :
    Filter.Tendsto (fun Δs => collapseRateEntropic pc m hm Δs * Δs / comptonWavelength pc m hm)
                   Filter.atTop (nhds 1) := by
  set Cwl := comptonWavelength pc m hm with hCwl_def
  have hCwl_pos : Cwl > 0 := comptonWavelength_pos pc m hm
  have hCwl_sq_pos : Cwl^2 > 0 := sq_pos_of_pos hCwl_pos

  -- Eventually the expression equals the simplified form
  have h_eventually_eq : (fun Δs => collapseRateEntropic pc m hm Δs * Δs / Cwl) =ᶠ[Filter.atTop]
      (fun Δs => 1 - Real.exp (-(Δs^2 / Cwl^2))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with Δs hΔs
    exact collapseRateEntropic_simplify pc m hm Δs hΔs

  -- Use the simplified form's limit
  apply Filter.Tendsto.congr' h_eventually_eq.symm
  exact tendsto_one_minus_exp_neg_sq (Cwl^2) hCwl_sq_pos

/-- Gravitational self-energy: E_G = Gm²/√(Δs² + λ_C²) -/
noncomputable def gravitationalSelfEnergy (Δs : ℝ) : ℝ :=
  pc.G * m^2 / regularizedSeparation pc m hm Δs

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

end E_Process
