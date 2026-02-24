/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace SuperiorReduction

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
theorem gravitational_compton_ratio (m : ℝ) (hm : m > 0) :
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

end SuperiorReduction
