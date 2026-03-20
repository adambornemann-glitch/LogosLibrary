/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/Bridge.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.ArctanPrim

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set Function

/-! ## §3: Poisson–Fourier bridge

The Poisson integral of a measure can be expressed via its characteristic function.
This is the step where Fubini connects the spatial and frequency representations. -/

/-- P_ε(ξ) = (1/(2π)) · Re(∫ e^{-ε|t|} e^{iξt} dt). Immediate from `fourier_two_sided_exp`. -/
private lemma poissonKernel_eq_half_fourier {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    poissonKernel ε ξ = (1 / (2 * Real.pi)) *
      (∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)).re := by
  rw [fourier_two_sided_exp hε ξ, Complex.ofReal_re]
  unfold poissonKernel; field_simp

/-- Conjugation trick: Re(e^{-ε|t|} · e^{ist} · ∫ e^{-iωt} dμ) equals
    Re(e^{-ist} · e^{-ε|t|} · ∫ e^{iωt} dμ), via Re(z) = Re(conj z). -/
private lemma re_conjugate_trick (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε s t : ℝ} :
    (cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
      ∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ).re =
    (cexp (-(I * ↑s * ↑t)) * cexp (-(↑ε * ↑|t|)) *
      ∫ ω, cexp (I * ↑ω * ↑t) ∂μ).re := by
  -- conj(e^{-ε|t|}) = e^{-ε|t|}  (real exponent is fixed by conjugation)
  have h_real : starRingEnd ℂ (cexp (-(↑ε * ↑|t|))) = cexp (-(↑ε * ↑|t|)) := by
    rw [← Complex.exp_conj]; congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal]
  -- conj(e^{ist}) = e^{-ist}  (conj flips I to -I)
  have h_imag : starRingEnd ℂ (cexp (I * ↑s * ↑t)) = cexp (-(I * ↑s * ↑t)) := by
    rw [← Complex.exp_conj]; congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  -- conj(∫ e^{-iωt} dμ) = ∫ e^{iωt} dμ  (conj commutes with Bochner integral)
  have h_int : starRingEnd ℂ (∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ) =
      ∫ ω, cexp (I * ↑ω * ↑t) ∂μ := by
    trans ∫ ω, starRingEnd ℂ (cexp (-(I * ↑ω * ↑t))) ∂μ
    · exact Eq.symm integral_conj
    · congr 1; ext ω
      rw [← Complex.exp_conj]; congr 1
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  -- Re(z) = Re(conj z), distribute conj over products, rearrange
  conv_lhs => rw [← Complex.conj_re]
  congr 1
  simp only [map_mul, h_real, h_imag, h_int]
  ring


/-- The Poisson integral of a finite measure equals a Fourier expression.

For a finite measure μ with characteristic function `φ(t) = ∫ e^{iωt} dμ`:

`∫ P_ε(s - ω) dμ(ω) = (1/2π) ∫ e^{ist} · e^{-ε|t|} · φ(t) dt`

This is the key bridge: the LHS depends on μ directly, but the RHS depends
only on the characteristic function φ. -/
lemma poisson_integral_eq_fourier (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ∫ ω, poissonKernel ε (s - ω) ∂μ =
    (1 / (2 * Real.pi)) * (∫ t : ℝ,
      (exp (-(I * ↑s * ↑t)) * exp (-(↑ε * ↑(|t|)) : ℂ) *
       ∫ ω, exp (I * ↑ω * ↑t) ∂μ).re ∂volume) := by
  -- Joint integrand
  set g : ℝ → ℝ → ℂ := fun ω t => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑(s - ω) * ↑t)

  -- ── Integrability hypotheses ──
  have h_g_int : ∀ ω, Integrable (g ω) volume := by
    intro ω
    by_contra h
    have h0 := integral_undef h
    have h1 := fourier_two_sided_exp hε (s - ω)
    change ∫ t, g ω t = 0 at h0
    simp only [g] at h0
    rw [h0] at h1
    exact absurd (Complex.ofReal_eq_zero.mp h1.symm) (by positivity)

  have h_int_joint : Integrable (uncurry g) (μ.prod volume) := by
    rw [integrable_prod_iff (by fun_prop : AEStronglyMeasurable (uncurry g) _)]
    simp only [uncurry_apply_pair]
    suffices h : ∀ ω, ∫ t, ‖g ω t‖ = ∫ t, Real.exp (-ε * |t|) by
      simp_rw [h];
      simp only [neg_mul, ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm, and_true]
      exact ae_of_all μ h_g_int
    intro ω
    congr 1; ext t; simp only [g, norm_mul, Complex.norm_exp]
    simp [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]

  have h_int_inner : Integrable (fun ω => ∫ t, g ω t) μ := by
    have := h_int_joint.integral_prod_left
    simp only [uncurry_apply_pair] at this
    exact this

  have h_factor : ∀ t, ∫ ω, g ω t ∂μ =
    cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
    ∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ := by
    intro t
    show ∫ ω, cexp (-(↑ε * ↑|t|)) * cexp (I * ↑(s - ω) * ↑t) ∂μ = _
    have h_eq : (fun (ω : ℝ) => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑(s - ω) * ↑t)) =
        (fun (ω : ℝ) => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
                   cexp (-(I * ↑ω * ↑t))) := by
      ext ω; simp only [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h_eq]
    exact integral_const_mul _ _

  have h_int_factored : Integrable (fun (t : ℝ) =>
      cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
      ∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ) volume := by
    have := h_int_joint.integral_prod_right
    simp only [uncurry_apply_pair] at this
    exact this.congr (ae_of_all _ fun t => h_factor t)

  simp_rw [poissonKernel_eq_half_fourier hε]

  suffices h_inner : ∫ ω, (∫ (t : ℝ), g ω t).re ∂μ =
      ∫ (t : ℝ), (cexp (-(I * ↑s * ↑t)) * cexp (-(↑ε * ↑|t|)) *
        ∫ ω, cexp (I * ↑ω * ↑t) ∂μ).re by
    -- Replace poissonKernel with (1/(2π)) * (∫ t, g ω t).re
    have h_rw : ∀ ω, poissonKernel ε (s - ω) =
        (1 / (2 * Real.pi)) * (∫ (t : ℝ), g ω t).re :=
      fun ω => poissonKernel_eq_half_fourier hε (s - ω)
    simp only [ ← smul_eq_mul (a := 1 / (2 * Real.pi))]
    rw [integral_smul]
    congr 1
  -- ── Main calc chain ──
  calc ∫ ω, (∫ (t : ℝ), g ω t).re ∂μ
      -- (a) Re commutes with ∫_ω
      _ = (∫ ω, (∫ (t : ℝ), g ω t) ∂μ).re := by
          erw [Complex.reCLM.integral_comp_comm h_int_inner]; rfl
      -- (b) Fubini
      _ = (∫ (t : ℝ), ∫ ω, g ω t ∂μ).re := by
          congr 1;
          exact integral_integral_swap h_int_joint
      -- (c) Factor
      _ = (∫ (t : ℝ), cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
            ∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ).re := by
          congr 1; exact integral_congr_ae (ae_of_all _ fun t => h_factor t)
      -- (d) Re commutes with ∫_t
      _ = ∫ (t : ℝ), (cexp (-(↑ε * ↑|t|)) * cexp (I * ↑s * ↑t) *
            ∫ ω, cexp (-(I * ↑ω * ↑t)) ∂μ).re := by
          have := (Complex.reCLM.integral_comp_comm h_int_factored).symm
          simp only at this
          exact this
      -- (e) Conjugation trick
      _ = ∫ (t : ℝ), (cexp (-(I * ↑s * ↑t)) * cexp (-(↑ε * ↑|t|)) *
            ∫ ω, cexp (I * ↑ω * ↑t) ∂μ).re := by
          congr 1; ext t; exact re_conjugate_trick μ


/-- Corollary: two measures with the same characteristic function have the
    same Poisson integrals. -/
lemma poisson_integral_eq_of_fourier_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    ∫ ω, poissonKernel ε (s - ω) ∂μ = ∫ ω, poissonKernel ε (s - ω) ∂ν := by
  rw [poisson_integral_eq_fourier μ hε s, poisson_integral_eq_fourier ν hε s]
  congr 1; congr 1
  ext t; congr 1; congr 1
  exact h t

end SpectralBridge.Bochner.FourierUniqueness
