/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: FunctionalCalc/BoundedFunctionalCalc.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Algebraic
/-!
# Bounded Functional Calculus: *-Homomorphism and Unitary Groups

This file completes the bounded functional calculus as a *-homomorphism
from bounded Borel functions to `B(H)`, with no domain hypotheses on vectors.

The key payoff is the construction of one-parameter unitary groups from
spectral power functions `λ ↦ exp(i t log λ)`, whose group law follows
purely from the multiplicativity of the bounded calculus.

## Main definitions

* `spectralPowerFunction`: The family `t ↦ (λ ↦ exp(i t log λ))` of bounded Borel functions

## Main results

### Bounded *-homomorphism (full Hilbert space, no domain hypotheses)

* `boundedFunctionalCalculus_mul`: `Φ(fg) = Φ(f) ∘ Φ(g)`
* `boundedFunctionalCalculus_conj`: `Φ(f̄) = Φ(f)*`
* `boundedFunctionalCalculus_one_eq`: `Φ(1) = I`

### Unitarity

* `boundedFunctionalCalculus_isUnitary`: `|f| = 1` implies `Φ(f)` is unitary

### One-parameter unitary groups

* `spectralPowerFunction_norm`: `‖exp(i t log λ)‖ = 1`
* `spectralPowerFunction_mul`: `f_s · f_t = f_{s+t}` (pointwise group law)
* `spectralPowerFunction_zero`: `f_0 = 1`
* `boundedFunctionalCalculus_unitaryGroup`: `Φ(f_{s+t}) = Φ(f_s) * Φ(f_t)`

## Tags

bounded functional calculus, *-homomorphism, unitary group, Stone's theorem
-/
namespace FunctionalCalculus

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent
  SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-!
## Auxiliary lemmas for bounded function algebra
-/

/-- Product of bounded functions is bounded. -/
lemma bounded_mul {f g : ℝ → ℂ}
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (hg : ∃ M, ∀ s, ‖g s‖ ≤ M) :
    ∃ M, ∀ s, ‖(f * g) s‖ ≤ M := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨Mf * Mg, fun s => ?_⟩
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hMf s) (hMg s) (norm_nonneg _) (le_trans (norm_nonneg _) (hMf s))

/-- Conjugate of a bounded function is bounded. -/
lemma bounded_conj {f : ℝ → ℂ}
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    ∃ M, ∀ s, ‖(starRingEnd ℂ ∘ f) s‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun s => by simp only [Function.comp_apply, RCLike.norm_conj]; exact hM s⟩

/-!
## Bounded *-Homomorphism Properties
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- **Multiplication**: `Φ(fg) = Φ(f) ∘ Φ(g)` for bounded Borel functions.

    This is the key structural result: no domain hypotheses are needed because
    every vector is in the functional domain of every bounded function. -/
lemma boundedFunctionalCalculus_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℂ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (hg : ∃ M, ∀ s, ‖g s‖ ≤ M)
    (hfg : ∃ M, ∀ s, ‖(f * g) s‖ ≤ M) :
    boundedFunctionalCalculus E hE (f * g) hfg =
    (boundedFunctionalCalculus E hE f hf) * (boundedFunctionalCalculus E hE g hg) := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.mul_apply]
  -- Every vector is in the domain of every bounded function
  have hψg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g :=
    functionalDomain_of_bounded E hE hE_univ g hg_meas hg ψ
  have hψfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g) :=
    functionalDomain_of_bounded E hE hE_univ (f * g) (hf_meas.mul hg_meas) hfg ψ
  -- The output of Φ(g) is also in the domain of f (bounded!)
  have hΦgψ_f : spectral_integral E hE g ψ hψg ∈
      functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE hE_univ f hf_meas hf _
  -- Bridge bounded → unbounded
  rw [← spectral_integral_bounded_eq E hE (f * g) hfg ψ hψfg]
  rw [← spectral_integral_bounded_eq E hE g hg ψ hψg]
  -- Apply multiplicativity of the unbounded calculus
  rw [spectral_integral_mul E hE f g ψ hψg hΦgψ_f hψfg]
  -- Bridge back
  rw [spectral_integral_bounded_eq E hE f hf _ hΦgψ_f]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- **Conjugation**: `Φ(f̄) = Φ(f)*` for bounded Borel functions.

    The adjoint of the functional calculus applied to `f` equals the functional
    calculus applied to the complex conjugate of `f`. -/
lemma boundedFunctionalCalculus_conj (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) (hf_meas : Measurable f) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    let hf_conj : ∃ M, ∀ s, ‖(starRingEnd ℂ ∘ f) s‖ ≤ M := bounded_conj hf
    (boundedFunctionalCalculus E hE f hf).adjoint =
    boundedFunctionalCalculus E hE (starRingEnd ℂ ∘ f) hf_conj := by
  intro hf_conj
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [boundedFunctionalCalculus]
  have hf_conj_meas : Measurable (starRingEnd ℂ ∘ f) := continuous_star.measurable.comp hf_meas
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE hE_univ f hf_meas hf ψ
  have hφ_conj : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f) :=
    functionalDomain_of_bounded E hE hE_univ (starRingEnd ℂ ∘ f) hf_conj_meas hf_conj φ
  rw [← spectral_integral_bounded_eq E hE f hf ψ hψf]
  rw [← spectral_integral_bounded_eq E hE (starRingEnd ℂ ∘ f) hf_conj φ hφ_conj]
  exact spectral_integral_conj E hE f ψ φ hψf hφ_conj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- **Identity**: `Φ(1) = I` for the bounded functional calculus.

    Clean formulation as a `ContinuousLinearMap` identity. -/
lemma boundedFunctionalCalculus_one_eq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) :
    boundedFunctionalCalculus E hE (fun _ => 1) ⟨1, fun _ => by simp⟩ = 1 := by
  have h := boundedFunctionalCalculus_const E hE hE_univ (1 : ℂ)
  simp only [one_smul] at h
  convert h using 2

/-!
## Unitarity
-/

/-- A bounded function with `‖f(s)‖ = 1` everywhere gives a unitary operator.

    The proof assembles three facts:
    - `Φ(f̄) = Φ(f)*` (conjugation)
    - `Φ(f · f̄) = Φ(f) Φ(f)*` (multiplication)
    - `f · f̄ = 1` pointwise when `|f| = 1`
    and symmetrically for `f̄ · f`. -/
theorem boundedFunctionalCalculus_isUnitary (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) (hf_meas : Measurable f)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M)
    (hf_unit : ∀ s, ‖f s‖ = 1) :
    let hf_conj := bounded_conj hf
    (boundedFunctionalCalculus E hE f hf) *
    (boundedFunctionalCalculus E hE (starRingEnd ℂ ∘ f) hf_conj) = 1 ∧
    (boundedFunctionalCalculus E hE (starRingEnd ℂ ∘ f) hf_conj) *
    (boundedFunctionalCalculus E hE f hf) = 1 := by
  intro hf_conj
  -- f · conj f = 1 pointwise
  have h_f_mul_conj : f * (starRingEnd ℂ ∘ f) = fun _ => 1 := by
    ext s
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [RCLike.mul_conj, hf_unit s]
    simp
  have h_conj_mul_f : (starRingEnd ℂ ∘ f) * f = fun _ => 1 := by
    ext s
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [mul_comm, RCLike.mul_conj, hf_unit s]
    simp
  have hf_conj_meas : Measurable (starRingEnd ℂ ∘ f) := continuous_star.measurable.comp hf_meas
  -- Boundedness of the products
  have h_prod_bdd : ∃ M, ∀ s, ‖(f * (starRingEnd ℂ ∘ f)) s‖ ≤ M :=
    ⟨1, fun s => by rw [show (f * (starRingEnd ℂ ∘ f)) s = 1 from congr_fun h_f_mul_conj s]; simp⟩
  have h_prod_bdd' : ∃ M, ∀ s, ‖((starRingEnd ℂ ∘ f) * f) s‖ ≤ M :=
    ⟨1, fun s => by rw [show ((starRingEnd ℂ ∘ f) * f) s = 1 from congr_fun h_conj_mul_f s]; simp⟩
  constructor
  · -- Φ(f) * Φ(f̄) = Φ(f · f̄) = Φ(1) = I
    rw [← boundedFunctionalCalculus_mul E hE hE_univ f (starRingEnd ℂ ∘ f)
        hf_meas hf_conj_meas hf hf_conj h_prod_bdd]
    conv_lhs => rw [show boundedFunctionalCalculus E hE (f * (starRingEnd ℂ ∘ f)) h_prod_bdd =
      boundedFunctionalCalculus E hE (fun _ => 1) ⟨1, fun _ => by simp⟩ from by
        congr 1]
    exact boundedFunctionalCalculus_one_eq E hE hE_univ
  · -- Φ(f̄) * Φ(f) = Φ(f̄ · f) = Φ(1) = I
    rw [← boundedFunctionalCalculus_mul E hE hE_univ (starRingEnd ℂ ∘ f) f
        hf_conj_meas hf_meas hf_conj hf h_prod_bdd']
    conv_lhs => rw [show boundedFunctionalCalculus E hE ((starRingEnd ℂ ∘ f) * f) h_prod_bdd' =
      boundedFunctionalCalculus E hE (fun _ => 1) ⟨1, fun _ => by simp⟩ from by
        congr 1]
    exact boundedFunctionalCalculus_one_eq E hE hE_univ

/-!
## One-Parameter Unitary Groups via Spectral Power Functions
-/

/-- The spectral power function `f_t(λ) = exp(i t log λ)`.

    For `λ > 0` this equals `λ^{it}`. For `λ ≤ 0`, `Real.log` returns its junk
    value (0), giving `exp(0) = 1`. The function is bounded by 1 everywhere
    since `exp` of a purely imaginary argument has unit modulus.

    When the spectral measure is supported on `(0, ∞)` (positive operators),
    the junk values are invisible to integration. -/
noncomputable def spectralPowerFunction (t : ℝ) : ℝ → ℂ :=
  fun s => Complex.exp (↑t * Complex.I * ↑(Real.log s))

/-- `|exp(i t log λ)| = 1` for all `λ` and `t`. -/
lemma spectralPowerFunction_norm (t : ℝ) (s : ℝ) : ‖spectralPowerFunction t s‖ = 1 := by
  simp only [spectralPowerFunction]
  have h_eq : ↑t * Complex.I * ↑(Real.log s) = ↑(t * Real.log s) * Complex.I := by
    push_cast; ring
  rw [h_eq, Complex.norm_exp]
  have h_re : (↑(t * Real.log s) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [h_re, Real.exp_zero]

/-- The spectral power function is bounded by 1. -/
lemma spectralPowerFunction_bounded (t : ℝ) : ∃ M, ∀ s, ‖spectralPowerFunction t s‖ ≤ M :=
  ⟨1, fun s => le_of_eq (spectralPowerFunction_norm t s)⟩

/-- The spectral power function is norm-one everywhere. -/
lemma spectralPowerFunction_unit (t : ℝ) : ∀ s, ‖spectralPowerFunction t s‖ = 1 :=
  spectralPowerFunction_norm t

/-- Measurability of the spectral power function. -/
lemma spectralPowerFunction_measurable (t : ℝ) : Measurable (spectralPowerFunction t) := by
  unfold spectralPowerFunction
  apply Complex.measurable_exp.comp
  apply Measurable.mul measurable_const
  exact Complex.measurable_ofReal.comp Real.measurable_log

/-- **Pointwise group law**: `f_s · f_t = f_{s+t}`.

    This is the key algebraic identity: `exp(is log λ) · exp(it log λ) = exp(i(s+t) log λ)`.
    The group law for `Φ(f_t)` follows immediately from multiplicativity. -/
theorem spectralPowerFunction_mul (s t : ℝ) :
    spectralPowerFunction s * spectralPowerFunction t = spectralPowerFunction (s + t) := by
  ext lambda
  simp only [spectralPowerFunction, Pi.mul_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `f_0 = 1` (the identity function in the group). -/
theorem spectralPowerFunction_zero :
    spectralPowerFunction 0 = fun _ => 1 := by
  ext s
  simp [spectralPowerFunction, Complex.exp_zero]

/-- `f_{-t} = conj(f_t)` for the spectral power function.

    Since `exp(-it log λ) = conj(exp(it log λ))` when the argument is purely imaginary. -/
theorem spectralPowerFunction_neg (t : ℝ) :
    spectralPowerFunction (-t) = starRingEnd ℂ ∘ spectralPowerFunction t := by
  ext s
  simp only [spectralPowerFunction, Function.comp_apply]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- **One-parameter unitary group law**:
    `Φ(f_{s+t}) = Φ(f_s) * Φ(f_t)`.

    Combined with unitarity (`|f_t| = 1` ⟹ `Φ(f_t)` unitary) and the identity
    (`Φ(f_0) = I`), this establishes that `t ↦ Φ(f_t)` is a one-parameter
    unitary group. This is the spectral-theoretic core of Stone's theorem. -/
theorem boundedFunctionalCalculus_unitaryGroup
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (s t : ℝ) :
    boundedFunctionalCalculus E hE (spectralPowerFunction (s + t))
      (spectralPowerFunction_bounded (s + t)) =
    (boundedFunctionalCalculus E hE (spectralPowerFunction s)
      (spectralPowerFunction_bounded s)) *
    (boundedFunctionalCalculus E hE (spectralPowerFunction t)
      (spectralPowerFunction_bounded t)) := by
  -- The group law is: Φ(f_{s+t}) = Φ(f_s · f_t) = Φ(f_s) * Φ(f_t)
  -- Step 1: f_{s+t} = f_s · f_t (pointwise)
  have h_eq : spectralPowerFunction (s + t) = spectralPowerFunction s * spectralPowerFunction t :=
    (spectralPowerFunction_mul s t).symm
  -- Step 2: Rewrite LHS using the pointwise identity
  conv_lhs => rw [show boundedFunctionalCalculus E hE (spectralPowerFunction (s + t))
    (spectralPowerFunction_bounded (s + t)) =
    boundedFunctionalCalculus E hE (spectralPowerFunction s * spectralPowerFunction t)
      (bounded_mul (spectralPowerFunction_bounded s) (spectralPowerFunction_bounded t)) from by
        congr 1]
  -- Step 3: Apply multiplicativity of bounded calculus
  exact boundedFunctionalCalculus_mul E hE hE_univ
    (spectralPowerFunction s) (spectralPowerFunction t)
    (spectralPowerFunction_measurable s) (spectralPowerFunction_measurable t)
    (spectralPowerFunction_bounded s) (spectralPowerFunction_bounded t)
    (bounded_mul (spectralPowerFunction_bounded s) (spectralPowerFunction_bounded t))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- The identity element of the one-parameter group: `Φ(f_0) = I`. -/
theorem boundedFunctionalCalculus_unitaryGroup_zero
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1) :
    boundedFunctionalCalculus E hE (spectralPowerFunction 0) (spectralPowerFunction_bounded 0) = 1 := by
  conv_lhs => rw [show boundedFunctionalCalculus E hE (spectralPowerFunction 0)
    (spectralPowerFunction_bounded 0) =
    boundedFunctionalCalculus E hE (fun _ => 1) ⟨1, fun _ => by simp⟩ from by
      congr 1
      exact spectralPowerFunction_zero]
  exact boundedFunctionalCalculus_one_eq E hE hE_univ

/-- Each `Φ(f_t)` is unitary: `Φ(f_t) Φ(f_t)* = I` and `Φ(f_t)* Φ(f_t) = I`. -/
theorem boundedFunctionalCalculus_unitaryGroup_isUnitary
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1) (t : ℝ) :
    let hft := spectralPowerFunction_bounded t
    let hft_conj := bounded_conj hft
    (boundedFunctionalCalculus E hE (spectralPowerFunction t) hft) *
    (boundedFunctionalCalculus E hE (starRingEnd ℂ ∘ spectralPowerFunction t) hft_conj) = 1 ∧
    (boundedFunctionalCalculus E hE (starRingEnd ℂ ∘ spectralPowerFunction t) hft_conj) *
    (boundedFunctionalCalculus E hE (spectralPowerFunction t) hft) = 1 :=
  boundedFunctionalCalculus_isUnitary E hE hE_univ
    (spectralPowerFunction t) (spectralPowerFunction_measurable t)
    (spectralPowerFunction_bounded t) (spectralPowerFunction_unit t)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The adjoint of `Φ(f_t)` is `Φ(f_{-t})`: inversion in the group is time-reversal.

    This connects `Φ(f_t)* = Φ(conj ∘ f_t) = Φ(f_{-t})`. -/
theorem boundedFunctionalCalculus_unitaryGroup_adjoint
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1) (t : ℝ) :
    (boundedFunctionalCalculus E hE (spectralPowerFunction t)
      (spectralPowerFunction_bounded t)).adjoint =
    boundedFunctionalCalculus E hE (spectralPowerFunction (-t))
      (spectralPowerFunction_bounded (-t)) := by
  -- Φ(f_t)* = Φ(conj ∘ f_t) by conjugation property
  have h_adj := boundedFunctionalCalculus_conj E hE hE_univ
    (spectralPowerFunction t) (spectralPowerFunction_measurable t) (spectralPowerFunction_bounded t)
  rw [h_adj]
  -- conj ∘ f_t = f_{-t} by spectralPowerFunction_neg
  congr 1
  exact (spectralPowerFunction_neg t).symm

end FunctionalCalculus
