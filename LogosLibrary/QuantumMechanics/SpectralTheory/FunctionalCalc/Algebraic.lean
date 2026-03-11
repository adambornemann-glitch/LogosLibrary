/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc.Integral
/-!
# Algebraic Properties of Functional Calculus

This file establishes that the functional calculus is a *-homomorphism from
(a suitable algebra of) functions on `ℝ` to operators on `H`.

## Main definitions

* `boundedFunctionalCalculus`: Functional calculus for bounded Borel functions
* `functionalCalculus`: Functional calculus for general measurable functions

## Main results (*-homomorphism properties)

* `functionalCalculus_add`: `(f + g)(A) = f(A) + g(A)`
* `functionalCalculus_mul`: `(fg)(A) = f(A) ∘ g(A)`
* `functionalCalculus_conj`: `f̄(A) = f(A)*`
* `functionalCalculus_one`: `1(A) = I`
* `functionalCalculus_indicator`: `𝟙_B(A) = E(B)`

## Extended lemmas for bounded calculus

* `boundedFunctionalCalculus_nonneg`: Positivity preservation
* `boundedFunctionalCalculus_mono`: Monotonicity
* `boundedFunctionalCalculus_real_selfAdjoint`: Real functions give self-adjoint operators
* `boundedFunctionalCalculus_sq`: `Φ(f²) = Φ(f)²`

## Tags

functional calculus, *-homomorphism, Borel functional calculus
-/
namespace FunctionalCalculus

open MeasureTheory InnerProductSpace Complex QuantumMechanics.Cayley SpectralBridge.Resolvent SpectralBridge.Bochner QuantumMechanics.Generators ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Main Definitions
-/

/-- Functional calculus for bounded Borel functions.
    This is a *-homomorphism from L^∞(ℝ, μ_ψ) to B(H). -/
noncomputable def boundedFunctionalCalculus
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f : ℝ → ℂ)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) : H →L[ℂ] H :=
  spectral_integral_bounded E hE f hf

/-- Functional calculus for general measurable functions. -/
noncomputable def functionalCalculus
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) :
    functionalDomainSubmodule E hE hE_univ f →ₗ[ℂ] H where
  toFun := fun ⟨ψ, hψ⟩ => spectral_integral E hE f ψ hψ
  map_add' := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    simp only
    have hxy : x + y ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
      (functionalDomainSubmodule E hE hE_univ f).add_mem hx hy
    exact spectral_integral_add_vector E hE f x y hx hy hxy
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    simp only [RingHom.id_apply]
    have hcψ : c • ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
      (functionalDomainSubmodule E hE hE_univ f).smul_mem c hψ
    exact spectral_integral_smul_vector E hE f c ψ hψ hcψ

/-- The inner product formula for functional calculus. -/
axiom functionalCalculus_inner
    (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E) (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ)
    (ψ : H) (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    ⟪functionalCalculus E hE hE_univ f ⟨ψ, hψ⟩, ψ⟫_ℂ = ∫ s, f s ∂(spectral_scalar_measure E ψ hE)

/-!
## Helper Lemmas for Algebraic Properties
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Spectral integral is additive in f -/
theorem spectral_integral_add_function (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    spectral_integral E hE (f + g) ψ hfg =
    spectral_integral E hE f ψ hf + spectral_integral E hE g ψ hg :=
  spectral_integral_add E hE f g ψ hf hg hfg

/-- Spectral integral is multiplicative in f (composition property) -/
theorem spectral_integral_mul_function (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (f g : ℝ → ℂ) (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g))
    (hf_gψ : spectral_integral E hE g ψ hg ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    spectral_integral E hE (f * g) ψ hfg =
    spectral_integral E hE f (spectral_integral E hE g ψ hg) hf_gψ :=
  spectral_integral_mul E hE f g ψ hg hf_gψ hfg

/-!
## *-Homomorphism Properties
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- **Addition**: (f + g)(A) = f(A) + g(A) -/
theorem functionalCalculus_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f g : ℝ → ℂ) (ψ : H)
    (hf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g)) :
    functionalCalculus E hE hE_univ (f + g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE hE_univ f ⟨ψ, hf⟩ + functionalCalculus E hE hE_univ g ⟨ψ, hg⟩ :=
  spectral_integral_add_function E hE f g ψ hf hg hfg

/-- **Multiplication**: (fg)(A) = f(A) ∘ g(A) on appropriate domain -/
theorem functionalCalculus_mul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f g : ℝ → ℂ) (ψ : H)
    (hg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g)
    (hfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f * g))
    (hf_gψ : functionalCalculus E hE hE_univ g ⟨ψ, hg⟩ ∈ functionalDomain (spectral_scalar_measure E · hE) f) :
    functionalCalculus E hE hE_univ (f * g) ⟨ψ, hfg⟩ =
    functionalCalculus E hE hE_univ f ⟨functionalCalculus E hE hE_univ g ⟨ψ, hg⟩, hf_gψ⟩ :=
  spectral_integral_mul_function E hE f g ψ hg hfg hf_gψ

/-- **Conjugation**: f̄(A) = f(A)* -/
theorem functionalCalculus_conj (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (ψ φ : H)
    (hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f)
    (hφ : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f)) :
    ⟪functionalCalculus E hE hE_univ f ⟨ψ, hψ⟩, φ⟫_ℂ =
    ⟪ψ, functionalCalculus E hE hE_univ (starRingEnd ℂ ∘ f) ⟨φ, hφ⟩⟫_ℂ :=
  spectral_integral_conj E hE f ψ φ hψ hφ

/-- **Normalization**: 1(A) = I -/
theorem functionalCalculus_one (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ => 1)) :
    functionalCalculus E hE hE_univ (fun _ => 1) ⟨ψ, h⟩ = ψ :=
  spectral_integral_one E hE hE_univ ψ h

/-- **Spectral mapping for indicator**: 𝟙_B(A) = E(B) -/
theorem functionalCalculus_indicator (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (B : Set ℝ) (hB : MeasurableSet B)
    (ψ : H) (h : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (Set.indicator B 1)) :
    functionalCalculus E hE hE_univ (Set.indicator B 1) ⟨ψ, h⟩ = E B ψ :=
  spectral_integral_indicator E hE hE_univ B hB ψ h

/-!
## Bounded Functional Calculus Properties
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Bounded spectral integral is additive in f -/
lemma spectral_integral_bounded_add (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℂ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) (hg : ∃ M, ∀ s, ‖g s‖ ≤ M)
    (hfg : ∃ M, ∀ s, ‖(f + g) s‖ ≤ M) :
    spectral_integral_bounded E hE (f + g) hfg =
    spectral_integral_bounded E hE f hf + spectral_integral_bounded E hE g hg := by
  ext ψ
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE hE_univ f hf_meas hf ψ
  have hψg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g :=
    functionalDomain_of_bounded E hE hE_univ g hg_meas hg ψ
  have hψfg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f + g) :=
    functionalDomain_of_bounded E hE hE_univ (f + g) (hf_meas.add hg_meas) hfg ψ
  simp only [ContinuousLinearMap.add_apply]
  rw [← spectral_integral_bounded_eq E hE (f + g) hfg ψ hψfg,
      ← spectral_integral_bounded_eq E hE f hf ψ hψf,
      ← spectral_integral_bounded_eq E hE g hg ψ hψg]
  exact spectral_integral_add E hE f g ψ hψf hψg hψfg

/-- Bounded spectral integral is homogeneous in f -/
lemma spectral_integral_bounded_smul (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (c : ℂ) (f : ℝ → ℂ)
    (hf_meas : Measurable f)
    (hf : ∃ M, ∀ s, ‖f s‖ ≤ M)
    (hcf : ∃ M, ∀ s, ‖(c • f) s‖ ≤ M) :
    spectral_integral_bounded E hE (c • f) hcf = c • spectral_integral_bounded E hE f hf := by
  ext ψ
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE hE_univ f hf_meas hf ψ
  have hψcf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • f) :=
    functionalDomain_of_bounded E hE hE_univ (c • f) (hf_meas.const_smul c) hcf ψ
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [← spectral_integral_bounded_eq E hE (c • f) hcf ψ hψcf,
      ← spectral_integral_bounded_eq E hE f hf ψ hψf]
  exact spectral_integral_smul E hE c f ψ hψf hψcf

/-- Functional calculus of zero function is zero -/
lemma boundedFunctionalCalculus_zero (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) :
    boundedFunctionalCalculus E hE (fun _ => 0) ⟨0, fun _ => by simp⟩ = 0 := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.zero_apply]
  have hψ : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (0 : ℂ)) :=
    functionalDomain_of_bounded E hE hE_univ (fun _ => 0) measurable_const ⟨0, fun _ => by simp⟩ ψ
  rw [← spectral_integral_bounded_eq E hE (fun _ => 0) ⟨0, fun _ => by simp⟩ ψ hψ]
  have h1 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (1 : ℂ)) :=
    functionalDomain_of_bounded E hE hE_univ (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩ ψ
  have h0_eq : (fun _ : ℝ => (0 : ℂ)) = (0 : ℂ) • (fun _ : ℝ => (1 : ℂ)) := by ext; simp
  have hψ0 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) ((0 : ℂ) • fun _ : ℝ => (1 : ℂ)) := by
    convert hψ using 2
    ext; simp
  rw [← @enorm_eq_zero]
  convert spectral_integral_smul E hE 0 (fun _ : ℝ => (1 : ℂ)) ψ h1 hψ0 using 1
  simp only [zero_smul]
  exact ENormedAddMonoid.enorm_eq_zero (spectral_integral E hE (fun x => 0) ψ hψ)

/-- Functional calculus of a constant function `c` is scalar multiplication by `c`:
    `Φ(λ_ . c) = c · I`. -/
lemma boundedFunctionalCalculus_const (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (c : ℂ) :
    boundedFunctionalCalculus E hE (fun _ => c) ⟨‖c‖, fun _ => le_refl _⟩ = c • 1 := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  have h_eq : (fun _ : ℝ => c) = c • (fun _ : ℝ => (1 : ℂ)) := by ext s; simp
  have hψ1 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => (1 : ℂ)) :=
    functionalDomain_of_bounded E hE hE_univ _ measurable_const ⟨1, fun _ => by simp⟩ ψ
  have hψc : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun _ : ℝ => c) :=
    functionalDomain_of_bounded E hE hE_univ _ measurable_const ⟨‖c‖, fun _ => le_refl _⟩ ψ
  have hψc' : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (c • fun _ : ℝ => (1 : ℂ)) := by
    rw [← h_eq]; exact hψc
  rw [← spectral_integral_bounded_eq E hE _ ⟨‖c‖, fun _ => le_refl _⟩ ψ hψc]
  rw [spectral_integral_eq_of_eq_fun E hE _ _ h_eq ψ hψc hψc']
  rw [spectral_integral_smul E hE c (fun _ : ℝ => (1 : ℂ)) ψ hψ1 hψc']
  rw [spectral_integral_one E hE hE_univ ψ hψ1]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Functional calculus respects negation -/
lemma boundedFunctionalCalculus_neg (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℂ) (hf_meas : Measurable f) (hf : ∃ M, ∀ s, ‖f s‖ ≤ M) :
    boundedFunctionalCalculus E hE (-f) (by obtain ⟨M, hM⟩ := hf; exact ⟨M, fun s => by simp [hM s]⟩) =
    -boundedFunctionalCalculus E hE f hf := by
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.neg_apply]
  have h_eq : -f = (-1 : ℂ) • f := by ext s; simp
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f :=
    functionalDomain_of_bounded E hE hE_univ f hf_meas hf ψ
  have hψnf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (-f) :=
    functionalDomain_of_bounded E hE hE_univ (-f) hf_meas.neg
      (by obtain ⟨M, hM⟩ := hf; exact ⟨M, fun s => by simp [hM s]⟩) ψ
  have hψnf' : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) ((-1 : ℂ) • f) := by
    rw [← h_eq]; exact hψnf
  rw [← spectral_integral_bounded_eq E hE (-f) _ ψ hψnf]
  rw [← spectral_integral_bounded_eq E hE f hf ψ hψf]
  rw [spectral_integral_eq_of_eq_fun E hE _ _ h_eq ψ hψnf hψnf']
  rw [spectral_integral_smul E hE (-1) f ψ hψf hψnf']
  simp only [neg_smul, one_smul]


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Real-valued bounded functions give self-adjoint operators -/
lemma boundedFunctionalCalculus_real_selfAdjoint (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf : ∃ M, ∀ s, |f s| ≤ M) :
    let f' : ℝ → ℂ := fun s => f s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    (boundedFunctionalCalculus E hE f' hf').adjoint = boundedFunctionalCalculus E hE f' hf' := by
  intro f' hf'
  ext φ
  apply ext_inner_left ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [boundedFunctionalCalculus]
  have hf'_meas : Measurable f' := Complex.measurable_ofReal.comp hf_meas
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' ψ
  have hφf : φ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' φ
  have h_conj : starRingEnd ℂ ∘ f' = f' := by
    ext s
    simp only [Function.comp_apply, f', Complex.conj_ofReal]
  have hφ_conj : φ ∈ functionalDomain (spectral_scalar_measure E · hE) (starRingEnd ℂ ∘ f') := by
    rw [h_conj]; exact hφf
  rw [← spectral_integral_bounded_eq E hE f' hf' ψ hψf]
  rw [← spectral_integral_bounded_eq E hE f' hf' φ hφf]
  rw [spectral_integral_conj E hE f' ψ φ hψf hφ_conj]
  congr 1
  exact spectral_integral_eq_of_eq_fun E hE _ _ h_conj φ hφ_conj hφf

/-!
## Positivity and Monotonicity
-/

/-- If `g : X → ℂ` has `(g x).re ≥ 0` for all `x`, then `(∫ g dμ).re ≥ 0`.
    This is the complex version of nonnegativity preservation under integration. -/
lemma integral_re_nonneg {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} (hg : ∀ x, 0 ≤ (g x).re) (hg_int : Integrable g μ) :
    0 ≤ (∫ x, g x ∂μ).re := by
  calc (∫ x, g x ∂μ).re
      = RCLike.re (∫ x, g x ∂μ) := rfl
    _ = ∫ x, RCLike.re (g x) ∂μ := (integral_re hg_int).symm
    _ = ∫ x, (g x).re ∂μ := by rfl
    _ ≥ 0 := integral_nonneg hg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Positive functions give positive operators -/
lemma boundedFunctionalCalculus_nonneg (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ s, |f s| ≤ M)
    (hf_pos : ∀ s, 0 ≤ f s) (ψ : H) :
    let f' : ℝ → ℂ := fun s => f s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf_bdd
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    0 ≤ (⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ).re := by
  intro f' hf'
  simp only [boundedFunctionalCalculus]
  have hf'_meas : Measurable f' := Complex.measurable_ofReal.comp hf_meas
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' ψ
  rw [← spectral_integral_bounded_eq E hE f' hf' ψ hψf]
  rw [spectral_integral_inner_cross E hE hE_univ f' ψ ψ hψf hf'_meas hf']
  have hint : Integrable f' (spectral_scalar_measure E ψ hE) := by
    haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
      spectral_scalar_measure_finite E hE hE_univ ψ
    refine ⟨hf'_meas.aestronglyMeasurable, ?_⟩
    obtain ⟨M, hM⟩ := hf'
    apply MeasureTheory.HasFiniteIntegral.of_bounded
    exact Filter.Eventually.of_forall hM
  rw [spectral_cross_integral_diag E hE hE_univ f' ψ hint]
  rw [← Complex.reCLM_apply]
  erw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]

  apply MeasureTheory.integral_nonneg
  intro s
  simp only [f']
  exact hf_pos s


/-- Monotonicity of functional calculus -/
lemma boundedFunctionalCalculus_mono (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f g : ℝ → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bdd : ∃ M, ∀ s, |f s| ≤ M) (hg_bdd : ∃ M, ∀ s, |g s| ≤ M)
    (hfg : ∀ s, f s ≤ g s) (ψ : H) :
    let f' : ℝ → ℂ := fun s => f s
    let g' : ℝ → ℂ := fun s => g s
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf_bdd
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    let hg' : ∃ M, ∀ s, ‖g' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hg_bdd
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    (⟪boundedFunctionalCalculus E hE f' hf' ψ, ψ⟫_ℂ).re ≤
    (⟪boundedFunctionalCalculus E hE g' hg' ψ, ψ⟫_ℂ).re := by
  intro f' g' hf' hg'
  have h_diff_nonneg : ∀ s, 0 ≤ (g s - f s) := fun s => sub_nonneg.mpr (hfg s)
  have h_diff_bdd : ∃ M, ∀ s, |g s - f s| ≤ M := by
    obtain ⟨Mf, hMf⟩ := hf_bdd
    obtain ⟨Mg, hMg⟩ := hg_bdd
    refine ⟨Mg + Mf, fun s => ?_⟩
    calc |g s - f s| ≤ |g s| + |f s| := abs_sub_le (g s) 0 (f s) |>.trans (by simp)
         _ ≤ Mg + Mf := add_le_add (hMg s) (hMf s)
  have h_nonneg := boundedFunctionalCalculus_nonneg E hE hE_univ (g - f)
    (hg_meas.sub hf_meas) h_diff_bdd h_diff_nonneg ψ
  simp only [Pi.sub_apply, Complex.ofReal_sub] at h_nonneg
  have hf'_meas : Measurable f' := Complex.measurable_ofReal.comp hf_meas
  have hg'_meas : Measurable g' := Complex.measurable_ofReal.comp hg_meas
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' ψ
  have hψg : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) g' :=
    functionalDomain_of_bounded E hE hE_univ g' hg'_meas hg' ψ
  simp only [boundedFunctionalCalculus] at h_nonneg ⊢
  rw [← spectral_integral_bounded_eq E hE f' hf' ψ hψf]
  rw [← spectral_integral_bounded_eq E hE g' hg' ψ hψg]
  -- Get integrability for cross_integral_diag
  have hf_int : Integrable f' (spectral_scalar_measure E ψ hE) := by
    haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
      spectral_scalar_measure_finite E hE hE_univ ψ
    refine ⟨hf'_meas.aestronglyMeasurable, ?_⟩
    obtain ⟨M, hM⟩ := hf'
    exact MeasureTheory.HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hM)
  have hg_int : Integrable g' (spectral_scalar_measure E ψ hE) := by
    haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
      spectral_scalar_measure_finite E hE hE_univ ψ
    refine ⟨hg'_meas.aestronglyMeasurable, ?_⟩
    obtain ⟨M, hM⟩ := hg'
    exact MeasureTheory.HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hM)
  rw [spectral_integral_inner_cross E hE hE_univ f' ψ ψ hψf hf'_meas hf']
  rw [spectral_integral_inner_cross E hE hE_univ g' ψ ψ hψg hg'_meas hg']
  rw [spectral_cross_integral_diag E hE hE_univ f' ψ hf_int]
  rw [spectral_cross_integral_diag E hE hE_univ g' ψ hg_int]
  -- Now have: 0 ≤ (∫ (g' - f') dμ).re and goal: (∫ f' dμ).re ≤ (∫ g' dμ).re
  have hgf_int : Integrable (fun s => g' s - f' s) (spectral_scalar_measure E ψ hE) :=
    hg_int.sub hf_int
  have h_gf_bdd : ∃ M, ∀ s, ‖(fun s => g' s - f' s) s‖ ≤ M := by
    obtain ⟨M, hM⟩ := h_diff_bdd
    refine ⟨M, fun s => ?_⟩
    simp only [f', g']
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hM s
  have hψgf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (fun s => g' s - f' s) :=
    functionalDomain_of_bounded E hE hE_univ _ (hg'_meas.sub hf'_meas) h_gf_bdd ψ
  rw [← spectral_integral_bounded_eq E hE _ h_gf_bdd ψ hψgf] at h_nonneg
  rw [spectral_integral_inner_cross E hE hE_univ _ ψ ψ hψgf (hg'_meas.sub hf'_meas) h_gf_bdd] at h_nonneg
  rw [spectral_cross_integral_diag E hE hE_univ _ ψ hgf_int] at h_nonneg
  -- Now h_nonneg : 0 ≤ (∫ (g' - f') dμ).re
  have h_sub : ∫ s, (g' s - f' s) ∂spectral_scalar_measure E ψ hE =
               ∫ s, g' s ∂spectral_scalar_measure E ψ hE -
               ∫ s, f' s ∂spectral_scalar_measure E ψ hE := by
    rw [← MeasureTheory.integral_sub hg_int hf_int]
  rw [h_sub, Complex.sub_re] at h_nonneg
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-- Functional calculus of f² = (Φ(f))² for real f -/
lemma boundedFunctionalCalculus_sq (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ s, |f s| ≤ M) :
    let f' : ℝ → ℂ := fun s => f s
    let f'2 : ℝ → ℂ := fun s => (f s)^2
    let hf' : ∃ M, ∀ s, ‖f' s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf_bdd
      exact ⟨M, fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM s⟩
    let hf'2 : ∃ M, ∀ s, ‖f'2 s‖ ≤ M := by
      obtain ⟨M, hM⟩ := hf_bdd
      refine ⟨M^2, fun s => ?_⟩
      simp only [f'2, norm_pow, norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM s) 2
    boundedFunctionalCalculus E hE f'2 hf'2 =
    (boundedFunctionalCalculus E hE f' hf') * (boundedFunctionalCalculus E hE f' hf') := by
  intro f' f'2 hf' hf'2
  ext ψ
  simp only [boundedFunctionalCalculus, ContinuousLinearMap.mul_apply]
  have hf'_meas : Measurable f' := Complex.measurable_ofReal.comp hf_meas
  have hf'2_meas : Measurable f'2 := hf'_meas.pow_const 2
  have hψf : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' ψ
  have hψf2 : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) f'2 :=
    functionalDomain_of_bounded E hE hE_univ f'2 hf'2_meas hf'2 ψ
  rw [← spectral_integral_bounded_eq E hE f'2 hf'2 ψ hψf2]
  have h_eq : f'2 = f' * f' := by ext s; simp [f', f'2, sq]
  have hψf_mul : ψ ∈ functionalDomain (spectral_scalar_measure E · hE) (f' * f') := by
    rw [← h_eq]; exact hψf2
  rw [spectral_integral_eq_of_eq_fun E hE f'2 (f' * f') h_eq ψ hψf2 hψf_mul]
  have hΦfψ : spectral_integral E hE f' ψ hψf ∈ functionalDomain (spectral_scalar_measure E · hE) f' :=
    functionalDomain_of_bounded E hE hE_univ f' hf'_meas hf' (spectral_integral E hE f' ψ hψf)
  rw [spectral_integral_mul E hE f' f' ψ hψf hΦfψ hψf_mul]
  rw [spectral_integral_bounded_eq E hE f' hf' (spectral_integral E hE f' ψ hψf) hΦfψ]
  rw [spectral_integral_bounded_eq E hE f' hf' ψ hψf]

/-- Integrability of f * ⟪E{·}ψ, ψ⟫ for bounded measurable f -/
lemma spectral_inner_mul_integrable (E : Set ℝ → H →L[ℂ] H) (hE : IsSpectralMeasure E)
    (hE_univ : E Set.univ = 1) (f : ℝ → ℂ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ s, ‖f s‖ ≤ M) (ψ : H) :
    Integrable (fun s => f s * ⟪(E {s}) ψ, ψ⟫_ℂ) (spectral_scalar_measure E ψ hE) := by
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ hE) :=
    spectral_scalar_measure_finite E hE hE_univ ψ
  have h_inner_int : Integrable (fun s => ⟪(E {s}) ψ, ψ⟫_ℂ) (spectral_scalar_measure E ψ hE) := by
    apply Integrable.of_bound (spectral_inner_measurable E hE hE_univ ψ).aestronglyMeasurable (‖ψ‖^2)
    apply Filter.Eventually.of_forall
    intro s
    calc ‖⟪(E {s}) ψ, ψ⟫_ℂ‖
        ≤ ‖(E {s}) ψ‖ * ‖ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * ‖ψ‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact spectral_measure_norm_le E hE {s} (measurableSet_singleton s) ψ
      _ = ‖ψ‖^2 := by ring
  obtain ⟨M, hM⟩ := hf_bdd
  apply Integrable.bdd_mul h_inner_int hf_meas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  exact hM

end FunctionalCalculus
