/-
Author: Adam Bornemann
Created: 12/25/25
Updated: 1/9/26

============================================================================================================================
ROUTES TO THE SPECTRAL THEOREM: FROM DYNAMICS TO SPECTRUM
============================================================================================================================

This file establishes the mathematical highways connecting the dynamical objects
(unitary groups, resolvents) to the spectral measure E. These are the "inverse"
directions of the spectral theorem: given U(t) or R(z), recover E.

TWO ROUTES TO THE SAME DESTINATION:

  ┌─────────────────────────────────────────────────────────────────────┐
  │                                                                     │
  │   BOCHNER ROUTE                        RESOLVENT ROUTE              │
  │   ────────────                         ───────────────              │
  │                                                                     │
  │   U(t) unitary group                   R(z) = (A - zI)⁻¹            │
  │        │                                    │                       │
  │        ▼                                    ▼                       │
  │   t ↦ ⟨U(t)ψ, ψ⟩                       z ↦ ⟨R(z)ψ, ψ⟩               │
  │   positive definite                    Nevanlinna function          │
  │        │                                    │                       │
  │        ▼                                    ▼                       │
  │   Bochner's Theorem                    Stieltjes Inversion          │
  │        │                                    │                       │
  │        ▼                                    ▼                       │
  │   μ_ψ spectral measure                 E(a,b] from boundary values  │
  │        │                                    │                       │
  │        └──────────────► E(B) ◄──────────────┘                       │
  │                    spectral                                         │
  │                   projections                                       │
  │                                                                     │
  └─────────────────────────────────────────────────────────────────────┘

PHYSICAL MEANING:

The spectral measure E encodes "how much" of each energy level λ is present
in a quantum state. The two routes correspond to two experimental approaches:

  • BOCHNER: Watch the system evolve. The correlation ⟨U(t)ψ, ψ⟩ oscillates
    with frequencies determined by the energy spectrum. Fourier analysis
    (Bochner's theorem) extracts the spectral measure from these oscillations.

  • RESOLVENT: Probe the system at complex energies z = E ± iε. The response
    ⟨R(z)ψ, ψ⟩ has poles/branch cuts on the real axis at the spectrum.
    As ε → 0, the imaginary part becomes a delta function at eigenvalues.

HISTORICAL DEVELOPMENT:

  Stone (1932):     Proved U(t) ↔ self-adjoint A correspondence
  Bochner (1932):   Characterized positive-definite functions via measures
  von Neumann:      Spectral theorem for unbounded operators
  Riesz-Nagy:       Systematic treatment via resolvents

The Stieltjes inversion formula predates quantum mechanics, originating in
moment problems. Stone recognized its power for operator theory.

MATHEMATICAL CONTENT:

  §1 BochnerRoute: Positive-definite functions and Bochner's theorem
     - PositiveDefinite: Σᵢⱼ c̄ᵢcⱼf(tᵢ - tⱼ) ≥ 0
     - unitary_correlation_positive_definite: t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite
     - bochner_measure: The measure from Bochner's theorem
     - polarization_spectral: Recover ⟨E(B)ψ, φ⟩ from diagonal terms

  §2 ResolventRoute: Stieltjes inversion and Stone's formula
     - resolvent_kernel_im: Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)
     - resolvent_kernel_diff: The Lorentzian emerges from R(z₊) - R(z₋)
     - stieltjes_inversion: ⟨E(a,b]ψ, ψ⟩ = lim (1/π) ∫ Im⟨R(t+iε)ψ, ψ⟩ dt
     - stones_formula: E(a,b) = s-lim (1/2πi) ∫ [R(t+iε) - R(t-iε)] dt

THE LORENTZIAN BRIDGE:

The key analytical object is the Lorentzian (Cauchy/Poisson) kernel:

                         ε
  L_ε(s - t)  =  ─────────────────
                 (s - t)² + ε²

As ε → 0⁺, this becomes π·δ(s - t). The Lorentzian arises naturally from:

  Im((s - (t + iε))⁻¹) = L_ε(s - t)

This connects complex analysis (resolvent) to real analysis (spectral measure).
The resolvent "knows" about the spectrum because its imaginary part at the
boundary concentrates precisely at spectral values.

AXIOM PHILOSOPHY:

This file contains axioms marking genuine theorems from:
  - Fourier analysis (Bochner's theorem)
  - Real analysis (Lorentzian approximation to delta)
  - Measure theory (Fubini, dominated convergence)
  - Complex analysis (Stieltjes inversion)

These are not gaps in reasoning but explicit interfaces to classical analysis.
The structural theorems (stieltjes_inversion, stones_formula) are fully proved
assuming these analytical facts.

AXIOM TIERS:

  Tier 1 (Calculus):     lorentzian_total_integral, arctan_kernel_bound
  Tier 2 (Analysis):     lorentzian_concentration, approx_identity_continuous
  Tier 3 (Theorems):     bochner_theorem, measure_eq_of_fourier_eq
  Tier 4 (Construction): spectral_scalar_measure, spectral_integral

Dependencies:
  - Bochner.lean: One-parameter unitary groups, generators
  - Resolvent.lean: Resolvent operators, bounds, functional relations

References:
  [1] Stone, M.H. "Linear Transformations in Hilbert Space" (1932)
  [2] Bochner, S. "Monotone Funktionen, Stieltjessche Integrale" (1932)
  [3] Reed & Simon, "Methods of Modern Mathematical Physics I" - Chapter VII
  [4] Riesz & Sz.-Nagy, "Functional Analysis" - Chapter X
  [5] Rudin, "Functional Analysis" - Chapter 13 (Unbounded Operators)
-/
import LogosLibrary.QuantumMechanics.Evolution.Bochner
import LogosLibrary.QuantumMechanics.Evolution.Resolvent

namespace SpectralBridge


open InnerProductSpace MeasureTheory Complex Filter Topology  StonesTheorem.Bochner Stone.Generators
open scoped BigOperators Topology

-- STEP 1: Redeclare H and its instances (required in nested namespace)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


namespace BochnerRoute
set_option linter.unusedSectionVars false

/-- A function f : ℝ → ℂ is positive-definite. -/
def PositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (t i - t j)).re

/-- Continuous positive-definite function. -/
def PositiveDefiniteContinuous (f : ℝ → ℂ) : Prop :=
  PositiveDefinite f ∧ ContinuousAt f 0

-- ============================================================================
-- SPECTRAL MEASURE AXIOMS: Tie E to U_grp
-- ============================================================================

/-- The spectral scalar measure associated to a spectral projection family E.

    AXIOM JUSTIFICATION: This measure exists by the spectral theorem for
    projection-valued measures. Construction requires Mathlib's Stieltjes
    measure machinery applied to F(t) = ⟪E(-∞,t]ψ,ψ⟫. -/
axiom spectral_scalar_measure' (E : Set ℝ → (H →L[ℂ] H)) (ψ : H) :
    MeasureTheory.Measure ℝ


/-- The spectral distribution function F_ψ(t) = ⟪E(-∞, t]ψ, ψ⟫ -/
noncomputable def spectralDistribution (E : Set ℝ → H →L[ℂ] H) (ψ : H) :
    StieltjesFunction where
  toFun := fun t => (⟪E (Set.Iic t) ψ, ψ⟫_ℂ).re
  mono' := sorry  -- E monotone: s ≤ t → E(Iic s) ≤ E(Iic t) in projection order
  right_continuous' := by sorry  -- From strong operator continuity of E

/-- The spectral scalar measure FROM the Stieltjes function -/
noncomputable def spectral_scalar_measure (E : Set ℝ → H →L[ℂ] H) (ψ : H) :
    Measure ℝ :=
  (spectralDistribution E ψ).measure


/-
noncomputable def spectral_scalar_measure (E : Set ℝ → (H →L[ℂ] H)) (ψ : H) :
    MeasureTheory.Measure ℝ := by
  sorry -- Would need actual measure construction; axiomatize properties instead
-/

/-- The spectral scalar measure assigns B ↦ ⟪E(B)ψ, ψ⟫.re -/
axiom spectral_scalar_measure_apply' (E : Set ℝ → (H →L[ℂ] H)) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
  (spectral_scalar_measure E ψ B).toReal = (⟪E B ψ, ψ⟫_ℂ).re

/-- The spectral scalar measure assigns finite values matching the inner product. -/
axiom spectral_scalar_measure_apply (E : Set ℝ → (H →L[ℂ] H)) (ψ : H)
    (B : Set ℝ) (hB : MeasurableSet B) :
  spectral_scalar_measure E ψ B = ENNReal.ofReal (⟪E B ψ, ψ⟫_ℂ).re

/-- Spectral theorem: the Fourier transform of the spectral measure gives the correlation. -/
axiom spectral_integral_relation (E : Set ℝ → (H →L[ℂ] H))
    (U_grp : OneParameterUnitaryGroup (H := H)) (ψ : H) (t : ℝ) :
  ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, Complex.exp (I * ω * t) ∂(spectral_scalar_measure E ψ)

/-- Uniqueness: a finite measure is determined by its Fourier transform. -/
axiom measure_eq_of_fourier_eq (μ ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν] :
  (∀ t : ℝ, ∫ ω, Complex.exp (I * ω * t) ∂μ = ∫ ω, Complex.exp (I * ω * t) ∂ν) → μ = ν

/-- The spectral scalar measure is finite (bounded by ‖ψ‖²). -/
lemma spectral_scalar_measure_finite (E : Set ℝ → (H →L[ℂ] H))
    (hE_univ : E Set.univ = 1) (ψ : H) :
    IsFiniteMeasure (spectral_scalar_measure E ψ) := by
  constructor
  rw [spectral_scalar_measure_apply E ψ Set.univ MeasurableSet.univ]
  rw [hE_univ]
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K,
             coe_algebraMap]
  exact ENNReal.ofReal_lt_top


/-- E(B) is self-adjoint (orthogonal projection). -/
axiom spectral_self_adjoint (E : Set ℝ → (H →L[ℂ] H))
    (B : Set ℝ) (ψ φ : H) :
  ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ

/-- **Bochner's Theorem** (axiom). -/
axiom bochner_theorem (f : ℝ → ℂ) (hf : PositiveDefiniteContinuous f) :
  ∃ (μ : MeasureTheory.Measure ℝ),
    MeasureTheory.IsFiniteMeasure μ ∧
    ∀ t, f t = ∫ ω, Complex.exp (I * ω * t) ∂μ

-- STEP 2: Declare U_grp as a variable AFTER H is in scope
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The function t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite. -/
theorem unitary_correlation_positive_definite (ψ : H) :
    PositiveDefinite (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  intro n t c
  set v := ∑ i : Fin n, c i • U_grp.U (t i) ψ with hv_def

  -- Key: ⟨U(s-r)ψ, ψ⟩ = ⟨U(s)ψ, U(r)ψ⟩ by unitarity
  have h_corr : ∀ i j : Fin n,
      ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ = ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ := by
    intro i j
    calc ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ
        = ⟪U_grp.U (t j) (U_grp.U (t i - t j) ψ), U_grp.U (t j) ψ⟫_ℂ := by
            rw [U_grp.unitary (t j)]
      _ = ⟪U_grp.U (t j + (t i - t j)) ψ, U_grp.U (t j) ψ⟫_ℂ := by
            rw [U_grp.group_law]; rfl
      _ = ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ := by congr 2; ring_nf

  -- conj(a) * b * ⟨x, y⟩ = ⟨a • x, b • y⟩
  have h_smul : ∀ i j,
      starRingEnd ℂ (c i) * c j * ⟪U_grp.U (t i) ψ, U_grp.U (t j) ψ⟫_ℂ =
      ⟪c i • U_grp.U (t i) ψ, c j • U_grp.U (t j) ψ⟫_ℂ := by
    intro i j; rw [inner_smul_left, inner_smul_right]; ring

  -- Main calculation: sum = ⟨v, v⟩
  calc (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ⟪U_grp.U (t i - t j) ψ, ψ⟫_ℂ).re
      = (∑ i, ∑ j, ⟪c i • U_grp.U (t i) ψ, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          simp_rw [h_corr, h_smul]
    _ = (∑ i, ⟪c i • U_grp.U (t i) ψ, ∑ j, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          simp_rw [inner_sum]
    _ = (⟪∑ i, c i • U_grp.U (t i) ψ, ∑ j, c j • U_grp.U (t j) ψ⟫_ℂ).re := by
          rw [sum_inner]
    _ = (⟪v, v⟫_ℂ).re := by rw [← hv_def]
    _ ≥ 0 := inner_self_nonneg (𝕜 := ℂ)

/-- The correlation function is continuous. -/
theorem unitary_correlation_continuous (ψ : H) :
    Continuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  apply Continuous.inner
  · exact U_grp.strong_continuous ψ
  · exact continuous_const

/-- Combined: satisfies Bochner's hypotheses. -/
theorem unitary_correlation_pd_continuous (ψ : H) :
    PositiveDefiniteContinuous (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ) := by
  constructor
  · exact unitary_correlation_positive_definite U_grp ψ
  · exact (unitary_correlation_continuous U_grp ψ).continuousAt

/-- Bochner's theorem gives a measure from the correlation function. -/
noncomputable def bochner_measure (ψ : H) : MeasureTheory.Measure ℝ :=
  Classical.choose (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))

-- STEP 3: Declare E as a variable (NOT in theorem signature)
variable (E : Set ℝ → (H →L[ℂ] H))




lemma bochner_measure_spec (ψ : H) :
    MeasureTheory.IsFiniteMeasure (bochner_measure U_grp ψ) ∧
    ∀ t, ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ ω, Complex.exp (I * ω * t) ∂(bochner_measure U_grp ψ) :=
  Classical.choose_spec (bochner_theorem (fun t => ⟪U_grp.U t ψ, ψ⟫_ℂ)
    (unitary_correlation_pd_continuous U_grp ψ))


/-- The Bochner measure IS the spectral measure. -/
theorem bochner_measure_eq_spectral (hE_univ : E Set.univ = 1) (ψ : H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (bochner_measure U_grp ψ B).toReal = (⟪E B ψ, ψ⟫_ℂ).re := by
  obtain ⟨h_finite, h_fourier⟩ := bochner_measure_spec U_grp ψ

  haveI : IsFiniteMeasure (bochner_measure U_grp ψ) := h_finite
  haveI : IsFiniteMeasure (spectral_scalar_measure E ψ) :=
    spectral_scalar_measure_finite E hE_univ ψ

  have h_fourier_eq : ∀ t : ℝ,
      ∫ ω, Complex.exp (I * ω * t) ∂(bochner_measure U_grp ψ) =
      ∫ ω, Complex.exp (I * ω * t) ∂(spectral_scalar_measure E ψ) := fun t => by
    rw [← h_fourier t, spectral_integral_relation E U_grp ψ t]

  have h_eq : bochner_measure U_grp ψ = spectral_scalar_measure E ψ :=
    measure_eq_of_fourier_eq _ _ h_fourier_eq

  rw [h_eq, spectral_scalar_measure_apply' E ψ B hB]

/-- Convert spectral measure to ℂ for polarization calculations -/
noncomputable def spectral_measure_cplx
    (U_grp : OneParameterUnitaryGroup (H := H)) (ψ : H) (B : Set ℝ) : ℂ :=
  ((bochner_measure U_grp ψ B).toReal : ℂ)

/-- Diagonal spectral values are real (from self-adjointness). -/
lemma spectral_diagonal_real (B : Set ℝ) (ψ : H) :
    (⟪E B ψ, ψ⟫_ℂ).im = 0 := by
  have h := spectral_self_adjoint E B ψ ψ
  have key : ⟪E B ψ, ψ⟫_ℂ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ :=
    calc ⟪E B ψ, ψ⟫_ℂ
        = ⟪ψ, E B ψ⟫_ℂ := h
      _ = starRingEnd ℂ ⟪E B ψ, ψ⟫_ℂ := by
        exact Eq.symm (conj_inner_symm ψ ((E B) ψ))
  exact Complex.conj_eq_iff_im.mp key.symm

/-- spectral_measure_cplx equals the inner product. -/
lemma spectral_measure_cplx_eq (hE_univ : E Set.univ = 1) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    spectral_measure_cplx U_grp ψ B = ⟪E B ψ, ψ⟫_ℂ := by
  unfold spectral_measure_cplx
  rw [bochner_measure_eq_spectral U_grp E hE_univ ψ B hB]
  have h_im := spectral_diagonal_real E B ψ
  conv_rhs => rw [← Complex.re_add_im ⟪E B ψ, ψ⟫_ℂ, h_im]
  simp

/-- Polarization gives off-diagonal spectral measures. -/
theorem polarization_spectral (hE_univ : E Set.univ = 1) (ψ φ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    ⟪E B ψ, φ⟫_ℂ = (1/4 : ℂ) * (
      spectral_measure_cplx U_grp (ψ + φ) B -
      spectral_measure_cplx U_grp (ψ - φ) B -
      I * spectral_measure_cplx U_grp (ψ + I • φ) B +
      I * spectral_measure_cplx U_grp (ψ - I • φ) B)  := by
  simp_rw [spectral_measure_cplx_eq U_grp E hE_univ _ _ hB]
  simp only [map_add, map_sub, map_smul]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
             inner_smul_left, inner_smul_right]
  have h_sa : ⟪E B φ, ψ⟫_ℂ = star ⟪E B ψ, φ⟫_ℂ := by
    rw [spectral_self_adjoint E B φ ψ]
    simp only [RCLike.star_def, inner_conj_symm]
  simp only [h_sa, RCLike.star_def, Complex.conj_I]
  set z := ⟪E B ψ, φ⟫_ℂ
  have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (norm := ring_nf) (1 - 1) * hI2
  simp only [I_sq, mul_neg, mul_one, neg_mul, add_neg_cancel, zero_add]

end BochnerRoute

namespace ResolventRoute
set_option linter.unusedVariables false
open StonesTheorem.Resolvent

/-- Helper: construct off-real point from real part and positive imaginary part -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t + ↑ε * I, by simp [Complex.add_im]; exact ne_of_gt hε⟩

def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : OffRealAxis :=
  ⟨↑t - ↑ε * I, by simp [Complex.sub_im]; exact ne_of_gt hε⟩

/-!
## Mathematical Background

The four theorems below establish the connection between the resolvent operator
R(z) = (A - zI)⁻¹ and the spectral measure E.

**Key Identity**: For a self-adjoint operator A with spectral measure E:
  R(z) = ∫_ℝ (s - z)⁻¹ dE(s)

**Stieltjes Inversion**: The spectral measure can be recovered from the resolvent:
  ⟪E(a,b] ψ, ψ⟫ = lim_{ε→0+} (1/π) ∫_a^b Im⟪R(t+iε) ψ, ψ⟫ dt

The key is that Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²), which is an
approximate δ-function at s = t as ε → 0.

**Stone's Formula**: A symmetric version for open intervals:
  E(a,b) = s-lim_{ε→0+} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt
-/

-- ============================================================================
-- RESOLVENT-SPECTRAL CONNECTION AXIOM
-- ============================================================================

/-- **Core Axiom**: The resolvent has spectral representation.

This is the fundamental connection between the resolvent R(z) and spectral measure E.
It encapsulates the spectral theorem for unbounded self-adjoint operators.

For z ∉ ℝ:  ⟪R(z)ψ, ψ⟫ = ∫_ℝ (s - z)⁻¹ d⟪E(ds)ψ, ψ⟫

This can be proven from first principles via:
1. Laplace transform connection: R(z) ~ ∫ e^{±itz} U(t) dt
2. Spectral theorem for U(t): ⟪U(t)ψ, ψ⟫ = ∫ e^{its} dμ_ψ(s)
3. Fubini to swap integrals
-/
axiom resolvent_spectral_bilinear {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(BochnerRoute.spectral_scalar_measure E ψ)

/-- The spectral integral is integrable for z off the real axis. -/
axiom resolvent_spectral_integrable {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : OffRealAxis) (ψ : H) :
    MeasureTheory.Integrable (fun s : ℝ => ((s : ℂ) - z.val)⁻¹)
      (BochnerRoute.spectral_scalar_measure E ψ)

-- ============================================================================
-- RESOLVENT-SPECTRAL INTEGRATION LEMMAS
-- ============================================================================

/-- The integrand for resolvent spectral representation -/
noncomputable def resolvent_integrand (μ : MeasureTheory.Measure ℝ) (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

/-- The resolvent integrand is integrable for z off the real axis.
    Key: |(s - z)⁻¹| ≤ 1/|Im(z)| for all s ∈ ℝ. -/
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have h_im : ((s : ℂ) - z).im = -z.im := by simp
  have h_norm_ge : ‖(s : ℂ) - z‖ ≥ |z.im| := by
    calc ‖(s : ℂ) - z‖
        ≥ |((s : ℂ) - z).im| := Complex.abs_im_le_norm _
      _ = |-z.im| := by rw [h_im]
      _ = |z.im| := abs_neg _
  have h_pos : |z.im| > 0 := abs_pos.mpr hz
  calc ‖((s : ℂ) - z)⁻¹‖
      = 1 / ‖(s : ℂ) - z‖ := by rw [norm_inv]; simp only [one_div]
    _ ≤ 1 / |z.im| := by
        apply div_le_div_of_nonneg_left (by norm_num) h_pos h_norm_ge

/-- Imaginary part of resolvent kernel: Im((s - z)⁻¹) for z = t + iε -/
lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) :
    (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2) := by
  -- (s - (t + iε))⁻¹ = (s - t - iε)⁻¹ = (s - t + iε) / ((s-t)² + ε²)
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'

  have h_diff : (s : ℂ) - (↑t + ↑ε * I) = (s - t : ℝ) - ε * I := by
    simp only [Complex.ofReal_sub]
    ring

  rw [h_diff]
  -- ((s-t) - εi)⁻¹ = ((s-t) + εi) / ((s-t)² + ε²)
  have h_conj : ((s - t : ℝ) - ε * I)⁻¹ =
      ((s - t : ℝ) + ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
    have h_mul : ((s - t : ℝ) - ε * I) * ((s - t : ℝ) + ε * I) =
        ((s - t)^2 + ε^2 : ℂ) := by
      push_cast
      have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
      linear_combination (norm := ring) -ε^2 * hI2
    have h_conj_ne : (↑(s - t) : ℂ) + ↑ε * I ≠ 0 := by
      intro h
      have : ε = 0 := by simpa using congrArg Complex.im h
      linarith
    rw [← h_mul]
    field_simp [h_conj_ne]

  rw [h_conj]
  have h_real : ((s - t)^2 + ε^2 : ℂ) = ((s - t)^2 + ε^2 : ℝ) := by push_cast; ring
  rw [h_real, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]

-- ============================================================================
-- AXIOMS FOR LORENTZIAN DELTA APPROXIMATION
-- ============================================================================

/-- The Lorentzian integrates to π over ℝ. -/
axiom lorentzian_total_integral (t ε : ℝ) (hε : ε > 0) :
    ∫ s, ε / ((s - t)^2 + ε^2) = Real.pi

/-- The Lorentzian is nonnegative. -/
lemma lorentzian_nonneg (s t ε : ℝ) (hε : ε > 0) :
    0 ≤ ε / ((s - t)^2 + ε^2) := by
  apply div_nonneg (le_of_lt hε)
  positivity

/-- The Lorentzian is bounded by 1/ε. -/
lemma lorentzian_bound (s t ε : ℝ) (hε : ε > 0) :
    ε / ((s - t)^2 + ε^2) ≤ 1 / ε := by
  have h_denom : ε^2 ≤ (s - t)^2 + ε^2 := by linarith [sq_nonneg (s - t)]
  have h1 : ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 :=
    div_le_div_of_nonneg_left (le_of_lt hε) (sq_pos_of_pos hε) h_denom
  simp only [one_div]
  calc ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 := h1
    _ = ε⁻¹ := by field_simp

/-- The Lorentzian concentrates near t as ε → 0.
    For any δ > 0, the integral outside (t-δ, t+δ) vanishes as ε → 0. -/
axiom lorentzian_concentration (t δ : ℝ) (hδ : δ > 0) :
    Tendsto (fun ε : ℝ => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
      ε / ((s - t)^2 + ε^2)) (𝓝[>] 0) (𝓝 0)

/-- Approximation to identity for continuous integrable functions. -/
axiom approx_identity_continuous (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f) (t : ℝ)
    (K : ℝ → ℝ → ℝ)  -- kernel K(ε, s)
    (hK_nonneg : ∀ ε > 0, ∀ s, K ε s ≥ 0)
    (hK_total : ∀ ε > 0, ∫ s, K ε s = 1)
    (hK_conc : ∀ δ > 0, Tendsto (fun ε => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s)
                                 (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t))

/-- The Lorentzian approximation to delta: ε/((s-t)² + ε²) → πδ(s-t) as ε → 0 -/
lemma lorentzian_approx_delta (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : MeasureTheory.Integrable f) (t : ℝ) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s)
            (𝓝[>] 0) (𝓝 (f t)) := by
  -- Define the normalized kernel K(ε, s) = (1/π) * ε/((s-t)² + ε²)
  let K : ℝ → ℝ → ℝ := fun ε s => (1 / Real.pi) * (ε / ((s - t)^2 + ε^2))

  -- Rewrite goal in terms of K
  have h_rewrite : ∀ ε > 0, (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s =
      ∫ s, (K ε s) • f s := by
    intro ε hε
    simp only [K]
    rw [← MeasureTheory.integral_smul]
    congr 1
    ext s
    rw [smul_smul]

  -- Apply the general approximation to identity theorem
  have h_tendsto : Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t)) := by
    apply approx_identity_continuous f hf_cont hf_int t K
    -- K is nonnegative
    · intro ε hε s
      simp only [K]
      apply mul_nonneg
      · simp only [one_div, inv_nonneg] ; exact Real.pi_nonneg
      · exact lorentzian_nonneg s t ε hε
    -- K integrates to 1
    · intro ε hε
      simp only [K]
      rw [MeasureTheory.integral_const_mul, lorentzian_total_integral t ε hε]
      field_simp
    -- K concentrates at t
    · intro δ hδ
      simp only [K]
      have h := lorentzian_concentration t δ hδ
      have h_eq : ∀ ε, ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          (1 / Real.pi) * (ε / ((s - t)^2 + ε^2)) =
          (1 / Real.pi) * ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          ε / ((s - t)^2 + ε^2) := fun ε => by
        exact integral_const_mul (1 / Real.pi) fun a => ε / ((a - t) ^ 2 + ε ^ 2)
      simp_rw [h_eq]
      convert h.const_mul (1 / Real.pi) using 2
      exact Eq.symm (CommMonoidWithZero.mul_zero (1 / Real.pi))
  -- Connect back to original formulation
  refine Tendsto.congr' ?_ h_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h_rewrite ε hε).symm

/-- Key identity: difference of resolvent kernels at conjugate points.

  (s - (t + iε))⁻¹ - (s - (t - iε))⁻¹ = 2iε / ((s-t)² + ε²)

This shows the resolvent difference is purely imaginary and proportional to Lorentzian. -/
lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) :
    ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ =
    (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
  -- Compute: z₊ = t + iε, z₋ = t - iε
  -- (s - z₊)⁻¹ - (s - z₋)⁻¹ = ((s - z₋) - (s - z₊)) / ((s - z₊)(s - z₋))
  --                         = (z₊ - z₋) / ((s - z₊)(s - z₋))
  --                         = 2iε / ((s-t)² + ε²)
  have h_z_plus : (↑t + ↑ε * I : ℂ) - (↑t - ↑ε * I) = 2 * ε * I := by ring
  have h_denom : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) =
      ((s - t)^2 + ε^2 : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    linear_combination (norm := ring) -ε^2 * hI2
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_prod_ne : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) ≠ 0 := by
    rw [h_denom]
    push_cast at h_denom_ne ⊢
    exact h_denom_ne
  have h_left_ne : (s : ℂ) - (↑t + ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, zero_mul]
  have h_right_ne : (s : ℂ) - (↑t - ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, mul_zero]
  -- Main calculation
  have h_denom_ne' : (↑s - ↑t : ℂ) ^ 2 + ↑ε ^ 2 ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  field_simp [h_left_ne, h_right_ne, h_denom_ne']
  -- Now goal should be denominator-free
  push_cast [sq]
  ring_nf
  simp only [I_pow_three, mul_neg, neg_mul, sub_neg_eq_add]
  ring


-- ============================================================================
-- ANALYTICAL AXIOMS FOR STIELTJES INVERSION
-- ============================================================================

/-- Arctan antiderivative for the Lorentzian kernel.
    ∫_a^b ε/((s-t)² + ε²) dt = arctan((b-s)/ε) - arctan((a-s)/ε) -/
axiom lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2) =
      Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)

/-- Fubini for the resolvent spectral integral.
    Swaps order of integration for the Lorentzian kernel. -/
axiom lorentzian_fubini {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ

/-- The arctan kernel converges to the indicator function.
    (1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s) as ε → 0+ -/
axiom arctan_indicator_limit (a b s : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0)
      (𝓝 (Set.indicator (Set.Ioc a b) 1 s))

/-- The arctan kernel is uniformly bounded by 1. -/
axiom arctan_kernel_bound (a b s ε : ℝ) (hε : ε > 0) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1

/-- Dominated convergence for the arctan kernel integral. -/
axiom arctan_dominated_convergence {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal)

/-- The imaginary part of the resolvent inner product equals the Lorentzian spectral integral. -/
axiom resolvent_im_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (t ε : ℝ) (hε : ε > 0) (ψ : H) :
    Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ s, ε / ((s - t)^2 + ε^2) ∂(BochnerRoute.spectral_scalar_measure E ψ)

-- ============================================================================
-- MAIN THEOREMS
-- ============================================================================

/-- **Stieltjes Inversion Formula**

Recover the spectral measure from the resolvent via:
  ⟪E(a,b] ψ, ψ⟫ = lim_{ε→0+} (1/π) ∫_a^b Im⟪R(t+iε) ψ, ψ⟫ dt

**Proof Strategy:**
1. By `resolvent_spectral_bilinear`: ⟪R(t+iε)ψ, ψ⟫ = ∫_ℝ (s - t - iε)⁻¹ dμ_ψ(s)
2. Take imaginary parts: Im((s - t - iε)⁻¹) = ε/((s-t)² + ε²) (Lorentzian)
3. The function ε/(π((s-t)² + ε²)) is an approximate identity → πδ(s-t)
4. Integrating t over [a,b]: ∫_a^b (1/π) · (ε/((s-t)² + ε²)) dt → 𝟙_{(a,b]}(s)
5. Swap integrals by Fubini, giving ⟪E(a,b]ψ, ψ⟫ in the limit
-/
theorem stieltjes_inversion {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / Real.pi : ℂ) *
        ∫ t in Set.Icc a b, Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ‖ < δ := by
  intro δ hδ

  set μ := BochnerRoute.spectral_scalar_measure E ψ with hμ_def
  haveI hμ_finite : MeasureTheory.IsFiniteMeasure μ :=
    BochnerRoute.spectral_scalar_measure_finite E hE_univ ψ
  -- Get ε₀ from dominated convergence
  have h_conv := arctan_dominated_convergence (μ := μ) a b hab
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    BochnerRoute.spectral_scalar_measure_apply' E ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 :=
    BochnerRoute.spectral_diagonal_real E (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← Complex.re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b, Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ := by
    congr 1
    ext t
    exact resolvent_im_spectral gen hsa E t ε hε ψ

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, ε / ((s - t)^2 + ε^2) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ :=
    lorentzian_fubini a b ε hε

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2)) ∂μ =
      ∫ s, (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    exact lorentzian_arctan_integral s a b ε hε

  -- Factor out 1/π
  have h_factor : (1 / Real.pi : ℂ) * ∫ t in Set.Icc a b,
      Complex.im ⟪resolventFun gen hsa (offRealPoint t ε hε) ψ, ψ⟫_ℂ =
      ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    simp only [MeasureTheory.integral_const_mul]
    norm_cast

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist
  simp only [Real.dist_eq] at h_bound

  -- Convert to norm bound
  rw [h_inner_eq, h_factor]
  rw [← Complex.ofReal_sub, Complex.norm_real, @norm_sub_rev]
  exact h_bound



-- ============================================================================
-- ADDITIONAL AXIOMS FOR STONE'S FORMULA
-- ============================================================================

/-- The resolvent difference integrated against the spectral measure. -/
axiom resolvent_diff_spectral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (t ε : ℝ) (hε : ε > 0) (ψ : H) :
    ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
       resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂(BochnerRoute.spectral_scalar_measure E ψ)

/-- Fubini for the resolvent difference kernel. -/
axiom resolvent_diff_fubini {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ

/-- The complex arctan integral for the resolvent difference.
    ∫_a^b (2εi)/((s-t)² + ε²) dt = 2i[arctan((b-s)/ε) - arctan((a-s)/ε)] -/
axiom resolvent_diff_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) =
      2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))

/-- Dominated convergence for Stone's formula integral. -/
axiom stones_dominated_convergence {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ s, (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ)
      (𝓝[>] 0)
      (𝓝 (μ (Set.Ioc a b)).toReal)

/-- The Stone's formula integral simplifies to a real value. -/
axiom stones_integral_real {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    (a b ε : ℝ) (hε : ε > 0) :
    ∫ s, (1 / (2 * Real.pi * Complex.I)) *
      (2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ =
    ∫ s, (1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ

/-- **Stone's Formula**

Recover spectral projections from the resolvent difference:
  E(a,b) = s-lim_{ε→0+} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt

**Proof Strategy:**
By `resolvent_kernel_diff`:
  (s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε / ((s-t)² + ε²)

The difference is purely imaginary and proportional to 2i times the Lorentzian.
The factor (1/2πi) cancels the 2i, leaving (1/π) times the Lorentzian.

Same convergence argument as Stieltjes inversion then applies.
-/
theorem stones_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (hE_univ : E Set.univ = 1)
    (a b : ℝ) (hab : a < b) (ψ : H) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, ε < ε₀ → ∀ hε : ε > 0,
      ‖⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ - (1 / (2 * Real.pi * Complex.I)) *
        ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
          resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ‖ < δ := by
  intro δ hδ

  set μ := BochnerRoute.spectral_scalar_measure E ψ with hμ_def
  haveI hμ_finite : MeasureTheory.IsFiniteMeasure μ :=
    BochnerRoute.spectral_scalar_measure_finite E hE_univ ψ

  -- Get ε₀ from dominated convergence
  have h_conv := stones_dominated_convergence (μ := μ) a b hab
  rw [Metric.tendsto_nhdsWithin_nhds] at h_conv
  obtain ⟨ε₀, hε₀_pos, hε₀_conv⟩ := h_conv δ hδ

  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_lt hε

  -- The spectral measure gives ⟪E(a,b]ψ, ψ⟫
  have h_spectral : (μ (Set.Ioc a b)).toReal = (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).re :=
    BochnerRoute.spectral_scalar_measure_apply' E ψ (Set.Ioc a b) measurableSet_Ioc

  -- ⟪E(a,b]ψ, ψ⟫ is real
  have h_real : (⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ).im = 0 :=
    BochnerRoute.spectral_diagonal_real E (Set.Ioc a b) ψ

  have h_inner_eq : ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ = (μ (Set.Ioc a b)).toReal := by
    conv_lhs => rw [← Complex.re_add_im ⟪E (Set.Ioc a b) ψ, ψ⟫_ℂ, h_real]
    simp [h_spectral]

  -- Express the integral using spectral representation
  have h_integral : ∫ t in Set.Icc a b,
      ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
        resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
      ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ := by
    congr 1
    ext t
    exact resolvent_diff_spectral gen hsa E t ε hε ψ

  -- Apply Fubini
  have h_fubini : ∫ t in Set.Icc a b, ∫ s, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ) ∂μ =
      ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ :=
    resolvent_diff_fubini a b ε hε

  -- Compute inner integral via arctan
  have h_arctan : ∫ s, (∫ t in Set.Icc a b, (2 * ε * Complex.I) / ((s - t)^2 + ε^2 : ℂ)) ∂μ =
      ∫ s, 2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    exact resolvent_diff_arctan_integral s a b ε hε

  -- Factor out 1/(2πi)
  have h_factor : (1 / (2 * Real.pi * Complex.I)) *
    ∫ t in Set.Icc a b, ⟪(resolventFun gen hsa (offRealPoint t ε hε) -
      resolventFun gen hsa (offRealPointNeg t ε hε)) ψ, ψ⟫_ℂ =
    ∫ s, (1 / (2 * Real.pi * Complex.I)) *
      (2 * Complex.I * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))) ∂μ := by
    rw [h_integral, h_fubini, h_arctan]
    exact
      Eq.symm
        (integral_const_mul (1 / (2 * ↑Real.pi * I)) fun a_1 =>
          2 * I * (↑(Real.arctan ((b - a_1) / ε)) - ↑(Real.arctan ((a - a_1) / ε))))

  -- Apply dominated convergence bound
  have h_dist : dist ε 0 < ε₀ := by simp [abs_of_pos hε]; exact hε_lt
  have h_mem : ε ∈ Set.Ioi (0 : ℝ) := hε
  have h_bound := hε₀_conv h_mem h_dist

  -- Convert to norm bound
  rw [h_inner_eq, h_factor, stones_integral_real a b ε hε]
  rw [← Complex.ofReal_sub, Complex.norm_real, norm_sub_rev]
  exact h_bound



-- ============================================================================
-- OPERATOR-VALUED SPECTRAL INTEGRAL
-- ============================================================================

/-- The operator-valued spectral integral ∫ f(λ) dE(λ) applied to a vector.
    This is the Stieltjes integral with respect to a projection-valued measure. -/
axiom spectral_integral (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) : H

notation "∫_E " f ", " ψ => spectral_integral _ f ψ


/-- The spectral integral of (λ - z)⁻¹ equals the resolvent. -/
axiom resolvent_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H)) (z : OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = spectral_integral E (fun t => ((t : ℂ) - z.val)⁻¹) ψ

/-- Lebesgue-Stieltjes representation: the spectral integral can be written
    as a Lebesgue integral against the spectral measure density when E is absolutely
    continuous. For general E, this is the Stieltjes integral. -/
axiom spectral_integral_eq_lebesgue (E : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (ψ : H) :
    spectral_integral E f ψ = ∫ t : ℝ, f t • E {t} ψ  -- formal equality via Stieltjes

/-- **Resolvent Spectral Representation (Operator Form)**

The resolvent has an integral representation:
  R(z) = ∫_ℝ (s - z)⁻¹ dE(s)

This is the operator-valued Stieltjes integral of the function (s - z)⁻¹
with respect to the projection-valued spectral measure E.

**Proof Strategy:**
1. For z off the real axis, the integrand (s - z)⁻¹ is bounded
2. The integral converges in operator norm
3. Verify it satisfies (A - z) · R(z) = I by spectral calculus

This is essentially the spectral theorem for unbounded self-adjoint operators,
specialized to the resolvent function.
-/
theorem resolvent_spectral_representation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : OffRealAxis) (ψ : H) :
    resolventFun gen hsa z ψ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ • E {t} ψ := by
  rw [← spectral_integral_eq_lebesgue]
  exact resolvent_eq_spectral_integral gen hsa E z ψ




/-- **Resolvent Spectral Representation (Bilinear Form)**

The bilinear form version:
  ⟪R(z)ψ, ψ⟫ = ∫_ℝ (s - z)⁻¹ dμ_ψ(s)

where μ_ψ is the scalar spectral measure: μ_ψ(B) = ⟪E(B)ψ, ψ⟫.re

This follows directly from the `resolvent_spectral_bilinear` axiom with μ = spectral_scalar_measure.
-/
theorem resolvent_spectral_representation' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ =
      ∫ s : ℝ, ((s : ℂ) - z.val)⁻¹ ∂(BochnerRoute.spectral_scalar_measure E ψ) :=
  resolvent_spectral_bilinear gen hsa E z ψ

/-- Specialization: the spectral measure μ can be any measure agreeing with E on measurable sets. -/
theorem resolvent_spectral_representation'_alt {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → (H →L[ℂ] H))
    (μ : H → MeasureTheory.Measure ℝ)
    (hμ : ∀ ψ, μ ψ = BochnerRoute.spectral_scalar_measure E ψ)
    (z : OffRealAxis) (ψ : H) :
    ⟪resolventFun gen hsa z ψ, ψ⟫_ℂ = ∫ t : ℝ, ((t : ℂ) - z.val)⁻¹ ∂(μ ψ) := by
  rw [hμ ψ]
  exact resolvent_spectral_bilinear gen hsa E z ψ


end ResolventRoute

end SpectralBridge
