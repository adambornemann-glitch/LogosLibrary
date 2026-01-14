/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Operators

/-!
# Spectral Theory of the Dirac Operator

This file develops the spectral decomposition of the Dirac Hamiltonian via
functional calculus, including the electron/positron projections and the
fundamental result that these subspaces are orthogonal and complete.

## Main definitions

### Spectrum and Gap
* `diracSpectrum`: The set (-∞, -mc²] ∪ [mc², ∞)
* `diracGap`: The forbidden energy region (-mc², mc²)

### Spectral Projections
* `electronProjection`: Spectral projection E([mc², ∞)) onto positive energies
* `positronProjection`: Spectral projection E((-∞, -mc²]) onto negative energies

### Spectral Data
* `DiracSpectralData`: Complete spectral decomposition bundling the Hamiltonian,
  unitary group, generator, and spectral measure

### Energy Functions
* `relativisticEnergy`: E(p) = √((pc)² + (mc²)²)
* `positiveEnergy`: E₊(p) = +√((pc)² + (mc²)²)
* `negativeEnergy`: E₋(p) = -√((pc)² + (mc²)²)

## Main results

* `electron_positron_orthogonal`: E₊ E₋ = 0
* `dirac_spectral_gap_zero`: E((-mc², mc²)) = 0
* `electron_positron_complete`: E₊ + E₋ = 1 (for m > 0)
* `dirac_evolution_unitary`: U(t) is unitary for all t
* `energy_geq_rest_mass`: |E(p)| ≥ mc²

## Physical interpretation

### The Mass Gap
The spectrum of H_D has a gap of width 2mc² centered at zero. No stationary
states exist with energy in (-mc², mc²). This gap:
- Separates particles (E > mc²) from antiparticles (E < -mc²)
- Determines the threshold for pair creation: γ → e⁺e⁻ requires Eᵧ ≥ 2mc²
- Is responsible for the stability of matter (electrons can't fall into negative energies)

### Electron and Positron Subspaces
The spectral projections decompose the Hilbert space:
  H = H₊ ⊕ H₋,  where H₊ = E([mc², ∞))H, H₋ = E((-∞, -mc²])H

- H₊ is the electron (positive energy) subspace
- H₋ is the positron (negative energy) subspace
- These are orthogonal and together span all of H

### Time Evolution
The unitary group U(t) = e^{-itH_D/ℏ} preserves the electron/positron
decomposition: an initial electron state remains an electron state.
This is because [U(t), E₊] = 0.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapters 1, 4
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. I §VIII

## Tags

spectral theory, spectral gap, electron, positron, functional calculus,
spectral projection, time evolution
-/

namespace SpectralTheory

open MeasureTheory InnerProductSpace Complex
open Dirac.Matrices Dirac.Operator QuantumMechanics.Cayley SpectralBridge QuantumMechanics.Generators FunctionalCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



/-- Abstract specification of Dirac matrices -/
structure DiracMatrices where
  /-- Spatial Dirac matrices α = (α₁, α₂, α₃), coupling momentum to spinor space. -/
  alpha : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  /-- Mass matrix β, distinguishing particle from antiparticle components. -/
  beta : Matrix (Fin 4) (Fin 4) ℂ
  /-- αᵢ² = I: each αᵢ is an involution with eigenvalues ±1. -/
  alpha_sq : ∀ i, alpha i * alpha i = 1
  /-- β² = I: the mass matrix is an involution. -/
  beta_sq : beta * beta = 1
  /-- {αᵢ, αⱼ} = 0 for i ≠ j: distinct spatial matrices anticommute.
      This ensures (α·p)² = p₁² + p₂² + p₃² with no cross terms. -/
  alpha_anticommute : ∀ i j, i ≠ j → alpha i * alpha j + alpha j * alpha i = 0
  /-- {αᵢ, β} = 0: momentum and mass terms anticommute.
      This ensures H_D² has no αᵢβ cross terms. -/
  alpha_beta_anticommute : ∀ i, alpha i * beta + beta * alpha i = 0
  /-- αᵢ† = αᵢ: Hermiticity ensures the kinetic term is symmetric. -/
  alpha_hermitian : ∀ i, (alpha i).conjTranspose = alpha i
  /-- β† = β: Hermiticity ensures the mass term is symmetric. -/
  beta_hermitian : beta.conjTranspose = beta


/-- Physical constants for the Dirac equation -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ: the quantum of action. -/
  hbar : ℝ
  /-- Speed of light c: the relativistic velocity scale. -/
  c : ℝ
  /-- Particle rest mass m: determines the spectral gap. -/
  m : ℝ
  /-- ℏ > 0: required for non-trivial quantum dynamics. -/
  hbar_pos : hbar > 0
  /-- c > 0: required for Lorentz signature. -/
  c_pos : c > 0
  /-- m ≥ 0: negative mass is unphysical. Zero mass is allowed (Weyl fermions). -/
  m_nonneg : m ≥ 0

/-- Rest mass energy E₀ = mc² -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2


/-- The Dirac Hamiltonian as an unbounded operator on a Hilbert space -/
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    DiracOperator H where
  /-- Physical constants ℏ, c, m for this particle. -/
  constants : DiracConstants
  /-- Dirac matrices satisfying the Clifford algebra. -/
  matrices : DiracMatrices
  /-- H_D is symmetric: ⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ for ψ, φ in the domain.
      This follows from Hermiticity of α and β; it's the first step toward self-adjointness. -/
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  /-- The domain is dense in H.
      Required for the closure of H_D to be defined on a meaningful subspace. -/
  domain_dense : Dense (domain : Set H)

/-! ## Spectrum and Spectral Gap -/

/-- The spectrum of the free Dirac operator: two half-lines separated by a gap.

  σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)

The gap (-mc², mc²) contains no spectrum for the free particle. Interactions
(external potentials) can create bound states in the gap. -/
def diracSpectrum (κ : DiracConstants) : Set ℝ :=
  Set.Iic (-κ.restEnergy) ∪ Set.Ici κ.restEnergy

/-- The spectral gap: the open interval (-mc², mc²) of forbidden energies.

No stationary states of the free Dirac equation have energy in this range.
The width of the gap is 2mc² ≈ 1.02 MeV for electrons. -/
def diracGap (κ : DiracConstants) : Set ℝ :=
  Set.Ioo (-κ.restEnergy) κ.restEnergy


/-! ## Spectral Gap Axioms -/

/-- **Axiom**: Every point in the spectral gap has a bounded resolvent.

For E ∈ (-mc², mc²), the operator (H_D - E) has a bounded inverse.
This is equivalent to saying E is in the resolvent set ρ(H_D). -/
axiom dirac_gap_in_resolvent (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (hm : H_D.constants.m > 0) :
    ∀ E ∈ diracGap H_D.constants,
      ∃ (R : H →L[ℂ] H), ∀ (ψ : H_D.domain), R (H_D.op ψ - E • (ψ : H)) = ψ

/-- **Axiom**: The spectral measure vanishes on the gap.

For any measurable B ⊆ (-mc², mc²), the spectral projection E(B) = 0.
This is the spectral-theoretic statement that the gap contains no spectrum. -/
axiom dirac_spectrum_eq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H)
    (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp)
    (hgen : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    ∀ B ⊆ diracGap H_D.constants, MeasurableSet B → E B = 0


/-! ## Complete Spectral Data -/

/-- Complete spectral data for a Dirac operator.

This bundles together all the ingredients of the spectral theorem:
- The Hamiltonian with its physical constants
- The unitary group U(t) = e^{-itH_D/ℏ}
- The self-adjoint generator
- The spectral measure E : Borel(ℝ) → Projections(H)

The spectral theorem guarantees these exist and are related by:
  U(t) = ∫ e^{its} dE(s)  and  H_D = ∫ s dE(s) -/
structure DiracSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Dirac Hamiltonian with physical constants and domain. -/
  hamiltonian : DiracHamiltonian H
  /-- The strongly continuous unitary group generated by H_D. -/
  U_grp : OneParameterUnitaryGroup (H := H)
  /-- The infinitesimal generator of U_grp (related to H_D by factors of i and ℏ). -/
  gen : Generator U_grp
  /-- The generator is self-adjoint, enabling the spectral theorem. -/
  gen_sa : gen.IsSelfAdjoint
  /-- The spectral measure: E(B) projects onto states with energy in B. -/
  E : Set ℝ → H →L[ℂ] H
  /-- E is the spectral measure associated to gen via the spectral theorem. -/
  E_spectral : FunctionalCalculus.IsSpectralMeasureFor E gen
  /-- The generator's domain equals the Hamiltonian's domain. -/
  domain_eq : gen.domain = hamiltonian.domain


/-! ## Spectral Projections -/

/-- Projection onto the electron (positive energy) subspace: E([mc², ∞)).

This projects onto states with energy ≥ mc², i.e., particle states.
In the non-interacting theory, electrons live entirely in this subspace. -/
def electronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Ici data.hamiltonian.constants.restEnergy)

/-- Projection onto the positron (negative energy) subspace: E((-∞, -mc²]).

This projects onto states with energy ≤ -mc², i.e., antiparticle states.
In Dirac's sea picture, these states are all filled in the vacuum. -/
def positronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))


/-! ## Spectral Measure Axioms -/

/-- Specification of a spectral measure for a self-adjoint generator.

This collects the properties that characterize a projection-valued measure:
- Multiplicativity: E(B)E(C) = E(B ∩ C)
- Self-adjointness of projections
- Normalization: E(ℝ) = 1
- Additivity for disjoint sets
- Strong continuity -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  /-- E(B)E(C) = E(B ∩ C): spectral projections multiply via intersection. -/
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  /-- E(B) is self-adjoint: ⟨E(B)ψ, φ⟩ = ⟨ψ, E(B)φ⟩. -/
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  /-- E(ℝ) = 1: the spectral measure is normalized (total probability 1). -/
  proj_univ : E Set.univ = 1
  /-- E(B ∪ C) = E(B) + E(C) for disjoint B, C: finite additivity. -/
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  /-- Strong operator continuity from the right for the spectral family. -/
  proj_sot : ∀ ψ t₀, Filter.Tendsto (fun t => E (Set.Iic t) ψ) (nhdsWithin t₀ (Set.Ioi t₀)) (nhds (E (Set.Iic t₀) ψ))
  /-- The defining relationship: U(t) = ∫e^{its}dE(s).
      This connects the unitary group to its spectral decomposition. -/
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ ⟨proj_mul, proj_sa, proj_sot, proj_empty, proj_univ, proj_add⟩)

/-- **Axiom**: The spectral measure is supported on the spectrum.

If every point in B has a bounded resolvent (is in the resolvent set),
then E(B) = 0. This is the abstract statement that the spectral measure
"lives on" the spectrum. -/
axiom spectral_measure_supported_on_spectrum
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B)
    (h_resolvent : ∀ s ∈ B, ∃ (R : H →L[ℂ] H),
        ∀ (ψ : gen.domain), R (gen.op ψ - s • (ψ : H)) = ψ) :
    E B = 0

/-- **Axiom**: Every point in the Dirac spectral gap has a bounded resolvent.

This is the detailed version of `dirac_gap_in_resolvent` that works with
the generator rather than the Hamiltonian directly. -/
axiom dirac_gap_in_resolvent_set (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0)
    (s : ℝ)
    (hs_lower : -data.hamiltonian.constants.restEnergy < s)
    (hs_upper : s < data.hamiltonian.constants.restEnergy) :
    ∃ (R : H →L[ℂ] H), ∀ (ψ : data.gen.domain),
        R (data.gen.op ψ - s • (ψ : H)) = ψ


/-! ## Orthogonality and Completeness -/

/-- Electron and positron subspaces are orthogonal: E₊ E₋ = 0.

**Physical meaning**: A state cannot be simultaneously a particle and an
antiparticle. The subspaces H₊ and H₋ have trivial intersection.

**Proof**: The spectral sets [mc², ∞) and (-∞, -mc²] are disjoint when mc² > 0,
so their spectral projections multiply to zero. -/
theorem electron_positron_orthogonal (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data * positronProjection data = 0 := by
  unfold electronProjection positronProjection
  have h_disj : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                         (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
      unfold DiracConstants.restEnergy
      apply mul_pos hm
      exact sq_pos_of_pos data.hamiltonian.constants.c_pos
    linarith
  exact FunctionalCalculus.spectral_projection_disjoint data.E
    data.E_spectral.toIsSpectralMeasure
    (Set.Ici data.hamiltonian.constants.restEnergy)
    (Set.Iic (-data.hamiltonian.constants.restEnergy))
    measurableSet_Ici measurableSet_Iic h_disj

/-- The spectral gap has zero spectral measure: E((-mc², mc²)) = 0.

**Physical meaning**: No stationary states exist with energy in the gap.
Any state in the gap region must be a superposition of electron and positron
states, not a stationary state of definite energy. -/
theorem dirac_spectral_gap_zero (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                    data.hamiltonian.constants.restEnergy) = 0 := by
  apply spectral_measure_supported_on_spectrum data.gen data.gen_sa data.E data.E_spectral
  · exact measurableSet_Ioo
  · intro s ⟨hs_lower, hs_upper⟩
    exact dirac_gap_in_resolvent_set data hm s hs_lower hs_upper

/-- Electron and positron projections are complete: E₊ + E₋ = 1 (for m > 0).

**Physical meaning**: Every state decomposes uniquely into electron and
positron components: ψ = E₊ψ + E₋ψ. There are no states "in the gap."

**Proof**: The three sets [mc², ∞), (-∞, -mc²], and (-mc², mc²) partition ℝ.
The gap contributes E(gap) = 0, so E₊ + E₋ = E(ℝ) = 1. -/
theorem electron_positron_complete (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data + positronProjection data = 1 := by
  unfold electronProjection positronProjection

  -- Step 1: mc² > 0
  have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
    unfold DiracConstants.restEnergy
    apply mul_pos hm
    exact sq_pos_of_pos data.hamiltonian.constants.c_pos

  -- Step 2: The gap contributes nothing
  have h_gap : data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                               data.hamiltonian.constants.restEnergy) = 0 :=
    dirac_spectral_gap_zero data hm

  -- Step 3: The three sets partition ℝ
  have h_union : Set.Ici data.hamiltonian.constants.restEnergy ∪
                 Set.Iic (-data.hamiltonian.constants.restEnergy) ∪
                 Set.Ioo (-data.hamiltonian.constants.restEnergy)
                         data.hamiltonian.constants.restEnergy = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo, Set.mem_univ, iff_true]
    by_cases h : x ≥ data.hamiltonian.constants.restEnergy
    · left; left; exact h
    · by_cases h' : x ≤ -data.hamiltonian.constants.restEnergy
      · left; right; exact h'
      · right
        push_neg at h h'
        exact ⟨h', h⟩

  -- Step 4a: Electron and positron supports are disjoint
  have h_disj1 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                          (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    linarith

  -- Step 4b: (Electron ∪ positron) is disjoint from gap
  have h_disj2 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy ∪
                           Set.Iic (-data.hamiltonian.constants.restEnergy))
                          (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                                   data.hamiltonian.constants.restEnergy) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_union, hx_gap⟩
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo] at hx_union hx_gap
    cases hx_union with
    | inl h => linarith [hx_gap.2]
    | inr h => linarith [hx_gap.1]

  -- Step 5: Chain of equalities using additivity
  calc data.E (Set.Ici data.hamiltonian.constants.restEnergy) +
       data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
      = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
          rw [← data.E_spectral.proj_add _ _ measurableSet_Ici measurableSet_Iic h_disj1]
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) + 0 := by abel
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) +
        data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                        data.hamiltonian.constants.restEnergy) := by rw [h_gap]
    _ = data.E Set.univ := by
        rw [← data.E_spectral.proj_add _ _ (measurableSet_Ici.union measurableSet_Iic)
            measurableSet_Ioo h_disj2, h_union]
    _ = 1 := data.E_spectral.proj_univ


/-! ## Time Evolution -/

/-- Time evolution operator U(t) = e^{-itH_D/ℏ}.

This is the solution operator for the Dirac equation: if ψ(0) is the initial
state, then ψ(t) = U(t)ψ(0) is the state at time t. -/
def diracTimeEvolution (data : DiracSpectralData H) (t : ℝ) : H →L[ℂ] H :=
  data.U_grp.U t

/-- Time evolution is unitary: U(t)*U(t) = U(t)U(t)* = 1.

**Physical meaning**: Time evolution preserves probability. The total
probability ∫|ψ(t,x)|²d³x is independent of t.

**Proof**: By definition of `OneParameterUnitaryGroup`. -/
theorem dirac_evolution_unitary (data : DiracSpectralData H) (t : ℝ) :
    Unitary (data.U_grp.U t) := by
  constructor
  · -- adjoint * U = 1
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (data.U_grp.unitary t φ ψ)
  · -- U * adjoint = 1
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, ← @inverse_eq_adjoint]
    exact data.U_grp.unitary (-t) φ ψ


/-! ## Functional Calculus -/

/-- Functional calculus for the Dirac operator: f(H_D) = ∫f(s)dE(s).

Given a measurable function f : ℝ → ℂ, this constructs the operator f(H_D)
via spectral integration. Examples:
- f(s) = e^{its} gives U(t)
- f(s) = s gives H_D itself
- f(s) = 1_{[mc²,∞)}(s) gives E₊ -/
noncomputable def diracFunctionalCalculus (data : DiracSpectralData H) (f : ℝ → ℂ) :
    FunctionalCalculus.functionalDomainSubmodule data.E data.E_spectral.toIsSpectralMeasure data.E_spectral.proj_univ f →ₗ[ℂ] H :=
  FunctionalCalculus.functionalCalculus data.E data.E_spectral.toIsSpectralMeasure data.E_spectral.proj_univ f

/-- The sign function for splitting electron and positron subspaces.

This function is +1 on [mc², ∞), -1 on (-∞, -mc²], and 0 in the gap.
Applying functional calculus: sign(H_D) = E₊ - E₋. -/
noncomputable def signFunction (κ : DiracConstants) : ℝ → ℂ := fun s =>
  if s ≥ κ.restEnergy then 1
  else if s ≤ -κ.restEnergy then -1
  else 0  -- in the gap, but E(gap) = 0 anyway


/-! ## Relativistic Energy-Momentum Relation -/

/-- Relativistic energy as a function of momentum: E(p) = √((pc)² + (mc²)²).

This is the positive branch of the relativistic dispersion relation
E² = (pc)² + (mc²)². The Dirac equation has both positive and negative
energy solutions. -/
noncomputable def relativisticEnergy (κ : DiracConstants) (p : ℝ) : ℝ :=
  Real.sqrt ((p * κ.c)^2 + κ.restEnergy^2)

/-- Positive energy branch: E₊(p) = +√((pc)² + (mc²)²).

These are the electron energies, always ≥ mc². -/
noncomputable def positiveEnergy (κ : DiracConstants) (p : ℝ) : ℝ := relativisticEnergy κ p

/-- Negative energy branch: E₋(p) = -√((pc)² + (mc²)²).

These are the positron energies (in the Dirac sea picture), always ≤ -mc². -/
noncomputable def negativeEnergy (κ : DiracConstants) (p : ℝ) : ℝ := -relativisticEnergy κ p

/-- The relativistic energy is always at least mc² in magnitude.

**Physical meaning**: A free particle cannot have energy less than its rest
mass energy. The minimum occurs at p = 0 (particle at rest). -/
theorem energy_geq_rest_mass (κ : DiracConstants) (p : ℝ) :
    relativisticEnergy κ p ≥ κ.restEnergy := by
  unfold relativisticEnergy DiracConstants.restEnergy
  have h_nonneg : κ.m * κ.c^2 ≥ 0 := by
    apply mul_nonneg κ.m_nonneg
    exact sq_nonneg κ.c
  have h_inner_nonneg : (p * κ.c)^2 + (κ.m * κ.c^2)^2 ≥ 0 := by positivity
  rw [ge_iff_le]
  rw [Real.le_sqrt h_nonneg h_inner_nonneg]
  nlinarith [sq_nonneg (p * κ.c)]


/-! ## Cayley Transform -/

/-- The Cayley transform of a self-adjoint generator is unitary.

The Cayley transform C(A) = (A - i)(A + i)⁻¹ maps self-adjoint operators
to unitary operators (with -1 not in the spectrum). This provides an
alternative characterization of self-adjointness. -/
theorem dirac_cayley_unitary
    (U_grp : @OneParameterUnitaryGroup H _ _)
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) :=
  cayleyTransform_unitary gen hsa

end SpectralTheory
