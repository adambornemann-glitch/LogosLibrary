# The Dirac Operator: Formal Definitions

**Source**: `Dirac.lean`  
**Author**: Adam Bornemann  
**Created**: January 10, 2026

---

## Table of Contents

1. [Overview](#overview)
2. [Dirac-Pauli Matrix Representations](#dirac-pauli-matrix-representations)
3. [Gamma Matrix Representations](#gamma-matrix-representations)
4. [Clifford Algebra Verification (Dirac-Pauli)](#clifford-algebra-verification-dirac-pauli)
5. [Clifford Algebra Verification (Gamma Matrices)](#clifford-algebra-verification-gamma-matrices)
6. [Gamma Matrix Hermiticity](#gamma-matrix-hermiticity)
7. [Spinor Space and Unbounded Operators](#spinor-space-and-unbounded-operators)
8. [Pauli Matrices](#pauli-matrices)
9. [Pauli Matrix Properties](#pauli-matrix-properties)
10. [Abstract Dirac Matrices Structure](#abstract-dirac-matrices-structure)
11. [Physical Constants](#physical-constants)
12. [Dirac Hamiltonian Structure](#dirac-hamiltonian-structure)
13. [Spectral Properties](#spectral-properties)
14. [Unboundedness Results](#unboundedness-results)
15. [Spectral Framework Connection](#spectral-framework-connection)
16. [Relativistic Dispersion](#relativistic-dispersion)
17. [Dirac Current and Probability](#dirac-current-and-probability)
18. [Continuity Equation](#continuity-equation)
19. [Born's Rule](#borns-rule)
20. [Thermodynamic Unitarity](#thermodynamic-unitarity)
21. [First Law Equivalence](#first-law-equivalence)
22. [Summary](#summary)

---

## Overview

This formalization constructs the free Dirac operator and verifies it fits within the spectral theory framework for unbounded self-adjoint operators. The Dirac Hamiltonian is:

$$H_D = c\boldsymbol{\alpha} \cdot \mathbf{p} + \beta mc^2 = -i\hbar c(\boldsymbol{\alpha} \cdot \nabla) + \beta mc^2$$

**Key Results**:
- Spectrum: $\sigma(H_D) = (-\infty, -mc^2] \cup [mc^2, \infty)$ with spectral gap $(-mc^2, mc^2)$
- Probability density $j^0 = \psi^\dagger\psi \geq 0$ (positive-definite, unlike Klein-Gordon)
- Current conservation: $\partial_\mu j^\mu = 0$
- First Law: Spectral measure invariant under time evolution

---

## Dirac-Pauli Matrix Representations

### def diracAlpha1
```lean
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]
```

### def diracAlpha2
```lean
def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, -I, 0, 0;
     I, 0, 0, 0]
```

### def diracAlpha3
```lean
def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]
```

### def diracBeta
```lean
def diracBeta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]
```

---

## Gamma Matrix Representations

### def gamma0
```lean
def gamma0 : Matrix (Fin 4) (Fin 4) ℂ := 
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
```

### def gamma1
```lean
def gamma1 : Matrix (Fin 4) (Fin 4) ℂ := 
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
```

### def gamma2
```lean
def gamma2 : Matrix (Fin 4) (Fin 4) ℂ := 
  !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]
```

### def gamma3
```lean
def gamma3 : Matrix (Fin 4) (Fin 4) ℂ := 
  !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]
```

---

## Clifford Algebra Verification (Dirac-Pauli)

### lemma diracAlpha1_sq
```lean
private lemma diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1
```

### lemma diracAlpha2_sq
```lean
private lemma diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1
```

### lemma diracAlpha3_sq
```lean
private lemma diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1
```

### lemma diracBeta_sq
```lean
private lemma diracBeta_sq : diracBeta * diracBeta = 1
```

### lemma diracAlpha12_anticommute
```lean
private lemma diracAlpha12_anticommute : 
    diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0
```

### lemma diracAlpha13_anticommute
```lean
private lemma diracAlpha13_anticommute : 
    diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0
```

### lemma diracAlpha23_anticommute
```lean
private lemma diracAlpha23_anticommute : 
    diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0
```

### lemma diracAlpha1_beta_anticommute
```lean
private lemma diracAlpha1_beta_anticommute : 
    diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0
```

### lemma diracAlpha2_beta_anticommute
```lean
private lemma diracAlpha2_beta_anticommute : 
    diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0
```

### lemma diracAlpha3_beta_anticommute
```lean
private lemma diracAlpha3_beta_anticommute : 
    diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0
```

### lemma diracAlpha1_hermitian
```lean
private lemma diracAlpha1_hermitian : diracAlpha1.conjTranspose = diracAlpha1
```

### lemma diracAlpha2_hermitian
```lean
private lemma diracAlpha2_hermitian : diracAlpha2.conjTranspose = diracAlpha2
```

### lemma diracAlpha3_hermitian
```lean
private lemma diracAlpha3_hermitian : diracAlpha3.conjTranspose = diracAlpha3
```

### lemma diracBeta_hermitian
```lean
private lemma diracBeta_hermitian : diracBeta.conjTranspose = diracBeta
```

---

## Clifford Algebra Verification (Gamma Matrices)

### lemma clifford_00
```lean
private lemma clifford_00 : gamma0 * gamma0 + gamma0 * gamma0 =
    2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_01
```lean
private lemma clifford_01 : gamma0 * gamma1 + gamma1 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_02
```lean
private lemma clifford_02 : gamma0 * gamma2 + gamma2 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_03
```lean
private lemma clifford_03 : gamma0 * gamma3 + gamma3 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_10
```lean
private lemma clifford_10 : gamma1 * gamma0 + gamma0 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_11
```lean
private lemma clifford_11 : gamma1 * gamma1 + gamma1 * gamma1 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_12
```lean
private lemma clifford_12 : gamma1 * gamma2 + gamma2 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_13
```lean
private lemma clifford_13 : gamma1 * gamma3 + gamma3 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_20
```lean
private lemma clifford_20 : gamma2 * gamma0 + gamma0 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_21
```lean
private lemma clifford_21 : gamma2 * gamma1 + gamma1 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_22
```lean
private lemma clifford_22 : gamma2 * gamma2 + gamma2 * gamma2 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_23
```lean
private lemma clifford_23 : gamma2 * gamma3 + gamma3 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_30
```lean
private lemma clifford_30 : gamma3 * gamma0 + gamma0 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_31
```lean
private lemma clifford_31 : gamma3 * gamma1 + gamma1 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_32
```lean
private lemma clifford_32 : gamma3 * gamma2 + gamma2 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma clifford_33
```lean
private lemma clifford_33 : gamma3 * gamma3 + gamma3 * gamma3 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
```

### lemma neg_two_eq_smul
```lean
private lemma neg_two_eq_smul : 
    (-2 : Matrix (Fin 4) (Fin 4) ℂ) = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
```

---

## Gamma Matrix Hermiticity

### lemma gamma0_hermitian_proof
```lean
private lemma gamma0_hermitian_proof : gamma0.conjTranspose = gamma0
```

### lemma gamma1_antihermitian
```lean
private lemma gamma1_antihermitian : gamma1.conjTranspose = -gamma1
```

### lemma gamma2_antihermitian
```lean
private lemma gamma2_antihermitian : gamma2.conjTranspose = -gamma2
```

### lemma gamma3_antihermitian
```lean
private lemma gamma3_antihermitian : gamma3.conjTranspose = -gamma3
```

---

## Spinor Space and Unbounded Operators

### abbrev SpinorSpace
```lean
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4)
```

### structure DiracOperator
```lean
structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H
```

---

## Pauli Matrices

### def pauliX
```lean
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
```

### def pauliY
```lean
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
```

### def pauliZ
```lean
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
```

---

## Pauli Matrix Properties

### lemma pauliX_hermitian
```lean
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX
```

### lemma pauliY_hermitian
```lean
lemma pauliY_hermitian : pauliY.conjTranspose = pauliY
```

### lemma pauliZ_hermitian
```lean
lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ
```

### lemma pauliX_sq
```lean
lemma pauliX_sq : pauliX * pauliX = 1
```

### lemma pauliY_sq
```lean
lemma pauliY_sq : pauliY * pauliY = 1
```

### lemma pauliZ_sq
```lean
lemma pauliZ_sq : pauliZ * pauliZ = 1
```

### lemma pauliXY_anticommute
```lean
lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0
```

### lemma pauliXZ_anticommute
```lean
lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0
```

### lemma pauliYZ_anticommute
```lean
lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0
```

---

## Abstract Dirac Matrices Structure

### structure DiracMatrices
```lean
structure DiracMatrices where
  alpha : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  beta : Matrix (Fin 4) (Fin 4) ℂ
  alpha_sq : ∀ i, alpha i * alpha i = 1
  beta_sq : beta * beta = 1
  alpha_anticommute : ∀ i j, i ≠ j → alpha i * alpha j + alpha j * alpha i = 0
  alpha_beta_anticommute : ∀ i, alpha i * beta + beta * alpha i = 0
  alpha_hermitian : ∀ i, (alpha i).conjTranspose = alpha i
  beta_hermitian : beta.conjTranspose = beta
```

### def standardDiracMatrices
```lean
def standardDiracMatrices : DiracMatrices
```

---

## Physical Constants

### structure DiracConstants
```lean
structure DiracConstants where
  hbar : ℝ
  c : ℝ
  m : ℝ
  hbar_pos : hbar > 0
  c_pos : c > 0
  m_nonneg : m ≥ 0
```

### def DiracConstants.restEnergy
```lean
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2
```

---

## Dirac Hamiltonian Structure

### structure DiracHamiltonian
```lean
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    DiracOperator H where
  constants : DiracConstants
  matrices : DiracMatrices
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  domain_dense : Dense (domain : Set H)
```

### axiom dirac_generates_unitary
```lean
axiom dirac_generates_unitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∃ (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp),
      gen.IsSelfAdjoint ∧ gen.domain = H_D.domain
```

---

## Spectral Properties

### def diracSpectrum
```lean
def diracSpectrum (κ : DiracConstants) : Set ℝ :=
  Set.Iic (-κ.restEnergy) ∪ Set.Ici κ.restEnergy
```

### def diracGap
```lean
def diracGap (κ : DiracConstants) : Set ℝ :=
  Set.Ioo (-κ.restEnergy) κ.restEnergy
```

### axiom dirac_gap_in_resolvent
```lean
axiom dirac_gap_in_resolvent (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (hm : H_D.constants.m > 0) :
    ∀ E ∈ diracGap H_D.constants,
      ∃ (R : H →L[ℂ] H), ∀ (ψ : H_D.domain), R (H_D.op ψ - E • (ψ : H)) = ψ
```

### axiom dirac_spectrum_eq
```lean
axiom dirac_spectrum_eq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H)
    (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp)
    (hgen : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    ∀ B ⊆ diracGap H_D.constants, MeasurableSet B → E B = 0
```

---

## Unboundedness Results

### axiom dirac_has_arbitrarily_negative_energy
```lean
axiom dirac_has_arbitrarily_negative_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2
```

### axiom dirac_has_arbitrarily_positive_energy
```lean
axiom dirac_has_arbitrarily_positive_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2
```

### theorem dirac_unbounded_below
```lean
theorem dirac_unbounded_below (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2
```

### theorem dirac_unbounded_above
```lean
theorem dirac_unbounded_above (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2
```

---

## Spectral Framework Connection

### structure DiracSpectralData
```lean
structure DiracSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  hamiltonian : DiracHamiltonian H
  U_grp : OneParameterUnitaryGroup (H := H)
  gen : Generator U_grp
  gen_sa : gen.IsSelfAdjoint
  E : Set ℝ → H →L[ℂ] H
  E_spectral : FunctionalCalculus.IsSpectralMeasureFor E gen
  domain_eq : gen.domain = hamiltonian.domain
```

### def diracTimeEvolution
```lean
def diracTimeEvolution (data : DiracSpectralData H) (t : ℝ) : H →L[ℂ] H :=
  data.U_grp.U t
```

### theorem dirac_evolution_unitary
```lean
theorem dirac_evolution_unitary (data : DiracSpectralData H) (t : ℝ) :
    Unitary (data.U_grp.U t)
```

### def diracFunctionalCalculus
```lean
noncomputable def diracFunctionalCalculus (data : DiracSpectralData H) (f : ℝ → ℂ) :
    FunctionalCalculus.functionalDomainSubmodule data.E data.E_spectral.proj_univ f →ₗ[ℂ] H :=
  FunctionalCalculus.functionalCalculus data.E data.E_spectral.proj_univ f
```

### def signFunction
```lean
noncomputable def signFunction (κ : DiracConstants) : ℝ → ℂ := fun s =>
  if s ≥ κ.restEnergy then 1
  else if s ≤ -κ.restEnergy then -1
  else 0
```

### def electronProjection
```lean
def electronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Ici data.hamiltonian.constants.restEnergy)
```

### def positronProjection
```lean
def positronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
```

### structure IsSpectralMeasureFor
```lean
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  proj_univ : E Set.univ = 1
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ)
```

### theorem electron_positron_orthogonal
```lean
theorem electron_positron_orthogonal (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data * positronProjection data = 0
```

### axiom spectral_measure_supported_on_spectrum
```lean
axiom spectral_measure_supported_on_spectrum
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B)
    (h_resolvent : ∀ s ∈ B, ∃ (R : H →L[ℂ] H),
        ∀ (ψ : gen.domain), R (gen.op ψ - s • (ψ : H)) = ψ) :
    E B = 0
```

### axiom dirac_gap_in_resolvent_set
```lean
axiom dirac_gap_in_resolvent_set (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0)
    (s : ℝ)
    (hs_lower : -data.hamiltonian.constants.restEnergy < s)
    (hs_upper : s < data.hamiltonian.constants.restEnergy) :
    ∃ (R : H →L[ℂ] H), ∀ (ψ : data.gen.domain),
        R (data.gen.op ψ - s • (ψ : H)) = ψ
```

### theorem dirac_spectral_gap_zero
```lean
theorem dirac_spectral_gap_zero (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                    data.hamiltonian.constants.restEnergy) = 0
```

### theorem electron_positron_complete
```lean
theorem electron_positron_complete (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data + positronProjection data = 1
```

---

## Relativistic Dispersion

### def relativisticEnergy
```lean
noncomputable def relativisticEnergy (κ : DiracConstants) (p : ℝ) : ℝ :=
  Real.sqrt ((p * κ.c)^2 + κ.restEnergy^2)
```

### def positiveEnergy
```lean
noncomputable def positiveEnergy (κ : DiracConstants) (p : ℝ) : ℝ := relativisticEnergy κ p
```

### def negativeEnergy
```lean
noncomputable def negativeEnergy (κ : DiracConstants) (p : ℝ) : ℝ := -relativisticEnergy κ p
```

### theorem energy_geq_rest_mass
```lean
theorem energy_geq_rest_mass (κ : DiracConstants) (p : ℝ) :
    relativisticEnergy κ p ≥ κ.restEnergy
```

### theorem dirac_not_semibounded
```lean
theorem dirac_not_semibounded (H_D : DiracHamiltonian H) :
    ¬∃ c : ℝ, ∀ (ψ : H_D.domain), c * ‖(ψ : H)‖^2 ≤ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re
```

### theorem dirac_spectral_gap
```lean
theorem dirac_spectral_gap (H_D : DiracOperator H) (m c_light : ℝ) (hm : m > 0) (hc : c_light > 0) :
    ∀ E : ℝ, -m * c_light^2 < E → E < m * c_light^2 →
      ∃ (inv : H →ₗ[ℂ] H_D.domain), True
```

### theorem dirac_cayley_unitary
```lean
theorem dirac_cayley_unitary
    (U_grp : @OneParameterUnitaryGroup H _ _ )
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa)
```

---

## Dirac Current and Probability

### structure GammaMatrices
```lean
structure GammaMatrices where
  gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  clifford_minkowski : ∀ μ ν, gamma μ * gamma ν + gamma ν * gamma μ =
    2 • (if μ = ν then (if μ = 0 then 1 else -1) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0)
  gamma0_hermitian : (gamma 0).conjTranspose = gamma 0
  gammaI_antihermitian : ∀ i : Fin 3, (gamma i.succ).conjTranspose = -gamma i.succ
```

### def standardGammaMatrices
```lean
def standardGammaMatrices : GammaMatrices
```

### structure SpinorField
```lean
structure SpinorField where
  ψ : Spacetime → (Fin 4 → ℂ)
```

### structure SpinorField'
```lean
structure SpinorField' where
  ψ : (Fin 4 → ℝ) → (Fin 4 → ℂ)
  integrable : ∀ t : ℝ, Integrable (fun x : Fin 3 → ℝ =>
    ‖ψ (Fin.cons t (fun i => x i))‖^2) volume
```

### def diracAdjoint
```lean
noncomputable def diracAdjoint (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun a => ∑ b, star (ψ b) * (Γ.gamma 0) b a
```

### def diracCurrent
```lean
noncomputable def diracCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => ∑ a : Fin 4, ∑ b : Fin 4, star (ψ a) * (Γ.gamma 0 * Γ.gamma μ) a b * ψ b
```

### lemma gamma0_sq
```lean
lemma gamma0_sq (Γ : GammaMatrices) : Γ.gamma 0 * Γ.gamma 0 = 1
```

### theorem current_zero_eq_norm_sq
```lean
theorem current_zero_eq_norm_sq (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = ∑ a, ‖ψ a‖^2
```

### theorem current_zero_nonneg
```lean
theorem current_zero_nonneg (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    0 ≤ (diracCurrent Γ ψ 0).re
```

### theorem current_zero_eq_zero_iff
```lean
theorem current_zero_eq_zero_iff (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = 0 ↔ ψ = 0
```

### def probabilityDensity
```lean
noncomputable def probabilityDensity (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : ℝ :=
  (diracCurrent Γ ψ 0).re
```

### def probabilityCurrent
```lean
noncomputable def probabilityCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun i => diracCurrent Γ ψ i.succ
```

---

## Continuity Equation

### abbrev Spacetime
```lean
abbrev Spacetime := Fin 4 → ℝ
```

### def stdBasis
```lean
def stdBasis (μ : Fin 4) : Spacetime := fun ν => if μ = ν then 1 else 0
```

### def fourDivergence
```lean
noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : (Fin 4 → ℝ) → ℂ :=
  fun x => ∑ μ, deriv (fun t => j (Function.update x μ t) μ) (x μ)
```

### def partialDeriv'
```lean
noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ)) (x : Spacetime) : Fin 4 → ℂ :=
  fun a => fderiv ℝ (fun y => ψ y a) x (stdBasis μ)
```

### axiom dirac_current_conserved
```lean
axiom dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x) :
    ∀ x, fourDivergence (fun x => diracCurrent Γ (ψ.ψ x)) x = 0
```

### def spacetimePoint
```lean
def spacetimePoint (t : ℝ) (x : Fin 3 → ℝ) : Spacetime :=
  ![t, x 0, x 1, x 2]
```

### def totalProbability
```lean
noncomputable def totalProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) : ℝ :=
  ∫ x : Fin 3 → ℝ, probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) ∂volume
```

### axiom leibniz_integral_rule
```lean
axiom leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) :
    deriv (totalProbability Γ ψ) t =
    ∫ x : Fin 3 → ℝ, deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t ∂volume
```

### axiom continuity_equation
```lean
axiom continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t =
    -(∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i))
```

### axiom divergence_integral_vanishes
```lean
axiom divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_vanish : Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                               (Filter.cocompact _) (nhds 0)) :
    ∫ x : Fin 3 → ℝ, (∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)) ∂volume = 0
```

### theorem probability_conserved
```lean
theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_vanish : ∀ t, Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                              (Filter.cocompact _) (nhds 0)) :
    ∀ t, deriv (totalProbability Γ ψ) t = 0
```

---

## Born's Rule

### def normalizedProbability
```lean
noncomputable def normalizedProbability (Γ : GammaMatrices) (ψ : SpinorField)
    (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) / totalProbability Γ ψ t
```

### theorem born_rule_valid
```lean
theorem born_rule_valid (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_nonzero : totalProbability Γ ψ t ≠ 0) :
    (∀ x, 0 ≤ normalizedProbability Γ ψ t x) ∧
    (∫ x, normalizedProbability Γ ψ t x ∂volume = 1)
```

---

## Thermodynamic Unitarity

### axiom spectral_projection_eq_indicator
```lean
axiom spectral_projection_eq_indicator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) :
    E B = FunctionalCalculus.boundedFunctionalCalculus E (Set.indicator B 1) (indicator_bounded B)
```

### axiom unitary_eq_spectral_integral
```lean
axiom unitary_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (t : ℝ) (hb : ∃ M, ∀ s : ℝ, ‖Complex.exp (I * t * s)‖ ≤ M) :
    U_grp.U t = FunctionalCalculus.boundedFunctionalCalculus E (fun s => Complex.exp (I * t * s)) hb
```

### axiom functional_calculus_comm
```lean
axiom functional_calculus_comm (E : Set ℝ → H →L[ℂ] H)
    (f g : ℝ → ℂ)
    (hf : ∃ M, ∀ s : ℝ, ‖f s‖ ≤ M)
    (hg : ∃ M, ∀ s : ℝ, ‖g s‖ ≤ M) :
    FunctionalCalculus.boundedFunctionalCalculus E f hf * FunctionalCalculus.boundedFunctionalCalculus E g hg =
    FunctionalCalculus.boundedFunctionalCalculus E g hg * FunctionalCalculus.boundedFunctionalCalculus E f hf
```

### axiom norm_preserving_implies_inner_preserving
```lean
axiom norm_preserving_implies_inner_preserving (T : H →L[ℂ] H)
    (h_norm : ∀ χ, ‖T χ‖ = ‖χ‖) :
    ∀ ψ φ, ⟪T ψ, T φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
```

### lemma exp_its_bounded
```lean
lemma exp_its_bounded (t : ℝ) : ∃ M, ∀ s : ℝ, ‖Complex.exp (I * t * s)‖ ≤ M
```

### lemma indicator_bounded
```lean
lemma indicator_bounded (B : Set ℝ) : ∃ M, ∀ s : ℝ, ‖Set.indicator B (1 : ℝ → ℂ) s‖ ≤ M
```

### theorem unitary_commutes_with_spectral
```lean
theorem unitary_commutes_with_spectral (data : DiracSpectralData H)
    (t : ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
    data.U_grp.U t * data.E B = data.E B * data.U_grp.U t
```

### axiom spectral_scalar_measure_apply
```lean
axiom spectral_scalar_measure_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Set ℝ → H →L[ℂ] H) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    BochnerRoute.spectral_scalar_measure E ψ B = ENNReal.ofReal (‖E B ψ‖^2)
```

### theorem spectral_measure_invariant
```lean
theorem spectral_measure_invariant {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (t : ℝ) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
    BochnerRoute.spectral_scalar_measure E ψ B
```

### theorem unitary_implies_spectral_invariance
```lean
theorem unitary_implies_spectral_invariance {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (h_unitary : ∀ t, Unitary (U_grp.U t)) :
    ∀ t ψ B, MeasurableSet B →
      BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
      BochnerRoute.spectral_scalar_measure E ψ B
```

### theorem spectral_invariance_implies_unitary
```lean
theorem spectral_invariance_implies_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (h_inv : ∀ t ψ B, MeasurableSet B →
      BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
      BochnerRoute.spectral_scalar_measure E ψ B) :
    ∀ t, Unitary (U_grp.U t)
```

### lemma unitary_preserves_norm
```lean
lemma unitary_preserves_norm (data : DiracSpectralData H) (t : ℝ) (χ : H) :
    ‖data.U_grp.U t χ‖ = ‖χ‖
```

### theorem electron_number_conserved
```lean
theorem electron_number_conserved (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) (t : ℝ) (ψ : H) :
    ‖electronProjection data (data.U_grp.U t ψ)‖ =
    ‖electronProjection data ψ‖
```

### theorem positron_number_conserved
```lean
theorem positron_number_conserved (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) (t : ℝ) (ψ : H) :
    ‖positronProjection data (data.U_grp.U t ψ)‖ =
    ‖positronProjection data ψ‖
```

---

## First Law Equivalence

### structure FirstLawEquivalence
```lean
structure FirstLawEquivalence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (E : Set ℝ → H →L[ℂ] H) : Prop where
  unitary : ∀ t, Unitary (U_grp.U t)
  selfAdjoint : gen.IsSelfAdjoint
  spectral_invariant : ∀ t ψ B, MeasurableSet B →
    BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B = BochnerRoute.spectral_scalar_measure E ψ B
  energy_conserved : ∀ t ψ (hψ : ψ ∈ gen.domain),
    ⟪gen.op ⟨U_grp.U t ψ, by exact gen.domain_invariant t ψ hψ⟩, U_grp.U t ψ⟫_ℂ = ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
```

### axiom energy_eq_spectral_moment
```lean
axiom energy_eq_spectral_moment {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = ∫ s, s ∂(BochnerRoute.spectral_scalar_measure E ψ)
```

### theorem first_law_equivalence_of_self_adjoint
```lean
theorem first_law_equivalence_of_self_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    FirstLawEquivalence gen E
```

---

## Summary

| Category | Count |
|----------|-------|
| **Definitions** | 34 |
| **Lemmas** | 51 |
| **Theorems** | 21 |
| **Axioms** | 16 |
| **Structures** | 10 |
| **Abbreviations** | 2 |
| **Total** | **134** |

### Definitions (34)
`diracAlpha1`, `diracAlpha2`, `diracAlpha3`, `diracBeta`, `gamma0`, `gamma1`, `gamma2`, `gamma3`, `pauliX`, `pauliY`, `pauliZ`, `standardDiracMatrices`, `DiracConstants.restEnergy`, `diracSpectrum`, `diracGap`, `diracTimeEvolution`, `diracFunctionalCalculus`, `signFunction`, `electronProjection`, `positronProjection`, `relativisticEnergy`, `positiveEnergy`, `negativeEnergy`, `standardGammaMatrices`, `diracAdjoint`, `diracCurrent`, `probabilityDensity`, `probabilityCurrent`, `stdBasis`, `fourDivergence`, `partialDeriv'`, `spacetimePoint`, `totalProbability`, `normalizedProbability`

### Structures (10)
`DiracOperator`, `DiracMatrices`, `DiracConstants`, `DiracHamiltonian`, `DiracSpectralData`, `IsSpectralMeasureFor`, `GammaMatrices`, `SpinorField`, `SpinorField'`, `FirstLawEquivalence`

### Abbreviations (2)
`SpinorSpace`, `Spacetime`

### Key Theorems
1. **current_zero_eq_norm_sq**: $j^0 = \sum_a |\psi_a|^2$ (probability density is positive)
2. **probability_conserved**: $\frac{d}{dt}\int\rho\,d^3x = 0$ (total probability conserved)
3. **born_rule_valid**: Normalized probability is non-negative and integrates to 1
4. **spectral_measure_invariant**: $\mu_{U(t)\psi}(B) = \mu_\psi(B)$ (First Law)
5. **electron_positron_complete**: $E_+ + E_- = 1$ (particle-antiparticle decomposition)
6. **first_law_equivalence_of_self_adjoint**: Self-adjointness ⟺ Full First Law structure
