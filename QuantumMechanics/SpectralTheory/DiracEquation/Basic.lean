/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.CliffordAlgebra
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.GammaTraces
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.PauliMatrices
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Operators
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.SpectralTheory
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Current
import LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Conservation
/-!
# The Dirac Equation and Relativistic Quantum Mechanics

This module develops the Dirac equation for spin-1/2 particles, from the algebraic
foundations (Clifford algebra of spacetime) through spectral theory to the
physical consequences (probability conservation and the Born rule).

## Overview

The Dirac equation is the relativistic wave equation for fermions:

  iℏ ∂ψ/∂t = H_D ψ,    where   H_D = -iℏc(α·∇) + βmc²

The matrices α = (α₁, α₂, α₃) and β satisfy the Clifford algebra relations:
- αᵢ² = β² = I (involutions)
- {αᵢ, αⱼ} = 0 for i ≠ j (spatial anticommutation)
- {αᵢ, β} = 0 (momentum-mass anticommutation)

These relations ensure H_D² gives the relativistic dispersion relation
E² = (pc)² + (mc²)², which is the mathematical content of special relativity.

## Module Structure

### `CliffordAlgebra`
The algebraic foundations: Dirac matrices α, β and gamma matrices γ^μ in the
standard (Dirac-Pauli) representation. All 16 Clifford relations {γ^μ, γ^ν} = 2η^μν I
are verified by brute-force computation.

* `diracAlpha1`, `diracAlpha2`, `diracAlpha3`: Spatial Dirac matrices
* `diracBeta`: Mass matrix β = diag(1, 1, -1, -1)
* `gamma0`, `gamma1`, `gamma2`, `gamma3`: Covariant gamma matrices
* `gamma5`: Chirality matrix γ⁵ = iγ⁰γ¹γ²γ³
* `DiracMatrices`: Abstract structure for any valid representation
* `standardDiracMatrices`: The Dirac-Pauli representation

### `GammaTraces`
Trace identities for gamma matrix products — the workhorse formulas for
Feynman diagram calculations.

* `gamma_trace_zero`: Tr(γ^μ) = 0
* `gamma_trace_two`: Tr(γ^μ γ^ν) = 4η^μν
* `gamma_trace_three`: Tr(γ^μ γ^ν γ^ρ) = 0 (odd number)

### `PauliMatrices`
The 2×2 Pauli matrices forming the spin-1/2 representation of su(2).

* `pauliX`, `pauliY`, `pauliZ`: The three Pauli matrices
* Hermiticity, involution, and anticommutation properties

### `Operators`
Unbounded operator framework for the Dirac Hamiltonian.

* `DiracOperator`: Unbounded linear operator with explicit domain
* `DiracConstants`: Physical parameters (ℏ, c, m) with positivity
* `DiracHamiltonian`: Full Hamiltonian with symmetry properties

### `SpectralTheory`
Spectral decomposition via functional calculus.

* `diracSpectrum`: The set (-∞, -mc²] ∪ [mc², ∞)
* `diracGap`: The forbidden region (-mc², mc²)
* `electronProjection`: Spectral projection E([mc², ∞))
* `positronProjection`: Spectral projection E((-∞, -mc²])
* `DiracSpectralData`: Complete spectral decomposition

### `Current`
The probability current and density.

* `diracCurrent`: The 4-current jᵘ = ψ̄γᵘψ
* `probabilityDensity`: ρ = j⁰ = ψ†ψ
* `current_zero_eq_norm_sq`: j⁰ = Σₐ|ψₐ|²
* `current_zero_nonneg`: j⁰ ≥ 0

### `Conservation`
Probability conservation and the Born rule.

* `probability_conserved`: d/dt ∫ρ d³x = 0
* `born_rule_valid`: P(x,t) = ρ/∫ρ is a valid probability distribution

## Physical Interpretation

### The Dirac Sea and Antiparticles
The spectrum σ(H_D) = (-∞, -mc²] ∪ [mc², ∞) has negative energy states.
Dirac's interpretation: the "vacuum" has all negative-energy states filled
(the Dirac sea). A hole in the sea appears as a positron — a particle with
positive energy and opposite charge.

### Chirality and the Weak Force
The matrix γ⁵ projects onto left-handed (P_L = (1-γ⁵)/2) and right-handed
(P_R = (1+γ⁵)/2) states. The weak nuclear force couples only to left-handed
particles, which is why γ⁵ is physically important.

### Probability Conservation
Unlike the Klein-Gordon equation, the Dirac equation has a *positive-definite*
probability density ρ = ψ†ψ ≥ 0. This is the key physical requirement that
motivated Dirac's construction. The proof that dP/dt = 0 follows from the
continuity equation ∂ᵤjᵘ = 0.

### The Born Rule
The theorem `born_rule_valid` shows that ρ/∫ρ satisfies the axioms of a
probability distribution: non-negative and normalized to 1. This connects
the mathematical formalism to quantum mechanical measurement.

## References

* [Dirac, *The Principles of Quantum Mechanics*][dirac1930], Chapter XI
* [Thaller, *The Dirac Equation*][thaller1992]
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Chapter 3
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. II §X.4

## Tags

Dirac equation, Clifford algebra, gamma matrices, spinor, relativistic quantum mechanics,
spectral gap, probability conservation, Born rule, chirality
-/
