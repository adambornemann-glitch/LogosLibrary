/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Schrödinger
/-!
# The Heisenberg Uncertainty Principle

This file derives the textbook Heisenberg uncertainty relation as a special case
of the Robertson inequality for canonically conjugate observables.

## Main results

* `heisenberg_uncertainty_principle`: For observables X, P satisfying the
  canonical commutation relation ⟨ψ, [X,P]ψ⟩ = iℏ,
  $$\sigma_X \sigma_P \geq \frac{\hbar}{2}$$

## Context

The Robertson inequality (proven in `Robertson.lean`) states:
$$\sigma_A \sigma_B \geq \frac{1}{2}|\langle [A,B] \rangle_\psi|$$

For position X and momentum P, the canonical commutation relation [X, P] = iℏ
gives ⟨ψ, [X,P]ψ⟩ = iℏ for normalized ψ. Substituting:
$$\sigma_X \sigma_P \geq \frac{1}{2}|i\hbar| = \frac{\hbar}{2}$$

## Implementation notes

We define ℏ = 1 (natural units). The hypothesis `h_canonical` requires the
expectation value of the commutator to equal iℏ, rather than assuming an
operator equation [X, P] = iℏI, which would require extending our framework
to handle operator-valued commutators.

## Physical interpretation

This is the mathematical content of Heisenberg's 1927 uncertainty principle:
simultaneous sharp measurement of position and momentum is impossible.
The bound ℏ/2 is saturated by Gaussian wave packets (coherent states).

## References

* [Heisenberg, "Über den anschaulichen Inhalt der quantentheoretischen
  Kinematik und Mechanik"][heisenberg1927]
* [Robertson, "The uncertainty principle"][robertson1929]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], Section 3.5

## Tags

Heisenberg, uncertainty principle, canonical commutation relation
-/
namespace QuantumMechanics.Heisenberg
open QuantumMechanics.Schrodinger QuantumMechanics.Robertson QuantumMechanics.UnboundedObservable InnerProductSpace Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def ℏ : ℝ := 1

theorem heisenberg_uncertainty_principle
    (X P : UnboundedObservable H)
    (ψ : H)
    (h : ShiftedDomainConditions X P ψ)
    (h_canonical : ⟪ψ, commutatorAt X P ψ h.toDomainConditions⟫_ℂ = Complex.I * (ℏ : ℂ)) :
    X.stdDev ψ h.h_norm h.hψ_A * P.stdDev ψ h.h_norm h.hψ_B ≥ (ℏ : ℝ )/ 2 := by
  have h_robertson := robertson_uncertainty X P ψ h
  rw [h_canonical] at h_robertson
  have h_norm_iℏ : ‖Complex.I * (ℏ : ℂ)‖ = (ℏ : ℝ) := by
    simp only [norm_mul, Complex.norm_I, one_mul]
    have ℏ_pos : ℏ > 0 := by unfold ℏ; norm_num
    exact Complex.norm_real ℏ ▸ abs_of_pos ℏ_pos
  linarith [h_robertson, h_norm_iℏ]

  end QuantumMechanics.Heisenberg
