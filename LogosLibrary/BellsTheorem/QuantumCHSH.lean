/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann

# Quantum Violation of the CHSH Inequality

This file proves that quantum mechanics achieves |S| = 2√2 for appropriate
choices of state and observables, violating the LHV bound of 2.

## Main Results

* `quantum_chsh_value` : With Bell state and optimal observables, S = 2√2
* `tsirelson_bound` : No quantum state can exceed 2√2

## The Physical Setup

Alice and Bob share the singlet state |Ψ⁻⟩ = (|01⟩ - |10⟩)/√2.

Alice measures:
- A₀ = σ_z (Pauli Z)
- A₁ = σ_x (Pauli X)

Bob measures:
- B₀ = (σ_z - σ_x)/√2
- B₁ = -(σ_z + σ_x)/√2

These choices maximize the CHSH violation.
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Q_CHSH_Basic
import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Correlations
import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Violation
import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Tsirelson
