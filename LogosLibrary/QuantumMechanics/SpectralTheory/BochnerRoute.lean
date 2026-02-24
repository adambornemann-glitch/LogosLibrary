/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.PositiveDefinite
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.SpectralMeasure
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.UnitaryConnection
/-!
# Spectral Bridge: Bochner Route

This module establishes the connection between strongly continuous one-parameter
unitary groups and projection-valued spectral measures via Bochner's theorem.

## Module structure

* `PositiveDefinite`: Positive-definite functions and Bochner's theorem
* `SpectralMeasure`: Projection-valued measures and scalar spectral measures
* `UnitaryConnection`: The bridge connecting unitary groups to spectral measures

## Overview

Given a unitary group `U(t)` with self-adjoint generator `A`, we construct the
spectral measure `E` satisfying `U(t) = ∫ e^{itλ} dE(λ)` via the Bochner route:

1. The correlation function `⟨U(t)ψ, ψ⟩` is positive-definite and continuous
2. Bochner's theorem gives a measure `μ_ψ` with `⟨U(t)ψ, ψ⟩ = ∫ e^{itλ} dμ_ψ`
3. Uniqueness shows `μ_ψ = ⟨E(·)ψ, ψ⟩` is the spectral scalar measure
4. Polarization recovers the full operator-valued spectral measure

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980]
* Bochner, "Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse" (1933)
-/
