/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.ResolventKernel
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.SpectralRepresentation
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.StieltjesInversion
import LogosLibrary.QuantumMechanics.SpectralTheory.ResolventRoute.StonesFormula
/-!
# Spectral Bridge: Resolvent Route

This module establishes the connection between strongly continuous one-parameter
unitary groups and projection-valued spectral measures via Stone's formula and
Stieltjes inversion.

## Module structure

* `ResolventKernel`: Lorentzian kernel analysis, approximate identity
* `SpectralRepresentation`: R(z) = ∫ (λ-z)⁻¹ dE(λ)
* `StieltjesInversion`: μ(a,b] = lim_{ε→0} (1/π) ∫_a^b Im⟨R(t+iε)ψ,ψ⟩ dt
* `StonesFormula`: E(a,b) = s-lim_{ε→0} (1/2πi) ∫_a^b [R(t+iε) - R(t-iε)] dt

## Overview

The resolvent route recovers the spectral measure from the resolvent (Green's function)
via contour integration techniques:

1. The resolvent `R(z) = (A - z)⁻¹` is analytic off the spectrum
2. The imaginary part `Im(R(t+iε))` contains spectral information via the Lorentzian kernel
3. As `ε → 0`, the Lorentzian becomes a delta function, extracting the spectral measure
4. Stone's formula makes this precise for the operator-valued spectral projections

## Key identities

- `Im((s - (t+iε))⁻¹) = ε/((s-t)² + ε²)` (Lorentzian/Poisson kernel)
- `(s-(t+iε))⁻¹ - (s-(t-iε))⁻¹ = 2iε/((s-t)² + ε²)` (resolvent difference)
- `∫ ε/((s-t)² + ε²) ds = π` (Lorentzian total mass)
- `(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0` (approximate identity)

## Physical interpretation

This is the "physicist's approach" to spectral theory. The resolvent is the
Green's function, and the spectral density is extracted from its imaginary part
near the real axis. Stone's formula is equivalent to computing the discontinuity
across the branch cut of the resolvent.

## References

* Stone, "Linear Transformations in Hilbert Space" (1932)
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Chapter VII
* Stieltjes, "Recherches sur les fractions continues" (1894)
-/
