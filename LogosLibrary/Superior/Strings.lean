/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Strings.lean
-/
import LogosLibrary.Superior.Strings.Basic
import LogosLibrary.Superior.Strings.Thermal
import LogosLibrary.Superior.Strings.Topology
import LogosLibrary.Superior.Strings.Quaternion
import LogosLibrary.Superior.Strings.Synthesis
/-!
=====================================================================
# SUPERIOR-STRING THEORY
=====================================================================

A machine-verified framework for QCD flux tubes where target-space
time is replaced by the modular flow parameter from Tomita-Takesaki
theory, the worldsheet evolution parameter represents entropy flow,
and the critical dimension is D = 3 (spatial only).

## Architecture

The library is organized into five files:

### `Basic`
Definitions and derived quantities from a single input: string
tension σ > 0. Contains `QCDString` (the fundamental structure),
scale identities (m·Δx = 1), the critical dimension D_spatial = 3,
the Lüscher coefficient -π/12, the gravitational hierarchy
G_eff·σ = 2√3, entropic time definitions (τ_C, T), and the
collapse-temperature conjugacy τ_C·T = 1/(2π).

### `Thermal`
Lorentz covariance of the entropic framework. The Ott temperature
transformation T' = γT, collapse timescale dilation τ_C' = τ_C/γ,
entropy flow invariance σ_R' = σ_R, modular Hamiltonian invariance
K' = K, emergent time dilation t' = t/γ, and the frame-independence
of the τ_C·T identity. Connects to the `ThermalTime.Basic` library.

### `Topology`
The Hopf fibration S¹ ↪ S³ → S². The explicit Hopf map with the
norm identity |π(q)|² = |q|⁴, surjectivity onto S², the S¹ fiber
action (rotation, periodicity, composition), preservation of the
Hopf map along fibers (the single-axion theorem), the division
algebra hierarchy (ℝ, ℂ, ℍ, 𝕆), and the Hopf tower nesting.

### `Quaternion`
The algebraic engine. The full multiplication table (𝐢𝐣 = 𝐤, etc.),
the su(2) commutation relations [𝐢,𝐣] = 2𝐤, the Jacobi identity,
pure imaginary quaternions as ℝ³, the product decomposition into
dot and cross products, norm multiplicativity |pq|² = |p|²|q|²,
the conjugation rotation action with norm preservation and pure
imaginary closure, the Hopf map as conjugation on 𝐢, the Fueter
operator symbol calculus (∂̄*∂̄ = Δ₄), and the quaternionic
entropic parameter.

### `Synthesis`
The master theorem `superior_string_theory`: ten results proven
simultaneously from the preceding four files. Zero sorry. Zero
free parameters.

## The Ten Results

|  # | Result                    | Source     | Statement                        |
|----|---------------------------|------------|----------------------------------|
|  1 | Critical dimension        | Basic      | D_spatial = 3                    |
|  2 | Lüscher coefficient       | Basic      | -π/12 (matches lattice QCD)      |
|  3 | Hierarchy product         | Basic      | G_eff · σ = 2√3                  |
|  4 | Collapse-temperature      | Basic      | τ_C · T = 1/(2π)                 |
|  5 | Modular invariance        | Thermal    | K' = K under boosts              |
|  6 | Time dilation             | Thermal    | t' = t/γ (emergent)              |
|  7 | Entropy invariance        | Thermal    | σ_R' = σ_R                       |
|  8 | Single axion              | Topology   | S¹ fiber preserved by Hopf       |
|  9 | Lie algebra               | Quaternion | [𝐢, 𝐣] = 2𝐤                       |
| 10 | Fueter-Laplacian          | Quaternion | ∂̄*∂̄ = Δ₄                         |

## Key Insight

The naive ghost counting giving D = 3 instead of D = 4 is not a
failure. Time is not a target-space dimension; time IS the entropic
evolution parameter σ_R. The target space is purely spatial.
D_spatial = 3 is the critical dimension.

## Dependencies

- `Mathlib`: real analysis, quaternion algebra, trigonometry
- `LogosLibrary.Relativity.Thermodynamics.Ott`: Lorentz γ, Ott transformation
- `LogosLibrary.ThermalTime.Basic` (via Thermal): thermal time framework

## References

- Connes, Rovelli: "Von Neumann algebra automorphisms and
  time-thermodynamics relation" (1994)
- Barbour, Mercati et al.: Shape dynamics
- Polchinski, Strominger: Effective string theory
- Jacobson: "Thermodynamics of spacetime" (1995)

                                                                  ∎
-/
