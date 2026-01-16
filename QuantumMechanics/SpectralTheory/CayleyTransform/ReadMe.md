# The Cayley Transform for Unbounded Self-Adjoint Operators

This directory contains a Lean 4 formalization of the **Cayley transform**, which establishes a fundamental bijection between self-adjoint operators and unitary operators on a Hilbert space. Given a self-adjoint operator $A$, the Cayley transform produces the unitary operator

$$U = (A - iI)(A + iI)^{-1}$$

This correspondence is essential in quantum mechanics (where self-adjoint operators represent observables) and in the spectral theory of unbounded operators.

## Mathematical Background

The Cayley transform exploits the fact that for a self-adjoint operator $A$, the resolvent $(A + iI)^{-1}$ is a bounded operator defined on all of $\mathcal{H}$. The key insight is that the map $\psi \mapsto A\psi + i\psi$ is an isometry from $\text{dom}(A)$ (with the graph norm) onto $\mathcal{H}$, and the Cayley transform acts by:

$$U(A\psi + i\psi) = A\psi - i\psi$$

The eigenvalue correspondence follows from the Möbius transformation $\mu \mapsto \frac{\mu - i}{\mu + i}$, which maps $\mathbb{R}$ bijectively onto the unit circle minus $\{1\}$.

## File Structure

| File | Description |
|------|-------------|
| `Basic.lean` | Module docstring and imports; entry point for the directory |
| `Unitary.lean` | Theory of unitary operators: preservation of inner products, normality, approximate eigenvalues |
| `Mobius.lean` | Complex analysis lemmas for the Möbius map $\mu \mapsto \frac{\mu - i}{\mu + i}$ |
| `Transform.lean` | Core definition of `cayleyTransform` and proofs of isometry/unitarity |
| `Inverse.lean` | Inverse Cayley transform and the domain characterization $\text{dom}(A) = \text{range}(I - U)$ |
| `Eigenvalue.lean` | Eigenvalue correspondence between $A$ and $U$ |
| `Spectrum.lean` | Full spectral correspondence (approximate point spectrum) |
| `SpectralMeasure.lean` | Compatibility of spectral measures (scaffolding for spectral theorem) |

## Main Results

### Unitarity of the Cayley Transform
```lean
theorem cayleyTransform_unitary (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    Unitary (cayleyTransform gen hsa)
```

### Eigenvalue Correspondence
```lean
theorem cayley_eigenvalue_correspondence (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) (μ : ℝ) :
    (∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ)
```

### Spectral Correspondence
```lean
theorem cayley_spectrum_correspondence (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) (μ : ℝ) :
    (∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) ↔
    IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)
```

### Domain Characterization
```lean
theorem generator_domain_eq_range_one_minus_cayley (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (gen.domain : Set H) = LinearMap.range (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa)
```

## Dependencies

This formalization depends on:
- `LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent` — resolvent operators for generators
- `LogosLibrary.QuantumMechanics.Generators` — theory of generators of one-parameter unitary groups
- Standard Mathlib imports for Hilbert spaces and continuous linear maps

## Current Status

**Complete:**
- Cayley transform definition and basic properties
- Isometry and unitarity proofs  
- Eigenvalue correspondence (both directions)
- Full spectral correspondence
- Domain characterization
- Inverse transform construction


## References

- Reed, M. and Simon, B. *Methods of Modern Mathematical Physics I: Functional Analysis*, Chapter VIII
- Schmüdgen, K. *Unbounded Self-adjoint Operators on Hilbert Space*, Chapter 5
- Rudin, W. *Functional Analysis*, Chapter 13

## Author

Adam Bornemann, 2025–2026

---

*Part of the LogosLibrary quantum mechanics formalization project.*
