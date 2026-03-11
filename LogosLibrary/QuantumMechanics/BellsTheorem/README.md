# Bell's Theorem and the CHSH Inequality

✅ **Compiles. Zero `sorry`. Fully verified.**

The most complete formalization of Bell's theorem in any proof assistant: **46 files** covering the CHSH inequality, Tsirelson's bound, quantum violation, and extensive original extensions.

## Provenance

The foundation of this formalization is a faithful port of Echenim & Mhalla's Isabelle/HOL formalization of the CHSH inequality and Tsirelson's bound:

> M. Echenim and M. Mhalla, *A formalization of the CHSH inequality and Tsirelson's upper-bound in Isabelle/HOL*

**12 files (~2,600 lines)** are ported from their work, adapted to Lean 4 and Mathlib4. The remaining **34 files** are original extensions by Adam Bornemann.

### Ported Files (Echenim & Mhalla → Lean 4)

| File | Lines | Content |
|------|------:|---------|
| `Basic.lean` | 417 | Density matrices, observables, CHSH operator, LHV model, quantum violation witness |
| `LHV.lean` | 269 | Measure-theoretic LHV framework, response functions, Bell's theorem (|S| ≤ 2) |
| `CHSH_Basic.lean` | 371 | Spectral projections, dichotomic expectation bound (|Tr(Aρ)| ≤ 1), Kronecker product lemmas |
| `Separable.lean` | 181 | Separable states cannot violate CHSH |
| `Commuting.lean` | 68 | Commuting observables cannot violate CHSH |
| `Op_square.lean` | 270 | Commutator algebra, involution identities, S² = 4I − [A₀,A₁]·[B₀,B₁] |
| `UnitaryBounds.lean` | 247 | Unitary norm preservation, operator bounds for Tsirelson |
| `CommutatorAlgebra.lean` | 431 | Commutator squared identity, [A,B]² ≤ 4I, commutator product bounds |
| `Q_CHSH_Basic.lean` | 111 | Pauli matrices (σₓ, σᵧ, σ_z), algebraic properties |
| `Correlations.lean` | 144 | Alice/Bob observables, four correlation computations for Bell state |
| `Violation.lean` | 47 | Quantum CHSH value = 2√2, violation exceeds classical bound |
| `Tsirelson.lean` | 43 | Tsirelson's bound: ‖S‖ ≤ 2√2 for all quantum states |
| **Total ported** | **2,599** | |

### Original Extensions (Bornemann)

<!-- TODO: Fill in with the 34 original files -->

| File | Lines | Content |
|------|------:|---------|
| | | |
| **Total original** | **—** | |

## Main Results

### From the Port

These theorems reproduce and verify Echenim & Mhalla's Isabelle results in Lean 4:

| Theorem | Statement | File |
|---------|-----------|------|
| `bell_theorem` | ¬∃ LHV model with S = 2√2 | `LHV.lean` |
| `lhv_chsh_bound` | Under any LHV model, \|S\| ≤ 2 | `LHV.lean` |
| `CHSH_quantum_violation` | Bell state achieves \|S\| = 2√2 | `Basic.lean` |
| `quantum_chsh_value` | S = 2√2 (via explicit correlation computation) | `Violation.lean` |
| `tsirelson_bound'` | For all quantum states, \|S\| ≤ 2√2 | `Tsirelson.lean` |
| `CHSH_separable_bound` | Separable states satisfy \|S\| ≤ 2 | `Separable.lean` |
| `CHSH_commuting_bound` | Commuting observables satisfy \|S\| ≤ 2 | `Commuting.lean` |

### Original Extensions

<!-- TODO: Add theorems from the 34 original files -->

## Architecture

### Proof Strategy: CHSH Bound (Ported)

The classical bound |S| ≤ 2 follows from:
1. **Pointwise bound** (`chsh_pointwise_bound`): For a, a', b, b' ∈ {±1}, the CHSH expression satisfies |ab' − ab + a'b + a'b'| ≤ 2 via the factorization a(b'−b) + a'(b+b').
2. **Integration**: Since the integrand is bounded a.e. by 2 and μ is a probability measure, the integral is bounded by 2.

### Proof Strategy: Tsirelson's Bound (Ported)

The quantum bound |S| ≤ 2√2 follows from:
1. **CHSH² identity** (`CHSH_op_square`): S² = 4I − [A₀,A₁]·[B₀,B₁]
2. **Commutator bounds** (`comm_prod_ge_neg_four`): [A₀,A₁]·[B₀,B₁] ≥ −4I
3. **Operator norm**: S² ≤ 8I, so ‖S‖ ≤ 2√2

The proof proceeds through unitary operator theory — the product of two Hermitian involutions is unitary, and unitary operators satisfy ‖U + U†‖ ≤ 2.

### Proof Strategy: Quantum Violation (Ported)

The violation S = 2√2 is computed explicitly:
1. **State**: Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2
2. **Alice**: A₀ = σ_z ⊗ I, A₁ = σₓ ⊗ I
3. **Bob**: B₀ = I ⊗ (σ_z − σₓ)/√2, B₁ = I ⊗ −(σ_z + σₓ)/√2
4. **Each correlation** is computed by explicit 4×4 matrix multiplication and trace evaluation, yielding E(A₀,B₁) = E(A₁,B₀) = E(A₁,B₁) = 1/√2 and E(A₀,B₀) = −1/√2.

## Design Decisions

**Measure-theoretic LHV framework.** Following Echenim & Mhalla, the LHV hypothesis uses probability measures and almost-everywhere conditions rather than assuming a density function exists. This is the mathematically correct generality.

**Finite-dimensional matrices.** The formalization works with `Matrix (Fin n) (Fin n) ℂ` throughout. This is sufficient for CHSH (which is inherently finite-dimensional) and avoids the technicalities of unbounded operators.

**Explicit computation.** The quantum violation is proved by direct matrix arithmetic, not by abstract argument. Every correlation is computed entry-by-entry. This is verbose but leaves nothing to trust.

**Spectral projection method for expectation bounds.** The bound |Tr(Aρ)| ≤ 1 for dichotomic A is proved by decomposing A = P₊ − P₋ into spectral projections, showing both are positive semidefinite via Cauchy–Schwarz, and using Tr(P₊ρ) + Tr(P₋ρ) = 1 with Tr(P±ρ) ≥ 0.

## Dependencies

All ported files depend on Mathlib4. Key imports:
- `Mathlib.Analysis.InnerProductSpace.Basic` — Cauchy–Schwarz
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` — probability spaces
- `Mathlib.Algebra.Star.CHSH` — Mathlib's abstract CHSH infrastructure
- `Mathlib.LinearAlgebra.Matrix.Kronecker` — tensor products

## References

- J. S. Bell, *On the Einstein Podolsky Rosen paradox*, Physics **1** (1964), 195–200.
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, *Proposed experiment to test local hidden-variable theories*, Phys. Rev. Lett. **23** (1969), 880–884.
- B. S. Tsirelson, *Quantum generalizations of Bell's inequality*, Lett. Math. Phys. **4** (1980), 93–100.
- M. Echenim and M. Mhalla, *A formalization of the CHSH inequality and Tsirelson's upper-bound in Isabelle/HOL* (2023).
