# Spectral Theory for Unbounded Self-Adjoint Operators

This directory contains the spectral theorem for unbounded self-adjoint
operators on Hilbert spaces, developed via three converging routes,
culminating in the Borel functional calculus and its application to the
Dirac equation.

## Mathematical content

The **spectral theorem** states that every self-adjoint operator A on a
Hilbert space admits a unique projection-valued measure E such that

$$
A \;=\; \int_{\mathbb{R}} \lambda\, dE(\lambda).
$$

For unbounded operators, this requires careful domain handling: the domain
of A equals {ψ : ∫|λ|² dμ_ψ < ∞} where μ_ψ(B) = ⟨E(B)ψ, ψ⟩.

We construct the spectral measure via three routes that are proven to agree:

1. **Bochner route**: The function t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite,
   hence by Bochner's theorem equals the Fourier transform of a measure
   μ_ψ. Bochner's theorem itself — both existence and uniqueness — is
   proved in [`BochnerRoute/`](BochnerRoute/README.md).

2. **Resolvent route**: Stone's formula recovers E from the resolvent via
   ⟨E(a,b]ψ, ψ⟩ = lim_{ε→0⁺} (1/π) ∫_a^b Im⟨R(t+iε)ψ, ψ⟩ dt.

3. **Cayley route**: The Cayley transform U = (A−i)(A+i)⁻¹ is unitary;
   its spectral measure pulls back to give E for A. It's README can be
   found here [`CayleyTansform/`](CayleyTransform/README.md)




## Dependency graph
```
                    UnitaryEvo/Stone.lean
                           │
                           ▼
         ┌─────────────────┴─────────────────┐
         │                                   │
         ▼                                   ▼
    Cayley.lean ◄──────────────────► Routes.lean
         │                                   │
         │         (three routes agree)      │
         │                   ▲               │
         │                   │               │
         │            BochnerRoute/          │
         │       (Bochner's theorem,         │
         │        Fourier uniqueness)        │
         │                                   │
         └─────────────┬─────────────────────┘
                       │
                       ▼
               FunctionalCalc.lean
                       │
                       ▼
               DiracOperator.lean
```

## Main results by file

### Cayley.lean — The Cayley transform

The Cayley transform establishes a bijection between self-adjoint
operators and unitary operators missing 1 from their spectrum.

**Definitions:**
- `cayleyTransform`: U = (A − i)(A + i)⁻¹
- `inverseCayleyTransform`: A = i(1 + U)(1 − U)⁻¹

**Theorems:**
- `cayleyTransform_unitary`: The Cayley transform of a self-adjoint operator is unitary
- `cayley_inverse_domain`: dom(A) = range(1 − U)
- `cayley_eigenvalue_correspondence`: λ ∈ σ(A) ↔ (λ−i)/(λ+i) ∈ σ(U)
- `cayley_spectrum_correspondence`: The spectral measures correspond via μ ↦ (μ−i)/(μ+i)

**Axioms (1):**
- `exists_compatible_spectral_measures`: ∃ compatible E_A, E_U (the spectral theorem)

### BochnerRoute/ — Bochner's theorem

A self-contained proof of Bochner's theorem: a continuous positive-definite
function on ℝ is the Fourier–Stieltjes transform of a unique finite positive
Borel measure.

**Uniqueness** is fully proved via Lévy inversion with the Poisson kernel.
**Existence** goes through the GNS construction, Stone's theorem, and the
spectral theorem (the single axiom in its critical path).

The full proof architecture, file map, and axiom audit are documented in
[`BochnerRoute/README.md`](BochnerRoute/README.md).

**Axioms in critical path: 1** (`spectral_scalar_measure_exists` in
`SpectralAxiom.lean`, a consequence of the spectral theorem).

### Routes.lean — Two routes to spectral measures

Constructs spectral measures from unitary groups via complementary
approaches, consuming the Bochner route and the resolvent route.

**Definitions:**
- `IsSpectralMeasure`: Projection-valued measure axioms
- `bochner_measure`: Measure from positive-definite function via Bochner's theorem
- `spectral_scalar_measure`: μ_ψ(B) = ⟨E(B)ψ, ψ⟩
- `lorentzian`: ε/((s−t)² + ε²), the approximation to δ(s−t)

**Theorems:**
- `bochner_measure_fourier`: ⟨U(t)ψ, ψ⟩ = ∫ eⁱᵗˢ dμ_ψ(s)
- `stone_formula`: ⟨E(a,b]ψ, ψ⟩ = lim (1/π) ∫ Im⟨R(t+iε)ψ, ψ⟩ dt
- `spectral_self_adjoint`: ⟨E(B)ψ, φ⟩ = ⟨ψ, E(B)φ⟩
- `spectral_scalar_measure_finite`: μ_ψ(ℝ) = ‖ψ‖² < ∞

**Axioms (~14):**
- Lorentzian approximation properties, Stone's formula limit exchange
- Fubini/DCT applications for interchanging limits
- (Bochner's theorem and Fourier uniqueness are no longer axioms —
  these are now proved in [`BochnerRoute/`](BochnerRoute/README.md))

### FunctionalCalc.lean — Borel functional calculus

The functional calculus Φ : f ↦ f(A) = ∫f dE is a \*-homomorphism.

**Definitions:**
- `functionalDomain`: {ψ : ∫|f|² dμ_ψ < ∞}
- `functionalDomainSubmodule`: Domain as a ℂ-submodule
- `boundedFunctionalCalculus`: f(A) for bounded f, as H →L[ℂ] H
- `functionalCalculus`: f(A) for general f, on functionalDomainSubmodule
- `IsSpectralMeasureFor`: E is the spectral measure of generator A

**Theorems:**
- `functionalCalculus_add`: (f + g)(A) = f(A) + g(A)
- `functionalCalculus_mul`: (fg)(A) = f(A) ∘ g(A)
- `functionalCalculus_conj`: f̄(A) = f(A)\*
- `functionalCalculus_one`: 1(A) = I
- `functionalCalculus_indicator`: 𝟙_B(A) = E(B)
- `generator_eq_spectral_integral`: A = ∫ s dE(s) on dom(A)
- `generator_domain_eq_functional_domain`: dom(A) = {ψ : ∫|s|² dμ_ψ < ∞}
- `three_routes_agree`: Bochner, Stieltjes, Cayley routes produce same E
- `boundedFunctionalCalculus_nonneg`: f ≥ 0 ⟹ ⟨Φ(f)ψ, ψ⟩ ≥ 0
- `boundedFunctionalCalculus_mono`: f ≤ g ⟹ ⟨Φ(f)ψ, ψ⟩ ≤ ⟨Φ(g)ψ, ψ⟩

**Axioms (~22):**
- Spectral integral construction and properties
- Generator-spectral correspondence
- Three routes agreement

### DiracOperator.lean — Relativistic quantum mechanics

The Dirac equation for spin-1/2 particles, from Clifford algebra to the
Born rule.

**Definitions:**
- `diracAlpha1`, `diracAlpha2`, `diracAlpha3`, `diracBeta`: 4×4 Dirac matrices
- `gamma0` through `gamma3`, `gamma5`: Covariant gamma matrices
- `DiracMatrices`: Abstract Clifford algebra specification
- `DiracHamiltonian`: H_D = −iℏc(α·∇) + βmc² as unbounded operator
- `DiracSpectralData`: Full spectral decomposition
- `diracSpectrum`: (−∞, −mc²] ∪ [mc², ∞)
- `electronProjection`, `positronProjection`: Spectral projections
- `diracCurrent`: jᵘ = ψ̄γᵘψ
- `probabilityDensity`: ρ = j⁰ = ψ†ψ

**Theorems (Clifford algebra — all proved by computation):**
- `diracAlpha1_sq` etc.: αᵢ² = β² = I
- `diracAlpha12_anticommute` etc.: {αᵢ, αⱼ} = 0
- `clifford_00` through `clifford_33`: All 16 relations {γᵘ, γᵛ} = 2ηᵘᵛI
- `gamma_trace_two`: Tr(γᵘγᵛ) = 4ηᵘᵛ
- `gamma_trace_three`: Tr(γᵘγᵛγᵖ) = 0
- `gamma5_sq`: (γ⁵)² = I
- `gamma5_anticommutes`: {γ⁵, γᵘ} = 0

**Theorems (spectral structure):**
- `dirac_unbounded_below`, `dirac_unbounded_above`: H_D unbounded both directions
- `dirac_not_semibounded`: No lower bound exists
- `electron_positron_orthogonal`: E₊ E₋ = 0
- `dirac_spectral_gap_zero`: E((−mc², mc²)) = 0
- `electron_positron_complete`: E₊ + E₋ = 1

**Theorems (probability):**
- `current_zero_eq_norm_sq`: j⁰ = Σ|ψₐ|²
- `current_zero_nonneg`: ρ ≥ 0
- `probability_conserved`: d/dt ∫ρ d³x = 0
- `born_rule_valid`: ρ/∫ρ is a valid probability distribution

**Axioms (11):**
- Spectral theory for Dirac operator
- PDE results (current conservation, continuity equation, divergence theorem)

## Proof architecture

### The spectral theorem strategy
```
Self-adjoint A ──Stone's thm──► Unitary group U(t) = e^{itA}
       │                                │
       │                                ├──► Bochner route (BochnerRoute/)
       │                                │    ⟨U(t)ψ,ψ⟩ positive-definite
       │                                │         │
       │                                │         ▼
       │                                │    Measure μ_ψ via Bochner's theorem
       │                                │    (1 axiom: spectral theorem)
       │                                │
       │                                └──► Resolvent route
       │                                     R(z) = (A−z)⁻¹
       │                                          │
       │                                          ▼
       │                                     Stone's formula for E(a,b]
       │
       └──Cayley──► Unitary U = (A−i)(A+i)⁻¹
                          │
                          ▼
                    Spectral measure for U on 𝕋
                          │
                          ▼
                    Pull back to E on ℝ
```

### Clifford algebra verification

All 16 gamma matrix relations are verified by brute-force computation:
```lean
ext a b
fin_cases a <;> fin_cases b <;>
simp [gamma matrices, Matrix.mul_apply, ...]
```

Computationally expensive but axiom-free.

## Physical interpretation

### The spectral theorem and quantum measurement

The spectral measure E directly encodes measurement:

- E(B) projects onto states where "observable A has value in B"
- ⟨E(B)ψ, ψ⟩ = probability of measuring A ∈ B in state ψ
- f(A) = ∫f dE is the observable "f of A"

### The Dirac equation

The Dirac Hamiltonian H_D = −iℏc(α·∇) + βmc² describes spin-1/2
particles (electrons, quarks), their antiparticles (the negative energy
spectrum), and the relativistic dispersion relation E² = (pc)² + (mc²)².
The spectral gap (−mc², mc²) separates particle and antiparticle states.

### Probability conservation

Unlike Klein–Gordon, Dirac has positive-definite probability density:
ρ = ψ†ψ ≥ 0 (proved: `current_zero_nonneg`), conservation dP/dt = 0
(proved: `probability_conserved`), and the Born rule follows as a theorem.

## Axiom summary

| File | Count | Categories |
|:---|:---|:---|
| Cayley | 1 | Spectral theorem existence |
| BochnerRoute | 1 | Spectral theorem (scalar form) |
| Routes | ~14 | Resolvent theory, Stone's formula, measure theory |
| FunctionalCalc | ~22 | Spectral integral construction |
| DiracOperator | 11 | Spectral theory for Dirac, PDE results |

Most axioms are "soft" — they assert well-known theorems that require
substantial measure-theoretic or PDE machinery to formalise: dominated
and monotone convergence applications, the Leibniz integral rule, the
divergence theorem, and various limit exchanges. The single "hard" axiom
is `exists_compatible_spectral_measures` in `Cayley.lean`, which *is*
the spectral theorem.

The Bochner route's axiom `spectral_scalar_measure_exists` in
`SpectralAxiom.lean` is a scalar consequence of the same spectral
theorem; both will be discharged together.

**Previously axiomatised, now proved:**
- `fourier_uniqueness` — Fourier uniqueness for finite measures
  (Lévy inversion, [`BochnerRoute/Fourier/`](BochnerRoute/Fourier/README.md))
- `bochner_existence` — Bochner's theorem, existence direction
  (GNS + Stone, [`BochnerRoute/GNS/`](BochnerRoute/GNS/README.md))
- `bochner_theorem` — Full Bochner's theorem (existence + uniqueness,
  [`BochnerRoute/Existence/Spectral.lean`](BochnerRoute/Existence/Spectral.lean))

## References

- S. Bochner, *Monotone Funktionen, Stieltjessche Integrale und
  harmonische Analyse*, Math. Ann. **108** (1933), 378–410
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*,
  Chapters II, VII–VIII
- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*,
  Chapters 4–5
- B. Thaller, *The Dirac Equation*, Springer (1992)
- W. Rudin, *Functional Analysis*, 2nd ed., Chapters 12–13
- B. C. Hall, *Quantum Theory for Mathematicians*, Chapters 7, 10

