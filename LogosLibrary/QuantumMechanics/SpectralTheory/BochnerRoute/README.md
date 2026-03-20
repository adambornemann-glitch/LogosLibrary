# Bochner's Theorem

> *A continuous positive-definite function f : ℝ → ℂ is the
> Fourier–Stieltjes transform of a unique finite positive Borel
> measure on ℝ.*

This directory contains a machine-checked proof of Bochner's theorem in
Lean 4 against Mathlib, following the classical route through Fourier
uniqueness and the GNS construction.

## The theorem

A function f : ℝ → ℂ is **positive-definite** if

$$
\sum_{i=1}^n \sum_{j=1}^n \bar{c}_i\, c_j\, f(t_i - t_j) \;\geq\; 0
$$

for all finite collections of points and coefficients, and
**continuous positive-definite** if additionally continuous at 0
(which forces continuity everywhere — proved in `Continuity.lean`).

**Bochner's theorem** says that f is continuous positive-definite if and
only if there exists a unique finite positive Borel measure μ on ℝ with

$$
f(t) \;=\; \int_{\mathbb{R}} e^{i\omega t}\,d\mu(\omega)
\qquad \forall\, t \in \mathbb{R}.
$$

In Lean (`Existence/Spectral.lean`):
```lean
theorem bochner_theorem (f : ℝ → ℂ) (hf : IsContinuous f) :
    ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ
```

The input `IsContinuous f` bundles `PositiveDefinite f`, `IsHermitian f`,
and `ContinuousAt f 0`.

## Axiom audit

The proof uses **one axiom** beyond Lean's kernel and Mathlib:

| Axiom | File | Status |
|:---|:---|:---|
| `spectral_scalar_measure_exists` | `SpectralTheory/SpectralAxiom.lean` | To be discharged via Cayley transform |

This axiom asserts that for any strongly continuous one-parameter unitary
group U(t) on a Hilbert space and any vector ξ, the correlation function
t ↦ ⟨ξ, U(t)ξ⟩ is the Fourier transform of a finite positive Borel
measure. It is a consequence of the spectral theorem for self-adjoint
operators. The discharge plan is to prove the spectral theorem via the
Cayley transform route: the Cayley transform of a self-adjoint operator
is unitary (already proved in `CayleyTransform/Transform.lean`), and the
spectral theorem for bounded unitary operators gives a projection-valued
measure that pulls back to ℝ.

The axiom is consumed exactly once, in `Existence/Spectral.lean`. Every
other result in this directory — Fourier uniqueness, the GNS construction,
positive-definite function theory, spectral measure machinery — is proved
from first principles.

## Proof architecture

The proof has two independent halves:

### Uniqueness (Fourier, fully proved)

If two finite positive Borel measures have the same characteristic
function, they are equal. The argument follows the classical Lévy
inversion route:

1. Convolve with the **Poisson kernel** Pε(x) = ε/(π(x² + ε²))
2. **Fubini** shows the Poisson integral of μ depends only on the
   characteristic function
3. Integrating over an interval (a, b] and sending **ε → 0** via dominated
   convergence recovers μ((a, b]) at continuity points
4. **Countably many atoms** + right-continuity of the distribution function
   extend the agreement to all intervals (a, b]
5. `Measure.ext_of_Ioc` finishes the job

Details: [`Fourier/README.md`](Fourier/README.md)

### Existence (GNS → Stone → Spectral, one axiom)

Every continuous positive-definite function is the Fourier transform of a
measure. The argument builds a Hilbert space from f and extracts the
measure via spectral theory:

1. **GNS construction.** Build a pre-inner product on formal sums ℝ →₀ ℂ,
   quotient by the null space, complete to a Hilbert space 𝓗, and extend
   the translation action to a strongly continuous unitary group U(t) with
   a cyclic vector ξ satisfying f(t) = ⟨ξ, U(t)ξ⟩.

2. **Stone's theorem** (proved in `UnitaryEvo/Stone.lean`). The unitary
   group has a self-adjoint generator A with U(t) = exp(itA).

3. **Spectral theorem** (axiom). The self-adjoint operator A has a
   projection-valued measure E, giving ⟨ξ, U(t)ξ⟩ = ∫ eⁱᵗλ d⟨E(λ)ξ, ξ⟩.

The representing measure is μ(S) = ⟨E(S)ξ, ξ⟩, and the argument
composes in four lines:

$$
f(t) = \langle\xi, U(t)\xi\rangle
     = \langle\xi, e^{itA}\xi\rangle
     = \int e^{it\lambda}\,d\langle E(\lambda)\xi,\xi\rangle
     = \int e^{it\lambda}\,d\mu(\lambda).
$$

Details: [`GNS/README.md`](GNS/README.md)

### The theorem itself

`bochner_theorem` combines existence and uniqueness in six lines:
existence gives a measure, and any other measure with the same Fourier
transform equals it by `fourier_uniqueness`.

## Positive-definite function theory

The files at the top level of `BochnerRoute/` develop the theory of
positive-definite functions needed by both halves of the proof.

**Definitions** (`PositiveDefinite.lean`). `PositiveDefinite f` requires
the quadratic form to have non-negative real part. `IsHermitian f`
requires f(−t) = conj(f(t)). `PositiveDefiniteContinuous f` bundles
PD + continuity at 0. These are separate hypotheses because Hermitian
symmetry does not follow from the real-part PD condition alone — it holds
automatically for correlation functions and Fourier transforms of positive
measures, but must be assumed or derived in general.

**Properties** (`PdProperties.lean`). From PD alone: f(0).re ≥ 0, and
two-point bounds from specialising the quadratic form with c = (1, ±1)
and c = (1, ±i). From PD + Hermitian: the sharp norm bound ‖f(t)‖ ≤ f(0).re,
proved by optimising over coefficients c = (conj(f(t)), −‖f(t)‖). Also
defines `pdVariance f h = f(0).re − Re(f(h))`, which measures the drop
from the maximum.

**Continuity** (`Continuity.lean`). The `IsContinuous f` bundle (PD +
Hermitian + continuous at 0) and the oscillation bound
‖f(s) − f(t)‖² ≤ 2 · f(0).re · pdVariance f (s − t), proved via the
3-point PD condition. This gives: continuity at 0 implies continuity
everywhere, uniformly.

## Spectral measure theory

**Spectral measures** (`SpectralMeasure.lean`). Axiomatisation of
projection-valued measures via `IsSpectralMeasure`, the Stieltjes
construction of the scalar spectral measure μ_ψ(B) = ⟨E(B)ψ, ψ⟩,
and the proof that the two constructions (Stieltjes and direct
σ-additive) agree.

**Unitary connection** (`UnitaryConnection.lean`). The bridge between
unitary groups and spectral measures: the correlation function
t ↦ ⟨U(t)ψ, ψ⟩ is positive-definite and continuous (hence satisfies
Bochner's hypotheses), the Bochner measure equals the spectral scalar
measure (by Fourier uniqueness), and the polarisation identity recovers
off-diagonal terms ⟨E(B)ψ, φ⟩ from diagonal ones.

## File map
```
BochnerRoute/
├── README.md                        ← you are here
│
│   ── Positive-definite function theory ──
├── PositiveDefinite.lean            — Definitions: PositiveDefinite, PositiveDefiniteContinuous
├── PdProperties.lean                — PD properties, Hermitian symmetry, sharp norm bound
├── Continuity.lean                  — IsContinuous, oscillation bound, global continuity
│
│   ── Spectral measure theory ──
├── SpectralMeasure.lean             — PVM axioms, Stieltjes construction, scalar measure
├── UnitaryConnection.lean           — Unitary correlation → PD → Bochner → spectral
│
│   ── Uniqueness (fully proved) ──
├── Fourier/
│   ├── README.md
│   ├── PoissonKernel/Lemmas.lean    — §1: Poisson kernel, ∫(1+x²)⁻¹ = π
│   ├── ArctanPrim.lean              — §2: Arctan primitive and bounds
│   ├── Bridge.lean                  — §3: Poisson–Fourier bridge (Fubini)
│   ├── ArctanLim.lean               — §4: Pointwise limits as ε → 0
│   ├── Distribution.lean            — §5: DCT for integrated Poisson
│   ├── Agreement.lean               — §6: Agreement on (a,b] at continuity points
│   ├── ContPoints.lean              — §6.5: Countable atoms, density, extension
│   └── Unique.lean                  — §7: fourier_uniqueness
│
│   ── Existence (one axiom) ──
├── GNS/
│   ├── README.md
│   ├── PreHilbert/                  — Stage 1: pre-inner product on ℝ →₀ ℂ
│   │   ├── Defs.lean                ·   pdInner, translate
│   │   ├── Evolution.lean           ·   Basis evaluation (simp lemma)
│   │   ├── Linearity.lean           ·   Right-linearity, right-scalar
│   │   ├── Conjugate.lean           ·   Conjugate symmetry (uses IsHermitian)
│   │   ├── PosSemiDef.lean          ·   0 ≤ Re⟨α,α⟩ (uses PositiveDefinite)
│   │   ├── TransAction.lean         ·   U(t): linearity, group law, isometry
│   │   ├── Cyclic.lean              ·   ξ = δ₀, f(t) = ⟨ξ, U(t)ξ⟩
│   │   └── NormEst.lean             ·   ‖U(t)ξ − ξ‖² = 2·pdVariance
│   ├── PreHilbert.lean              — Barrel import + Cauchy–Schwarz
│   ├── Completion/                  — Stage 2: quotient, complete, unitary group
│   │   ├── NullSpace.lean           ·   Null space N, quotient, inner product
│   │   ├── Bundler.lean             ·   GNSData interface
│   │   ├── Constructor.lean         ·   gnsConstruction (builds GNSData)
│   │   ├── UnitaryGroup.lean        ·   GNSUnitaryGroup specification
│   │   ├── ConstructorII/
│   │   │   ├── Lemmas.lean          ·   Translation lifted through quotient & completion
│   │   │   └── StronglyCont.lean    ·   Strong continuity (ε/3 argument)
│   │   ├── ConstructorII.lean       ·   gnsUnitaryConstruction
│   │   ├── Cyclic.lean              ·   f(t) = ⟨ξ, U(t)ξ⟩_𝓗
│   │   └── ToStone.lean             ·   Package as OneParameterUnitaryGroup
│   ├── Theorem.lean                 — gns_theorem
│   └── TODO.lean                    — Uniform oscillation bound (sorry)
│
│   ── The theorem ──
└── Existence/
    └── Spectral.lean                — bochner_existence, bochner_theorem
```

## External dependencies

| Module | What it provides | Status |
|:---|:---|:---|
| `UnitaryEvo/Stone.lean` | Stone's theorem: U(t) = exp(itA) | Proved |
| `UnitaryEvo/Bochner.lean` | One-parameter unitary group API | Proved |
| `SpectralTheory/SpectralAxiom.lean` | Spectral theorem (scalar form) | **Axiom** |
| `CayleyTransform/Transform.lean` | Cayley transform is unitary | Proved |
| Mathlib | Everything else | — |

## What this replaces

The axiom `measure_eq_of_fourier_eq` (Fourier uniqueness) that was
previously assumed is now a theorem. The only remaining axiom in the
proof of Bochner's theorem is the spectral theorem.

## References

- S. Bochner, *Monotone Funktionen, Stieltjessche Integrale und
  harmonische Analyse*, Math. Ann. **108** (1933), 378–410
- P. Lévy, *Calcul des Probabilités* (1925), §24
- W. Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
- G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3
- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I*,
  Chapters II and VII
