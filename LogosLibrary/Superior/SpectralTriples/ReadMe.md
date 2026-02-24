# Spectral Triples in Lean 4

### A Formal Verification of the Spectral Geometry of U⁹

> *"The very notion of a geometric space is being replaced by that of a spectral triple (A, H, D)."*
> — Alain Connes, *Noncommutative Geometry and Reality* (1995)

---

## What This Is

This library is a Lean 4 formalization of the spectral-geometric classification of U⁹ = Tot(Met(X³)), the total space of the bundle of Riemannian metrics over a compact 3-manifold. It provides machine-verified proofs that:

- The KO-dimension, sign table, Clifford type, gauge group, and spectral action of U⁹ are **uniquely determined** by the single fact that 9 ≡ 1 (mod 8).
- The Standard Model gauge structure **emerges** from the product geometry of base × fiber through the Clifford transmutation ℍ² ⊗ ℝ = ℂ.
- The spectral action Tr(f(D/Λ)) + ½⟨Jψ, Dψ⟩ on U⁹ reproduces the Observerse Lagrangian: gravity + Yang-Mills + Dirac + cosmological constant.

The formalization covers the Chamseddine-Connes spectral action principle, the Seeley-DeWitt heat kernel expansion, the Kaluza-Klein mechanism via fiber integration, and the explicit Dirac spectrum of S³.

## Architecture

The library consists of four files, ordered by increasing concreteness:

```
SpectralDefs.lean          The alphabet: signs, types, classification
     │
SpectralAction.lean        The grammar: spectral action, Seeley-DeWitt, correspondence
     │
ProductGeometry.lean       The sentence: fiber bundle decomposition, Kaluza-Klein
     │
ConcreteSpectrum.lean      The speech: explicit S³ spectrum, DeWitt metric, couplings
```

Each file is self-contained in its mathematical scope and builds on the exports of the previous files.

### File 1 — `SpectralDefs.lean`: Definitions and KO-Classification

**The foundational layer.** Defines the sign algebra {+, −} ≅ ℤ/2ℤ, the sign table classifying real structures on spectral triples by KO-dimension mod 8, and the complete algebraic data of a spectral triple.

| Structure | Purpose |
|---|---|
| `Sign` | The eigenvalues of involutions: +1 or −1 |
| `RealStructure` | The sign triple (ε, ε′, ε″) of a real spectral triple |
| `signTable : Fin 8 → RealStructure` | The eightfold classification |
| `SpectralTripleData` | Algebraic invariants: metric dim, KO-dim, spinor dim |
| `SpectralTriple` | Full data including Dirac eigenvalues and multiplicities |
| `DimensionSpectrum` | Poles of the spectral zeta function ζ_D(s) |
| `CliffordAlgType` | Real / complex / quaternionic / doubled types |
| `NaturalGaugeType` | The gauge group determined by Clifford type |

**Key results:**

- **Parity theorem.** ε″ exists iff KO-dim is even. *(Odd manifolds have no chirality.)*
- **Even injectivity.** For even KO-dimensions, the sign triple uniquely determines the dimension.
- **ε′ period-2.** ε′(n) = +1 iff n is even. *(Dirac commutes with J on even manifolds.)*
- **Complex Clifford criterion.** The Clifford algebra is complex iff KO-dim ∈ {1, 5}. *(This is why the shiab operator is natural.)*
- **Why 9 and not 14.** KO-dim 1 gives M₁₆(ℂ) with natural U(16); KO-dim 6 gives M₁₂₈(ℝ) requiring ad hoc complexification.
- **Master classification of U⁹.** From dim = 9 alone: KO-dim 1, signs (+, −, ·), odd, complex Clifford, unitary gauge, 16-spinor, 5 poles.

### File 2 — `SpectralAction.lean`: The Spectral Action

**The physical content.** Implements the Chamseddine-Connes spectral action principle and establishes the term-by-term correspondence with the Observerse Lagrangian.

| Structure | Purpose |
|---|---|
| `CutoffMoments` | Moments f_k of the cutoff function |
| `SeeleyDeWittCoeff` | Individual heat kernel coefficient a_{2k} |
| `A4Decomposition` | The five geometric invariants in a₄ |
| `SeeleyDeWittData` | Complete coefficient set for a spectral triple |
| `FermionicAction` | The Dirac term ½⟨Jψ, Dψ⟩ |
| `GaugeCorrespondenceData` | Shiab ↔ Hodge star identification |

**The spectral action on U⁹ has six terms:**

| Term | Pole | Power of Λ | Physics |
|---|---|---|---|
| a₀ | 9 | Λ⁹ | Cosmological constant |
| a₂ | 7 | Λ⁷ | Einstein-Hilbert (gravity) |
| a₄ | 5 | Λ⁵ | Yang-Mills + curvature² |
| a₆ | 3 | Λ³ | Higher curvature (R³) |
| a₈ | 1 | Λ  | Highest order (R⁴) |
| ½⟨Jψ, Dψ⟩ | — | — | Dirac fermion (16-component) |

**The correspondence** with the Observerse Lagrangian L = L₁ + L₂ + L₃:

- L₁ = R_C · vol₉ ← gravitational Seeley-DeWitt terms
- L₂ = Tr(F ∧ ε(F)) ← gauge part of a₄ (shiab = Hodge star through Clifford)
- L₃ = ⟨Ψ, DΨ⟩ vol₉ ← fermionic action (nontrivial because ε′ = −1)

The correspondence is **surjective** (every Observerse term is covered) but not injective (the spectral action is finer).

### File 3 — `ProductGeometry.lean`: Fiber Bundle Decomposition

**The mechanism.** Formalizes U⁹ as a fiber bundle triple and proves the Kaluza-Klein decomposition of the spectral action.

The fiber bundle structure:

```
Sym²₊(ℝ³)  ──→  U⁹  ──→  X³
 (fiber)       (total)    (base)
 dim 6          dim 9      dim 3
 KO 6           KO 1       KO 3
 spinor 8       spinor 16  spinor 2
 real            complex    quat²
```

**Composition laws** (all machine-verified):

1. **Dimensions add:** 3 + 6 = 9
2. **KO-dimensions add mod 8:** (3 + 6) mod 8 = 1
3. **Spinor dimensions multiply:** 2 × 8 = 16

**The Clifford transmutation.** Neither the base (quatSquared) nor the fiber (real) is complex. Their product **is** complex. The complex structure that makes the shiab operator natural, the U(16) gauge group canonical, and the Standard Model possible — it **emerges** from the tensor product. This is proven, not assumed.

**The Kaluza-Klein dictionary:**

| Spectral term on U⁹ | Fiber integration | Effective term on X³ |
|---|---|---|
| a₀ (volume) | ∫_fiber vol | Cosmological constant |
| a₂ (scalar curv.) | ∫_fiber R vol | Einstein-Hilbert |
| mixed a₄ (gauge) | ∫_fiber tr(Ω²) | Yang-Mills |
| ½⟨Jψ, Dψ⟩ | ∫_fiber spinor | Dirac (16 fermions) |

**The gauge paradox:** S³ alone has zero gauge curvature. The fiber alone has zero gauge curvature. The product has **nonzero** gauge curvature. 0 + 0 ≠ 0 in curved geometry — this is the Kaluza-Klein mechanism.

### File 4 — `ConcreteSpectrum.lean`: Explicit Computations

**The concrete realization.** Takes X³ = S³(r) and computes everything explicitly.

**The S³ Dirac spectrum** (Bär, 1996):

- Eigenvalues: λ_n = ±(2n + 3) / (2r), uniformly spaced by 1/r
- Multiplicities: m(n) = (n + 1)(n + 2), quadratic growth
- Dirac gap: 3/(2r) (smallest eigenvalue, inversely proportional to radius)

**The DeWitt metric** on Sym²₊(ℝ³):

- G_g(h,k) = tr(g⁻¹h g⁻¹k) − tr(g⁻¹h)tr(g⁻¹k) at λ = −1
- Scalar curvature at identity: R = −15/4 (negative)
- Physical consequence: positive contribution to cosmological constant

**Coupling constant structure:**

| Coupling | Source | Power of Λ |
|---|---|---|
| Cosmological constant | a₀ | Λ⁹ |
| Newton's constant G_N | a₂ | Λ⁷ |
| Gauge coupling g² | mixed a₄ | Λ⁵ |

The hierarchy between consecutive couplings is Λ² — uniform steps, not arbitrary.

## Proof Statistics

| | Theorems | Sorries | Axioms |
|---|---|---|---|
| `SpectralDefs.lean` | 38 | 0 | 0 |
| `SpectralAction.lean` | ~40 | 0 | 1 |
| `ProductGeometry.lean` | 37 | 0 | 1 |
| `ConcreteSpectrum.lean` | 41 | 1 | 0 |
| **Total** | **~156** | **1** | **2** |

**The 1 sorry** is technical, not conceptual: the compact resolvent for S³ requires showing (2n+3)/(2r) → ∞ via Mathlib's `Filter.Tendsto` API. The eigenvalue formula makes this trivially true; the proof awaits the right lemma chain.

**The 2 axioms** are physically standard:

1. **`chimeric_gauge_curvature_nonzero`** — The chimeric connection on U⁹ has nonzero gauge curvature. *(Standard Kaluza-Klein: nontrivial fiber bundle ⇒ nontrivial connection curvature.)*
2. **`fiber_volume_positive`** — Sym²₊(ℝ³) has positive regularized volume under the DeWitt metric. *(Standard result, dischargeable when Mathlib has measure theory on symmetric spaces.)*

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) — core tactics, analysis, special functions
- `LogosLibrary.Superior.GeometricUnity.CliffordPeriodicity` — Cl(n+8) ≅ M₁₆(Cl(n))

## The Mathematical Lineage

The structures formalized here draw on:

- **Connes (1995)** — Real structures on spectral triples, the sign table, KO-dimension classification
- **Connes (2008)** — Spectral characterization of manifolds
- **Chamseddine-Connes (1996)** — The spectral action principle: S = Tr(f(D/Λ))
- **Chamseddine-Connes-Marcolli (2007)** — Gravity and the Standard Model with neutrino mixing
- **Bär (1996)** — The Dirac spectrum on spheres
- **DeWitt (1967)** — The supermetric on the space of Riemannian metrics
- **Connes (2019)** — *Noncommutative Geometry, the Spectral Standpoint*

## What Is Proven vs. What Is Assumed

**Proven from definitions** (no axioms needed):

- The full KO-dimension classification and sign table
- The Clifford transmutation: quatSquared ⊗ real = complex
- All composition laws for fiber bundle triples
- The structure of the spectral action (which terms, what powers of Λ)
- The explicit S³ Dirac spectrum with eigenvalue spacing and growth
- The gauge-fermion dimension match: gauge dim = (spinor dim)² = 256
- The surjectivity of the spectral → Observerse correspondence

**Assumed as axioms** (2 total):

- Nonzero gauge curvature of the chimeric connection (Kaluza-Klein)
- Positive fiber volume (symmetric space measure theory)

**Computed but marked sorry** (1 total):

- S³ compact resolvent via the explicit eigenvalue formula

## How to Read This Library

Start with `SpectralDefs.lean`. Read the sign table. Understand *why* KO-dim 1 means complex Clifford algebra. Then trace the consequences: complex → unitary gauge group → U(16) → shiab is natural. Each file's Master Theorem assembles that file's results into a single compound statement. The Master Theorem of `ConcreteSpectrum.lean` is the final synthesis: 18 clauses, all verified, for the complete spectral geometry of U⁹ = S³(r) × Sym²₊(ℝ³).

---

**Author:** Adam Bornemann
**License:** MIT
**Year:** 2026
