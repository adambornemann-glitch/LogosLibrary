# CommonResources — Shared Mathematical Infrastructure

**The foundation layer of the Superior Method.**

Everything in this directory is used by two or more clusters. If a
definition, a structure, or a theorem appears in only one cluster, it
does not belong here. CommonResources earns its keep by being
genuinely shared.

---

## What Lives Here

| Subdirectory / File | What it provides | Used by |
|---------------------|------------------|---------|
| [`DivisionAlgebra/`](DivisionAlgebra/README.md) | Hurwitz classification, gauge correspondence, Hopf data | KnotTheory, SpectralTriples, HotGravity, SuperCausets |
| [`HopfTower/`](HopfTower/README.md) | Hopf fibrations, tower nesting, S¹ persistence, Adams' theorem, Cayley-Dickson octonions, Clifford periodicity | KnotTheory, SpectralTriples, SuperCausets |
| [`Time/ThermalTime/`](Time/ThermalTime/README.md) | Connes–Rovelli thermal time, Ott transformation, measurement threshold | All clusters |
| [`Time/SuperCausets/`](Time/SuperCausets/README.md) | Second Law → causal order → ℍ → D=3 → U⁹ → SM → Λ (161 theorems, 2 sorry) | HotGravity, SpectralTriples, Bridges |
| `ModularFlow.lean` | 2π quantization, threshold dichotomy, thermal period, Ott covariance | HotGravity, SplitMechanics, KnotTheory |
| `Quintet.lean` | E = I · k_B · T · ln 2, Landauer energy, information invariance | HotGravity, Bridges |
| `CliffordPeriodicity.lean` | Bott periodicity, Cl(9) ≅ M₁₆(ℂ), spinor fibre, shiab degrees | SpectralTriples |

---

## The Time/ Subdirectory

Time provides the two temporal foundations of the framework: how
physical time emerges from thermal states, and how causal structure
emerges from the Second Law.

### Time/ThermalTime/

The Connes–Rovelli thermal time hypothesis, fully formalised. Physical
time is the modular flow rescaled by temperature: t = τ/T. The Ott
transformation T → γT is proved uniquely correct through seven
independent arguments (Landauer bound, entropy invariance, free energy,
partition function, 4-vector structure, detailed balance, specific
heat). Time dilation is derived as a theorem of thermodynamics.
Measurements require ΔS ≥ 2π nats of entropy production. The
classical limit is resolved by recognising the modular parameter τ
(not T) as the fundamental Lorentz invariant.

See the [ThermalTime README](Time/ThermalTime/README.md) for full
details.

**Stats:** ~50 theorems, 0 sorry, 1 axiom (`entropy_invariant`).

### Time/SuperCausets/

The most substantial single module in CommonResources. Standard causal
set theory (Bombelli–Lee–Meyer–Sorkin) takes the partial order as
primitive. SuperCausets inverts this: the Second Law is ontologically
prior. If entropy is strictly monotone along the causal relation
(x ≺ y ⟹ S(x) < S(y)), then irreflexivity and asymmetry are
*theorems*, not axioms.

From this starting point, the module builds a six-layer deductive
chain:

1. **Foundation** — Postulate Zero gives a strict partial order
2. **Tick** — one birth event = one modular cycle = 2π nats
3. **Thermal** — Ott covariance makes the growth process observer-independent
4. **Algebraic** — three physical requirements (normed division algebra,
   one thermal circle, nontrivial spatial structure) force ℍ uniquely,
   giving D_spatial = 3 via the Hopf base S²
5. **Spectral** — D = 3 yields the total space U⁹, then Cl(9) ≅ M₁₆(ℂ)
   and the Standard Model gauge group
6. **Cosmological** — Poisson fluctuations in the element count give
   Λ = 2π/√N

The two sorry are genuine open problems: the Gibbs inequality (a
Mathlib gap — the proof exists, the formalisation infrastructure does
not) and the hard direction of the causal set Hauptvermutung (open
for ~30 years in standard CST — Sorkin's conjecture, not ours to
close).

See the [SuperCausets README](Time/SuperCausets/README.md) for the
full deductive chain, postulate audit, and file-by-file breakdown.

**Stats:** 161 theorems, 2 sorry, 0 axioms.

---

## The Three Standalone Files

These sit directly in `CommonResources/` rather than in subdirectories
because each is a single self-contained file providing infrastructure
that does not need its own sub-hierarchy.

### ModularFlow.lean

The 2π quantization of the modular automorphism group, extracted from
ThermalTime and made available as a standalone import.

The core facts: the KMS period is 2π, every interaction is either
sub-threshold (ΔS < 2π, coherence preserved) or supra-threshold
(ΔS ≥ 2π, decoherence), and the thermal period contracts under
the Ott transformation. Also provides the thermal-time-to-entropic-time
interpolation and proves that entropy per modular cycle is
temperature-independent (it is always 2π nats — that is the *definition*
of one cycle).

Bundles everything into a `ModularFlowFramework` structure for
downstream consumption.

**Stats:** ~30 theorems, 0 sorry, 0 axioms.

### Quintet.lean

The relation E = I · k_B · T · ln 2 — Landauer's principle read as an
identity connecting energy, information, and temperature.

The key result: information content I = E/(k_B T ln 2) is Lorentz
invariant under Ott (because γ cancels in the E/T ratio) but scales
as γI under Landsberg. This gives a sixth independent argument
for Ott over Landsberg, complementing the seven in ThermalTime.
Also provides gravitational information content I_grav = Gm²/(Δx k_B T ln 2)
with scaling laws in mass, separation, and temperature.

Bundles everything into a `QuintetFramework` structure.

**Stats:** ~25 theorems, 0 sorry, 0 axioms.

### CliffordPeriodicity.lean

The 8-fold periodicity of real Clifford algebras (Bott periodicity),
targeted at the result that matters for SpectralTriples:

**Cl(9,0) ≅ M₁₆(ℂ)**

This is not a choice. It is forced: 9 mod 8 = 1, and position 1 in
the Bott period gives a complex matrix algebra. The file constructs
explicit `CliffordData` records for Cl(0) through Cl(9) (and Cl(14)
for comparison), verifies all dimension consistency checks, and
derives the consequences: ℂ¹⁶ spinor fibre, U(16) structure group,
Hermitian decomposition, shiab operator degrees (Ω² → Ω⁷), and
the Lagrangian structure (all three terms are 9-forms). Also proves
that n = 3 is the unique base manifold dimension producing ℂ¹⁶
spinors via the metric bundle formula dim = n + n(n+1)/2.

**Stats:** ~40 theorems, 0 sorry, 0 axioms.

---

## Dependency Graph

```
CliffordPeriodicity.lean ──────────────────────────────────────┐
                                                               │
ModularFlow.lean ──────────────────────────────────────────┐   │
                                                           │   │
Quintet.lean ──────────────────────────────────────────┐   │   │
                                                       │   │   │
DivisionAlgebra/                                       │   │   │
  Basic.lean ─────────┐                                │   │   │
  Quaternions.lean ────┤                               │   │   │
                       ▼                               │   │   │
HopfTower/             │                               │   │   │
  HopfFibration.lean ──┤ (imports DivisionAlgebra)     │   │   │
  HopfTowerKnot.lean ──┤                               │   │   │
  HopfTowerOctonion.lean ─┤ (imports HopfTowerKnot)    │   │   │
                       │                               │   │   │
Time/                  │                               │   │   │
  ThermalTime/ ────────┤                               │   │   │
  SuperCausets/        │                               │   │   │
    Basic ─────────────┤                               │   │   │
    ThermalCauset ─────┤ (imports ThermalTime)         │   │   │
    QuaternionicEntropy┤ (imports HopfTower)           │   │   │
    Cosmology ─────────┤                               │   │   │
    Synthesis ─────────┘                               │   │   │
                                                       │   │   │
           ┌───────────────────────────────────────────┘   │   │
           │               ┌───────────────────────────────┘   │
           ▼               ▼                                   ▼
    ┌──────────────────────────────────────────────────────────────┐
    │              Downstream clusters import from here            │
    │  KnotTheory  ·  HotGravity  ·  SpectralTriples  ·  etc.    │
    └──────────────────────────────────────────────────────────────┘
```

Within CommonResources, the internal dependency chains are:

- `HopfFibration.lean` imports from `DivisionAlgebra/`
- `HopfTowerOctonion.lean` imports from `HopfTowerKnot.lean`
- SuperCausets imports from ThermalTime, HopfTower, and DivisionAlgebra
  (its internal chain: Basic → ThermalCauset → QuaternionicEntropy →
  Cosmology → Synthesis)

Everything else is independent.

---

## Combined Statistics

| Component | Theorems | sorry | Axioms |
|-----------|:--------:|:-----:|:------:|
| DivisionAlgebra/Basic | ~45 | 0 | 0 |
| DivisionAlgebra/Quaternions | ~35 | 0 | 0 |
| HopfTower/HopfFibration | ~55 | 0 | 5 (Adams) |
| HopfTower/HopfTowerKnot | ~50 | 0 | 0 |
| HopfTower/HopfTowerOctonion | ~50 | 0 | 0 |
| CliffordPeriodicity | ~40 | 0 | 0 |
| ModularFlow | ~30 | 0 | 0 |
| Quintet | ~25 | 0 | 0 |
| ThermalTime (4 files) | ~50 | 0 | 1 |
| SuperCausets | 161 | 2 | 0 |
| **Total** | **~541** | **2** | **6** |

The 5 axioms in HopfFibration encode Adams' theorem (the classification
of Hopf-invariant-one maps). The proof requires stable homotopy theory
and K-theory — deep algebraic topology that Mathlib does not yet cover.
The axioms state: the four Hopf fibrations exist, and Adams' theorem
classifies them. Everything downstream is derived.

The 1 axiom in ThermalTime is `entropy_invariant`: S = Q/T is
Lorentz invariant (entropy counts microstates, which are integers,
which do not Lorentz transform).

The 2 sorry in SuperCausets are genuine open problems: the Gibbs
inequality (`klDivergence_nonneg` — the proof is standard but Mathlib
lacks the formalisation infrastructure) and the hard direction of the
causal set Hauptvermutung (open for ~30 years in standard CST).

---

## Design Principles

**Explicit constants.** Physical constants (G, ℏ, k_B, c) are carried
explicitly. Nothing is silently set to 1. When natural units are used,
they are set to 1 *explicitly* and the general-units version is also
provided.

**Structure fields are not axioms.** When a theorem says "given a
system satisfying these properties," the properties are structure
fields — explicit, named, visible in the type signature. Axioms are
reserved for mathematical facts that Mathlib cannot yet prove
(Adams' theorem, entropy invariance). The distinction matters.

**Self-contained review.** Several files reproduce quaternion
infrastructure locally rather than importing it. This is deliberate:
it means each file can be read and type-checked independently for
review purposes. The full library uses proper imports; the local
copies are for reviewability.

---

## License

MIT. See [LICENSE](../LICENSE).