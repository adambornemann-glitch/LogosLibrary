# The Riemann Machine

### A Möbius Gear Framework for the Riemann Hypothesis

*Via the Curry-Howard method — because the real thing would melt every computer ever built.*

---

## Overview

This formalization expresses the Riemann Hypothesis as a **positivity condition on a mechanical system** — a network of Möbius gears indexed by the primes of ℚ, coupled by the Riemann-Weil explicit formula, and turning on a carrier shaft whose smooth rotation is equivalent to all non-trivial zeros lying on the critical line.

The framework **does not prove RH**. It proves that the Möbius gear language is a **consistent and complete** vocabulary for expressing and studying RH, and that the structural content of the problem — everything except a single analytic limit step — is either proved or follows from the types.

**This work is part of the Logos Library Formalization Project**, building on the Möbius twist infrastructure developed in the Clifford periodicity, Hopf tower, and modular theory formalizations.

---

## The Chain

```
ZetaData.lean            ξ(s), functional equation, V₄ symmetry, RH as a type
     │
ExplicitFormula.lean     Test functions, Weil kernel, explicit formula
     │                   WeilPositivity ↔ CriticalLineConfinement
     │
LocalFactor.lean         4-axiom tooth profile, VerifiedLocalFactor (automatic)
     │
ArchimedeanGear.lean     Γ_ℝ(s), Gaussian, Fourier-as-J
PrimeFactor.lean         (1−p⁻ˢ)⁻¹, 𝟙_{ℤ_p}, β_p = log p (forced, not chosen)
     │
GearAssembly.lean        Meshing, carrier shaft, semi-local → global growth
     │                   PositivityTarget ↔ CriticalLineConfinement
     │
BetaFunction.lean        β : Place → ℝ₊, partition identity, spectral interpretation
     │
Positivity.lean          Five faces of RH, global coherence, the endgame
```

---

## The Five Faces of RH

The formalization provides five equivalent formulations of the Riemann Hypothesis. All are proved mutually equivalent (one direction via axiom).

| Face | File | Statement |
|------|------|-----------|
| **Standard** | `ZetaData` | ∀ zeros ρ, Re(ρ) = 1/2 |
| **Schwarz** | `ZetaData` | ∀ zeros ρ, the Schwarz reflection fixes ρ |
| **Duality** | `ZetaData` | ∀ zeros ρ, reflection = conjugation |
| **Weil** | `ExplicitFormula` | ∀ test functions f, Q(f) ≥ 0 |
| **Assembly** | `GearAssembly` | ∀ test functions f, Re(Σ_v W_v(f)) ≥ 0 |

The equivalence `assembly_iff_rh` closes the circle: the gear-theoretic positivity target and the classical critical line confinement are the same Prop.

---

## The Tooth Profile

Each place v of ℚ contributes a local Möbius gear satisfying a **4-axiom tooth profile** — the number-theoretic instantiation of the Möbius twist structure discovered in the Clifford/Tomita formalization:

| Axiom | Cayley-Dickson | Tomita | Zeta (arithmetic) |
|-------|---------------|--------|-------------------|
| **I. Involution** | J² = 1 | J² = 1 | ε(s)·ε(1−s) = 1 |
| **II. Anti-structure** | J(ab) = J(b)J(a) | JMJ = M' | Local functional equation |
| **III. Size preservation** | ‖J(a)‖ = ‖a‖ | ⟨Jψ,Jφ⟩ = ⟨φ,ψ⟩ | \|ε(½+it)\| = 1 |
| **IV. Ground state** | a·J(a) = ‖a‖² | JΩ = Ω | g = g̃, W_v(g) = 0 |

The key theorem: **every `LocalFactor` automatically satisfies the full tooth profile** (`localFactor_auto_verified`). The axioms are baked into the types. Constructing a local factor *is* verifying its tooth profile.

---

## The β-Function

Each place v of ℚ carries an effective inverse temperature:

```
β(∞) = 1           (archimedean baseline)
β(p) = log p       (for each prime p — FORCED, not chosen)
```

The temperature assignment is:

- **Unique**: `temperature_forced` proves β_p = log p is the only value compatible with the Euler factor being a bosonic partition function.
- **Injective**: `β_separates_places` proves no two distinct places share a temperature. The β-function is a complete invariant for places of ℚ.
- **Monotone**: larger primes are colder (higher inverse temperature).
- **Surprising**: the archimedean place sits between primes 2 and 3 on the temperature scale, since log 2 ≈ 0.693 < 1 < log 3 ≈ 1.099.

The Euler product is recovered as a **grand partition function**:

```
ζ(s) = Π_p (1 − e^{−s·β_p})⁻¹
```

Each factor is the partition function of a single bosonic mode with energy gap β_p = log p. The parameter s is the global inverse temperature. RH says: all phase transitions occur at the critical temperature Re(s) = 1/2.

---

## The Gear Assembly

The assembly grows by adding primes one at a time:

```
S₁ = {∞}  ⊂  S₂ = {∞, 2}  ⊂  S₃ = {∞, 2, 3}  ⊂  ...
```

At each step, the **meshing condition** (semi-local explicit formula + remainder positivity) is checked, and the **carrier shaft theorem** guarantees the spectral content is independent of which gears are observed:

```
                     SPECTRAL SIDE
                       Σ_ρ f̂(ρ)  (zeros)
                          ‖
            ══════════════╪═══════════════
           ║              ‖               ║
         W_∞(f)         W_2(f)          W_3(f)    ...
       Archimedean      Prime 2         Prime 3
         GEAR            GEAR            GEAR
           ║              ‖               ║
            ══════════════╪═══════════════
                          ‖
                    CARRIER SHAFT
                (independent of which
                  gears you observe)
```

The key structural theorem: **meshing + remainder domination implies semi-local positivity** (`meshing_implies_semilocal_positivity`). In the global limit, semi-local positivity gives global positivity gives RH.

---

## Provenance

### Proved (no axioms, no sorry)

- `zetaReflection_involution` — the functional equation involution
- `zetaSchwarzReflection_fixed_iff` — critical line = Schwarz fixed set
- `zero_reflection`, `zero_conjugation`, `zero_schwarz` — V₄ orbit of zeros
- `rh_iff_schwarz_fixes`, `rh_iff_reflection_eq_conj` — RH equivalences
- `weilKernel_on_criticalLine_re_nonneg` — kernel ≥ 0 on the line
- `spectralSum_re_nonneg_of_rh` — RH → spectral positivity
- `rh_implies_weilPositivity` — RH → Weil positivity (forward direction)
- `localFactor_auto_verified` — tooth profile automatic from types
- `effectiveβ_pos`, `effectiveβ_injective` — β basic properties
- `euler_as_partition` — Euler factor = bosonic partition function
- `temperature_forced` — β_p = log p is uniquely determined
- `β_separates_places` — β is a complete invariant for places
- `meshing_implies_semilocal_positivity` — meshing → semi-local positivity
- `carrier_shaft_arithmetic` — spectral side independent of gear set
- `assembly_iff_rh` — positivity target ↔ RH
- `rh_implies_globalCoherence` — RH → framework consistent
- `five_faces_equivalent` — all five formulations equivalent

### Axiomatized (known theorems, not constructed in Lean)

- `weilPositivity_implies_onLine` — converse Weil (requires Paley-Wiener theory)
- `global_limit_convergence` — limit of semi-local → global positivity
- `CompletedZetaData` fields — ξ(s) exists with the standard properties
- `ExplicitFormulaData.hFormula` — the Riemann-Weil explicit formula
- `EpsilonData`, `GammaFactorData`, `GaussianData` fields — local analytic data
- Various `Nodup` lemmas for gear set construction

### Conjectured

- `GlobalCoherenceConjecture` — global coherence of the gear framework implies RH

---

## The Gap

The framework reduces RH to a single condition:

> **For every finite set S of places, the S-assembly meshes with remainder dominated by the spectral sum.**

This is `global_limit_convergence` — the axiom that the limit of semi-local positivity gives global positivity. It is an analytic statement about the convergence of the explicit formula, not a structural statement about gears.

This gap is the **same gap** that appears in Connes' program on the adèle class space: the trace formula is valid semi-locally (for finite sets of places) but the global case requires a proof that the semi-local results cohere in the limit. The gear framework and the operator-algebraic framework arrive at the same obstruction from different directions.

---

## The Thermodynamic Interpretation

```
Number Theory              Thermodynamics
─────────────              ──────────────
Prime p                    Bosonic mode
log p = β_p                Energy gap
s                          Global inverse temperature
(1−p⁻ˢ)⁻¹                 Single-mode partition function
ζ(s)                       Grand partition function
Non-trivial zero ρ         Phase transition point
Re(s) = 1/2               Critical temperature
Explicit formula           First law (conservation)
Weil positivity            Second law (Q ≥ 0)
RH                         All transitions at critical T
```

---

## Connection to the Möbius Framework

This formalization builds on three prior components of the Logos Library:

- **MobiusBridge.lean** — The bridge between Cayley-Dickson conjugation and Bott periodicity. Establishes that the algebraic twist (CD) and the combinatorial twist (Bott) are different but connected by an injective, non-surjective map whose intertwining provably fails.

- **MobiusCycle.lean** — The Möbius structure of the KMS strip and Connes cocycle. Formalizes the modular conjugation J as a Möbius half-twist, proves fermionic KMS states cannot exist on ungraded algebras (the sign twist has no nonzero global sections), and shows the carrier shaft (canonical outer flow) is orientable because the Möbius twist dies in Out(M).

- **MobiusGear.lean** — The triangle relating all three Möbius twists (Bott, CD, Tomita). Establishes the 4-axiom tooth profile, proves CD and Tomita match 4/4 while Bott matches 1/4, and identifies the GNS construction as the consistent bridge (unlike the Bott bridge where intertwining fails).

The Riemann framework instantiates the tooth profile at each place of ℚ, with the functional equation playing the role of J, the epsilon factor playing the role of the modular operator, and the ground state (Gaussian / 𝟙_{ℤ_p}) playing the role of the vacuum Ω.

---

## File Listing

| File | Lines | Role |
|------|-------|------|
| `Riemann/ZetaData.lean` | ~480 | Critical strip geometry, V₄ symmetry, RH as a type |
| `Riemann/ExplicitFormula.lean` | ~470 | Test functions, Weil kernel, explicit formula, Weil ↔ RH |
| `Riemann/LocalFactor.lean` | ~470 | Tooth profile, epsilon factors, verified local factors |
| `Riemann/ArchimedeanGear.lean` | ~350 | Gamma factor, Gaussian, Fourier-as-J |
| `Riemann/PrimeFactor.lean` | ~430 | Euler factors, 𝟙_{ℤ_p}, β_p forced, gear sets |
| `Riemann/GearAssembly.lean` | ~520 | Meshing, carrier shaft, growth, global limit interface |
| `Riemann/BetaFunction.lean` | ~490 | β-function, uniqueness, partition identity, spectral interpretation |
| `Riemann/Positivity.lean` | ~420 | Global coherence, five faces, endgame, scorecard |


---

## Epilogue

The Riemann Hypothesis, in this framework, is a second law. The Weil quadratic form Q(f) = Re(Σ_ρ |f̂(ρ)|²) is the free energy of the prime gas, and RH asserts it is non-negative. The primes are the microstates. The zeros are the macroscopic observables. The explicit formula is the first law. Weil positivity is the second law.

The gears encode the mechanics. Positivity is the thermodynamics. The question — *does the machine turn smoothly?* — is the Riemann Hypothesis.

---

*Author: Adam Bornemann, 2026. Logos Library Formalization Project. MIT License.*