# Gravity Bridges

**Pairwise and triangular compatibility proofs for LQG, Entropic Gravity,
and Shape Dynamics.**

---

## What This Is

Three towers in the Superior framework address gravity from independent
starting points:

- **Loop Quantum Gravity (LQG)** — Discrete quantum geometry. SU(2)
  irreps, spin networks, spin foams, the EPRL vertex amplitude. Area
  and volume are quantised. The modular period 2π selects a unique
  vertex amplitude.

- **Entropic Gravity (EG)** — Gravity from thermodynamics. S = A/(4G)
  and T = a/(2π) yield F = ma via the Great Cancellation. 224 theorems.
  The Schwarzschild Quartet. Parametric (α, n) universality.

- **Shape Dynamics (SD)** — Thermodynamic geometry. CMC slicing is
  thermal equilibrium, York time is thermodynamic time, Padmanabhan's
  dV = TdS gives volume emergence. QM ↔ classical interpolation
  parameterised by temperature.

Each tower compiles independently. This directory contains four bridge
files that import pairs (or all three) and prove structural compatibility.
The compiler is the referee.

---

## The Bridge Network

Three pairwise bridges plus one triangular synthesis:

```
           LQG
          /   \
    (A)  /     \  (C)
        /       \
      EG ——(B)—— SD
         \     /
          \   /
           (D)
        Triangle
```

**Bridge A — LQG ↔ EG** (`LQGtoEQ.lean`)
The Jacobson–modular bridge. Both towers cite Jacobson (1995). Both
derive the coupling 8πG = (2π)·(4G). Both use the modular period 2π
and KMS at β = 1. The bridge proves the decomposition is the same,
the Jacobson ingredients are the same, and LQG's area spectrum is
what EG's entropy counts. 14 theorems.

**Bridge B — EG ↔ SD** (`EGtoSD.lean`)
The force–volume bridge. EG's entropic force F = T·(dS/dx) is
identified with SD's Padmanabhan volume emergence rate dV = T·dS.
The central result: F = dV/dx — gravitational force is volume
creation rate. Lorentz-invariant under Ott. The parametric family
(α, n) and temperature interpolation are orthogonal and jointly
consistent. 10 theorems.

**Bridge C — LQG ↔ SD** (`LQGtoSD.lean`)
The UV–IR bridge. The most structurally different pair: LQG is
discrete (spin labels, finite-dimensional Hilbert spaces), SD is
continuous (temperature, smooth volume emergence). The bridge
connects them: LQG's boundary dimension is SD's microstate count,
LQG's area gap sets SD's minimum entropy quantum, and both recover
Regge calculus (10 DOF per 4-simplex) in the classical limit.
12 theorems.

**Bridge D — The Triangle** (`Synthesis.lean`)
Triangular results requiring all three towers simultaneously. The
modular period 2π is proven shared by all three. The entropy plays
three compatible roles (boundary dimension, area/4G, microstate
count). All three converge classically. Includes a complete postulate
audit — a transparent inventory of every physical assumption encoded
across all three towers. 12 theorems.

---

## The Contact Surface

The three towers share:

| Structure | LQG | EG | SD |
|-----------|-----|----|----|
| Modular period 2π | KMS automorphism | Unruh denominator | KMS periodicity |
| β = 1 | Modular theory | Boost temperature | Thermal time |
| S = A/(4G) | Microstate counting | Entropy gradient | BH thermodynamics |
| 8πG = (2π)(4G) | Jacobson 3↔3 | Schwarzschild Quartet | First law |
| Regge calculus | Semiclassical limit | Newton's law | Classical SD |

---

## The Central Results

**Force = Volume Creation** (Bridge B)

EG: F = T · dS/dx. SD: dV = T · dS. Therefore F = dV/dx.
Gravitational force is the rate of spacetime volume creation.
Not a metaphor — an algebraic identity between independently
constructed definitions.

**8πG Is Forced** (Bridge A)

The gravitational coupling decomposes as (2π)·(4G). The 2π comes
from quantum field theory (Tomita–Takesaki). The 4G comes from
quantum gravity (Bekenstein–Hawking). LQG and EG each derive a
factor. Neither factor is adjustable.

**UV Completes IR** (Bridge C)

LQG provides the discrete atoms of geometry. SD provides the
thermodynamic framework that assembles them into continuous
spacetime. The modular period 2π is the hinge connecting discrete
and continuous regimes.

**Mutual Consistency** (Bridge D)

All three towers, with their 41 physical postulates, are mutually
consistent. The kernel verifies this. The kernel does not verify
whether any postulate describes nature — that is the job of
experiment.

---

## The Postulate Audit

Bridge D (Synthesis) contains a complete inventory of every physical
assumption across all three towers, classified by type:

| Type | Description | Count |
|------|-------------|:-----:|
| A | Representation theory (SU(2) facts) | 7 |
| B | Combinatorial (4-simplex identities) | 5 |
| C | Physical identifications | 29 |
| D | Conjectures (hypotheses in theorem signatures) | 4* |

*Type D are clearly labelled conjectures, not definitions.

**Total: 41 physical postulates. 0 bridge postulates.**

Independent postulates (removing derivable ones): LQG ~12, EG 2,
SD ~5. Shared postulates (Bekenstein–Hawking, modular period, KMS,
Schwarzschild, Ott) appear in multiple towers and are identified —
not assumed identical — by the bridges.

The distinction: **theorems** are verified by the kernel (no escape).
**Postulates** are encoded as definitions or structure fields (the
kernel checks consistency, not truth).

---

## Statistics

| Bridge | File | Theorems | `sorry` | Axioms |
|--------|------|:--------:|:-------:|:------:|
| A: LQG ↔ EG | `LQGtoEQ.lean` | 14 | 0 | 0 |
| B: EG ↔ SD | `EGtoSD.lean` | 10 | 0 | 0 |
| C: LQG ↔ SD | `LQGtoSD.lean` | 12 | 0 | 0 |
| D: Triangle | `Synthesis.lean` | 12 | 0 | 0 |
| **Total** | | **48** | **0** | **0** |

---

## Dependencies

Each bridge file imports the synthesis/endpoint files of its two (or
three) towers. No bridge imports another bridge. The triangle
(Synthesis) imports all three towers directly.

```
LQGtoEQ.lean    ← LQG/EPRLVertex + EntropicGravity
EGtoSD.lean     ← EntropicGravity + ShapeDynamics/Synthesis
LQGtoSD.lean    ← LQG/EPRLVertex + ShapeDynamics/Synthesis
Synthesis.lean  ← LQG/EPRLVertex + EntropicGravity + ShapeDynamics/Synthesis
```

---

## What Is and Isn't Claimed

**What the bridges prove:** Algebraic and structural compatibility
across three independently constructed formalisations of gravity.
Shared constants (2π, β = 1, 8πG) are the same mathematical objects.
Cross-tower identifications (force = volume rate, area = entropy,
boundary dimension = microstates) are compiler-verified equalities.

**What the bridges do not prove:** That LQG, Entropic Gravity, and
Shape Dynamics are the same theory. That any of them correctly
describes nature. That the classical limits literally coincide (only
that they share structural data). The bridges connect formal
structures, not physical theories.