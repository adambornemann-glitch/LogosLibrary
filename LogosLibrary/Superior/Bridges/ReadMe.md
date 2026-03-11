# Bridges

**Lateral connections between the clusters of the Superior framework.**

---

## What This Section Is

The main clusters of the framework — CommonResources, KnotTheory,
HotGravity, SpectralTriples, SplitMechanics — are built as vertical
towers: each file imports the previous and extends it upward, always
within one cluster.

The **Bridges** section is different. These files connect *across*
clusters, proving that structures built independently in separate towers
are in fact the same mathematical object.

A bridge does not extend a tower. It ties two towers together.

Connections that are *internal* to a cluster live inside that cluster:

- The Hopf Knots (Strings ↔ YangMills) live in `KnotTheory/Knots/`
- The Spectral Bridge (Triples ↔ GeometricUnity) lives in
  `SpectralTriples/SpectralBridge.lean`

What remains here are the genuinely *lateral* connections — bridges
between clusters with no shared ancestor besides CommonResources.

---

## The Bridges

### CProcess — HotGravity ↔ HotGravity (`CProcess.lean`)

Chemical decoherence and nanothermodynamic subdivision are the same
phenomenon. Connects Objective Reduction (the 2π decoherence threshold)
with Nanothermodynamics (the subdivision potential ε = T · I(A:B) / N).

**The bridge equation:** At decoherence, mutual information reaches one
modular period: I(A:B) = 2π. Therefore ε = 2πT/N.

**Marcus monotonicity is NanoThermo monotonicity:** Larger reorganisation
energy λ → faster entropy production Γ → faster MI growth → larger
subdivision potential at any time t. This is `subdivision_monotone_in_MI`
applied to chemistry.

**The correlated bath is the DPI:** Correlated bath modes provide a
coarser description of the electronic state. Mutual information grows
slower. Photosynthetic coherence persists not by magic but by the data
processing inequality.

(~15 theorems, 0 sorry, 0 axioms)

---

### Gravity Bridges — HotGravity internal (`Gravity/`)

Pairwise and triangular compatibility proofs for Loop Quantum Gravity,
Entropic Gravity, and Shape Dynamics.

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

| Bridge | File | Connects | Core result | Theorems |
|--------|------|----------|-------------|:--------:|
| A | `LQGtoEQ.lean` | LQG ↔ EG | Jacobson ingredients identical; area spectrum = entropy | 14 |
| B | `EGtoSD.lean` | EG ↔ SD | Force = volume creation rate: F = dV/dx | 10 |
| C | `LQGtoSD.lean` | LQG ↔ SD | UV completes IR; area gap = minimum entropy quantum | 12 |
| D | `Synthesis.lean` | All three | Shared modular period; complete postulate audit | 12 |
| | | | **Gravity total** | **48** |

See the [Gravity Bridges README](Gravity/README.md) for full details
including the postulate audit, contact surface, and dependency diagram.

---

## Statistics

| File | Theorems | `sorry` | Axioms |
|------|:--------:|:-------:|:------:|
| CProcess.lean | ~15 | 0 | 0 |
| Gravity/ (4 files) | 48 | 0 | 0 |
| **Bridges total** | **~63** | **0** | **0** |

---

## Dependencies

No bridge imports another bridge. Each imports only the
synthesis/endpoint files of the towers it connects.

```
CProcess.lean           ← HotGravity/NanoThermo
                          + HotGravity/ObjectiveReduction/EProcess

Gravity/LQGtoEQ.lean    ← HotGravity/LQG/EPRLVertex
                          + HotGravity/EntropicGravity
Gravity/EGtoSD.lean     ← HotGravity/EntropicGravity
                          + HotGravity/ShapeDynamics/Synthesis
Gravity/LQGtoSD.lean    ← HotGravity/LQG/EPRLVertex
                          + HotGravity/ShapeDynamics/Synthesis
Gravity/Synthesis.lean  ← HotGravity/LQG/EPRLVertex
                          + HotGravity/EntropicGravity
                          + HotGravity/ShapeDynamics/Synthesis
```

---

## Design Principles

1. **Bridges introduce no axioms.** They consume what the towers provide.
   If a bridge required new assumptions, it would indicate the towers are
   not describing the same structure.

2. **Bridges prove identification, not extension.** A bridge theorem says
   "X from tower A *is* Y from tower B," not "X implies new result Z."
   The new content is the identification itself.

3. **Intra-cluster wiring lives in the cluster.** The Hopf Knots belong
   to KnotTheory. The Spectral Bridge belongs to SpectralTriples. Only
   genuinely lateral connections — between clusters with no shared
   ancestor besides CommonResources — live here.

---

## File Structure

```
Bridges/
├── README.md              This file
├── CProcess.lean          Objective Reduction ↔ Nanothermodynamics
└── Gravity/
    ├── README.md          Gravity bridges detail
    ├── LQGtoEQ.lean       LQG ↔ Entropic Gravity
    ├── EGtoSD.lean        Entropic Gravity ↔ Shape Dynamics
    ├── LQGtoSD.lean       LQG ↔ Shape Dynamics
    └── Synthesis.lean     Triangular synthesis (all three)
```

---

## What Is and Isn't Claimed

**What the bridges prove:** Algebraic and structural compatibility across
independently constructed formalisations. Shared constants and structures
are the same mathematical objects. Cross-tower identifications are
compiler-verified equalities.

**What the bridges do not prove:** That any pair of connected towers
describes the same physical theory. That any tower correctly describes
nature. The bridges connect formal structures, not physical theories.

---

## License

MIT. See [LICENSE](../../LICENSE).