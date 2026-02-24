# Superior Nanothermodynamics

A Lean 4 formalization proving that nanothermodynamics is restricted modular flow.

## The Claim

Thirty years of nanothermodynamics research — Hill's subdivision potential, the Hamiltonian of mean force, anomalous heat capacities in nanoclusters, non-extensive entropy — were computing restricted modular flow in the sense of Connes–Rovelli thermal time, without knowing it.

This library makes the identification precise and proves it Lorentz-covariant.

## What's Formalized

### Definition.lean (~950 lines, 0 sorry)

The core framework.

**Structures:**
- `AlgebraicCut`: von Neumann entropies (S_A, S_B, S_AB) with subadditivity and Araki–Lieb
- `PureCut`: maximal entanglement (S_AB = 0)
- `ProductCut`: zero correlations (S_AB = S_A + S_B)
- `NanoSystem`: subsystem with bare/effective Hamiltonians, temperature, particle count

**Key results:**
- Mutual information I(A:B) = S_A + S_B − S_AB is non-negative (from subadditivity)
- For pure states: S_A = S_B and I(A:B) = 2·S_A (from Araki–Lieb)
- Subdivision potential ε = T·I/N transforms as energy under Lorentz boosts (Ott covariance)
- Modular Hamiltonian K = H*/T is Lorentz invariant (proof: one-step γ cancellation)
- Boltzmann factor exp(−βE) is Lorentz invariant
- Thermal state exp(−K) is Lorentz invariant
- Master theorem: K invariant ∧ ε covariant ∧ thermal time dilates — simultaneously

**Translation dictionary (formal):**
- "Trace out environment" = restrict to subalgebra
- "Weak coupling" = zero mutual information
- "Non-extensivity" = mutual information
- "Hill's subdivision potential" = entropic cost of the algebraic cut

### Limits.lean

Classical thermodynamics as a theorem.

- N·ε = T·I (total cost is property of the cut, not the particles)
- ε → 0 as N → ∞ (thermodynamic limit)
- ε ≤ 2T·S_A/N (O(1/N) convergence rate)
- H_bare ≤ H* ≤ H_bare + 2T·S_A/N (sandwich theorem, collapses as N → ∞)
- H*(N) → H_bare and K(N) → H_bare/T (classical Hamiltonian recovered)
- Weak coupling biconditional: H* = H_bare ↔ I = 0 (sharp boundary, not crossover)

### Monotonicity.lean

Ordering theorems and the data processing inequality.

- ε is monotone increasing in I (more correlation → bigger cost)
- ε is monotone increasing in T (hotter → bigger cost)
- ε is monotone decreasing in N (more particles → smaller per-particle cost)
- Coarse-graining decreases ε and moves H* closer to H_bare (DPI)
- Joint bound: the complete 3D parameter space in one `calc` block

### PageCurve.lean (~620 lines, 0 sorry)

The Page curve is a subdivision potential.

- `PageEntropy` axiomatizes the Page curve's essential properties
- `pageCut` constructs a `PureCut` — inherits all pure-state theorems automatically
- ε(0) = 0 and ε(1) = 0 (information conservation)
- Maximum at Page time f = 1/2
- Strictly increasing before, strictly decreasing after
- Ott-covariant at every point (one-liner: calls existing infrastructure)
- Decoding Hawking radiation costs ≥ S_max/π measurements, time ≥ 2·S_max/T
- **Universality theorem**: all properties in one conjunction, valid for nanoclusters and black holes alike

## Architecture

```
NanoThermo.lean              ← root import
├── NanoThermo/
│   ├── Definition.lean      ← core framework + covariance
│   ├── Limits.lean          ← thermodynamic limit + biconditionals
│   ├── Monotonicity.lean    ← ordering + data processing inequality
│   └── PageCurve.lean       ← black hole connection + universality
```

Built on:
- `LogosLibrary.Relativity.LorentzBoost.TTime` (thermal time formalization)
- Mathlib (real analysis, special functions, filters)

## The Physical Picture

| Parameter | Nanocluster | Black Hole |
|-----------|-------------|------------|
| N | ~100 atoms | ~10⁷⁷ Planck areas |
| T | ~300 K | ~10⁻⁷ K |
| ε | ~T/100 (measurable) | ~T·S_BH/N |
| I(A:B) | molecular correlations | Page curve |
| K = H*/T | molecular modular Hamiltonian | area operator / T_Hawking |

Same Lean type. Same theorems. Different parameter values.

## Proof Highlights

**Most satisfying proof:** `nano_modular_hamiltonian_invariant` — the Lorentz invariance of the modular Hamiltonian reduces to `mul_div_mul_left` (γ cancels in one step).

**Most powerful proof:** `universality` — four properties of the Page curve in one conjunction, proved by invoking theorems that were originally written for nanoclusters.

**Most physically meaningful proof:** `hmf_approaches_bare` — classical thermodynamics emerges as N → ∞, not as an approximation but as a `Filter.Tendsto` limit.

**Shortest proof with the deepest consequence:** `page_curve_covariant` — one line. The Ott covariance of evaporating black holes was already proved when we did the nanocluster framework.

## Zero Sorry

Every file compiles with zero `sorry` statements. All proofs are complete.

The DPI is axiomatized (via the `CoarseGraining` structure) because the full proof requires Haar measure integration not yet in Mathlib. Everything downstream of the axiom is proved.

## Citation

If you use this formalization, please cite:

```
Bornemann, A. (2026). Superior Nanothermodynamics: A Lean 4 Formalization.
```

## License

MIT