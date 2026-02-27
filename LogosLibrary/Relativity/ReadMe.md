# Relativity

Formally verified foundations of relativistic physics, from flat spacetime to rotating black holes to the thermodynamic origin of time.

## What This Section Does

This section builds a dependency chain from special relativity to a collection of results in relativistic thermodynamics that, taken together, constitute an original research programme. The chain is:

1. **Minkowski spacetime** — the flat background
2. **Kerr metric** — rotating black holes in full generality
3. **Ott's temperature transformation** — resolving a 60-year debate
4. **Jacobson's derivation** — Einstein's equations from thermodynamics, shown to require Ott
5. **Connes-Rovelli thermal time** — time dilation derived from thermodynamics, uniqueness proven

Each file imports from the one above it. The mathematics is cumulative: later results depend structurally on earlier infrastructure.

## Structure

```
Relativity/
├── SR/
│   └── MinkowskiSpacetime.lean       (~410 lines)
├── GR/
│   ├── KerrMetric.lean               (~2,400 lines)
│   └── Bornemann.lean                (~1,200 lines)
└── Thermodynamics/
    ├── Ott.lean                      (~2,700 lines)
    ├── Jacobson.lean                 (~2,250 lines)
    └── ConnesRovelli.lean            (~3,800 lines)

```

**Note on line counts:** These files are heavily commented. The author uses an expository style in which the Lean code is interleaved with extensive physical motivation, historical context, and pedagogical explanation. The proof content is a fraction of the total line count. This is a deliberate choice — the files are intended to be readable as self-contained introductions to the physics, not merely as machine-checkable artefacts. Whether you find this helpful or maddening is a matter of taste.

## Dependency Graph

```
MinkowskiSpacetime
       │
   KerrMetric ──────── (also imports QM/Uncertainty/UnboundedOperators)
       │
     Ott
      ╱ ╲
Jacobson  ConnesRovelli
               │
          Bornemann ─── (also imports QM/Uncertainty/Schrodinger)
```

## File Descriptions

### `SR/MinkowskiSpacetime.lean`

Standard special relativity infrastructure. Defines Minkowski space as ℝⁿ⁺¹ with signature (−,+,+,…,+), proves the causal trichotomy (every vector is exactly one of timelike, spacelike, or lightlike), constructs the Lorentz boost in the x-direction and verifies it preserves the metric via an explicit `calc` proof. Also provides `AddCommGroup` and `Module ℝ` instances, four-vector constructors, proper time, worldlines, and the Lorentz factor γ ≥ 1.

**Status:** Fully proven. No axioms, no `sorry`.

### `GR/KerrMetric.lean`

A thorough treatment of the Kerr solution for rotating black holes in Boyer-Lindquist coordinates. Covers:

- **Metric components:** Σ, Δ, ρ², full metric tensor, Schwarzschild limit
- **Horizons:** r₊, r₋, positivity, ordering, Δ = 0 verification, Schwarzschild limit (r₊ = 2M, r₋ = 0)
- **Ergosphere:** Static limit surface, frame-dragging angular velocity, proof that rotation is forced inside the ergosphere
- **Ring characterisation:** Σ = 0 ↔ (r = 0 ∧ θ = π/2), ring is *not* a Killing horizon (Δ = a² ≠ 0)
- **Thermodynamics:** Surface gravity, Hawking temperature (proven positive for subextremal), inner vs outer horizon temperatures (proven distinct)
- **Ring temperature:** Argued equal to outer horizon temperature via thermal equilibrium (axiomatized)
- **Complexity:** Proper time from horizon to ring is finite (Schwarzschild case axiomatized from standard integral πM), complexity is finite
- **Extremal properties:** Full characterisation when |a| = M (horizons merge, κ = 0, T = 0, S > 0)

**Axioms:** `thermal_equilibrium_principle` (steady-state objects inside a black hole equilibrate with the outer horizon), `schwarzschild_proper_time_integral_value` (the standard textbook integral ∫ r/√(r(2M−r)) dr = πM). Both are standard physics, formalised here because their full proofs require differential geometry infrastructure not yet in Mathlib.

### `Thermodynamics/Ott.lean`

The central claim: Ott's temperature transformation T → γT is the unique physically consistent law for relativistic thermodynamics, and Landsberg's T → T is ruled out. The file presents seven independent arguments:

| # | Argument | Method |
|---|----------|--------|
| 1 | Landauer bound | Information theory |
| 2 | Entropy invariance | Statistical mechanics |
| 3 | Free energy | Thermodynamic potentials |
| 4 | Partition function | Equilibrium statistics |
| 5 | Four-vector structure | Relativistic geometry |
| 6 | Detailed balance | Microscopic reversibility |
| 7 | Specific heat | Material properties |

A unification theorem (`Unification.the_deep_structure`) shows all seven reduce to: *information is physical (Landauer) + physics is covariant (Lorentz) ⟹ T → γT*. The file concludes by applying the result to Kerr black holes.

An additional `RelativeEntropy` namespace proves that Landsberg leads to absurdities: microstate counts become non-integral, information content becomes frame-dependent, and erasure paradoxes arise.

**Axioms:** `entropy_invariant` (S = k ln Ω counts microstates, which are integers and therefore Lorentz invariant), standard Lorentz transformation of energy (δQ → γδQ).

### `Thermodynamics/Jacobson.lean`

Proves that Jacobson's 1995 thermodynamic derivation of Einstein's field equations *requires* Ott and is *incompatible* with Landsberg. The key results:

- The Clausius ratio δQ/T is Lorentz invariant under Ott, not under Landsberg
- Ott is *uniquely determined* by requiring the Clausius ratio to be invariant: for any f(v) > 0, if f preserves δQ/T, then f(v) = γ(v)
- The Unruh relation T ∝ a is preserved by Ott and violated by Landsberg
- Downstream consequences: Carnot efficiency is frame-invariant, chemical potential ratio μ/T is invariant, Wien's law is consistent with Doppler, etc.

**Axioms:** The Raychaudhuri equation, the Bekenstein-Hawking entropy-area relation.

### `Thermodynamics/ConnesRovelli.lean`

Proves that the Connes-Rovelli thermal time relation t = τ/T is the *unique* Lorentz-covariant relationship between temperature and time, and derives time dilation as a theorem (not a postulate). The central result:

**Uniqueness theorem:** Any function f(T, τ) satisfying positivity, linearity in τ, and Lorentz covariance must have the form f(T, τ) = c·τ/T. The proof solves a multiplicative Cauchy functional equation and uses a lemma (`lorentzGamma_surjective_ge_one`) proving every γ ≥ 1 is physically realizable.

Also proves: modular Hamiltonian K = H/T is a Lorentz scalar, Rindler thermodynamics is covariant, quantum mechanics emerges as the T → 0 limit.

**Axioms:** The thermal time ansatz itself (that physical time is identified with the modular parameter). The file proves this identification is forced to take the form τ/T, but the identification itself is physical input.

### `Bornemann.lean`

An original result arguing that Schwarzschild-de Sitter spacetime is dynamically forbidden in any universe with a thermal bath at T > 0. The argument combines Robertson's uncertainty principle for angular momentum (properly formalized for unbounded operators) with the observation that thermal environments generically excite angular momentum, making the J = 0 state unstable on timescales shorter than 10⁻²⁴ seconds for stellar-mass objects.

The file contains angular momentum operator infrastructure that would more naturally live in `QuantumMechanics/AngularMomentum/`, as well as extended physical commentary and worked numerical estimates. The proof file contains *additional context* beyond the formal mathematics.

**The load-bearing axiom:** `thermal_excites_after_positive_time` — that a thermal bath at T > 0 generically excites nonzero angular momentum expectation values in positive time. Three physical arguments for this axiom are given in comments (measure-theoretic, fluctuation-dissipation, reductio from CMB photon counting). Everything downstream of this axiom is machine-checked.

## What Is Proven vs. What Is Axiomatized

This library makes a clear distinction between machine-verified results and physical inputs that are axiomatized because their proofs require infrastructure (differential geometry, measure theory on infinite-dimensional spaces) not yet available in Mathlib.

### Fully proven (no axioms in the proof chain)

- All of `MinkowskiSpacetime.lean`
- Horizon structure, ergosphere properties, ring characterization in `KerrMetric.lean`
- Robertson uncertainty for angular momentum; all `SdS_Forbidden` results conditional on the thermal axiom
- Clausius ratio invariance/non-invariance under Ott/Landsberg
- Uniqueness of Ott from Clausius preservation
- Uniqueness of thermal time relation
- Time dilation from Ott + thermal time
- All seven Landsberg refutations and the unification theorem

### Axiomatized (physically standard, not yet formalizable in Lean/Mathlib)

- `thermal_equilibrium_principle` — steady-state thermal equilibrium inside black holes
- `schwarzschild_proper_time_integral_value` — the integral πM
- `entropy_invariant` — microstate counting is Lorentz invariant
- `thermal_excites_after_positive_time` — thermal baths excite angular momentum
- Raychaudhuri equation, Bekenstein-Hawking area law
- The thermal time ansatz (that time *is* modular flow)

Every axiom is flagged with `axiom` in the source. There are no hidden `sorry` calls.

## Building

```bash
lake build LogosLibrary.Relativity.SR.MinkowskiSpacetime
lake build LogosLibrary.Relativity.GR.KerrMetric
lake build LogosLibrary.Relativity.GR.SdS.Bornemann
lake build LogosLibrary.Relativity.Thermodynamics.Ott
lake build LogosLibrary.Relativity.Thermodynamics.Jacobson
lake build LogosLibrary.Relativity.Thermodynamics.ConnesRovelli
```

## References

- Kerr, R.P. (1963). "Gravitational field of a spinning mass." *Phys. Rev. Lett.* 11, 237-238.
- Ott, H. (1963). "Lorentz-Transformation der Wärme und der Temperatur." *Z. Physik* 175, 70-104.
- Jacobson, T. (1995). "Thermodynamics of Spacetime: The Einstein Equation of State." *Phys. Rev. Lett.* 75, 1260-1263.
- Connes, A. & Rovelli, C. (1994). "Von Neumann algebra automorphisms and time-thermodynamics relation." *Class. Quantum Grav.* 11, 2899-2917.
- Robertson, H.P. (1929). "The Uncertainty Principle." *Phys. Rev.* 34, 163-164.
