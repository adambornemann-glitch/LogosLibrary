# P ≠ NP from Information Geometry

A formal development of **P ≠ NP as a thermodynamic impossibility** in [Lean 4](https://lean-lang.org/) with [Mathlib4](https://github.com/leanprover-community/mathlib4).

**Author:** Doctor Professor Baron von Wobble-Bob

## The Thesis in One Sentence

P ≠ NP because a polynomial-time SAT solver would violate the second law of thermodynamics.

## The Argument

Computation is physical (Landauer).  Every computational step has an irreducible thermodynamic cost measured by the **Fisher information metric** — the unique canonical Riemannian metric on probability distributions (Chentsov).  This metric assigns each computation a **thermodynamic length**: the total entropy production along its trajectory through distribution space.

The standard Turing machine formalism is **cost-blind** — it sees transitions but not their thermodynamic cost.  This is why proof barriers exist: relativisation, natural proofs, and algebrisation all operate within the cost-blind framework, which has too much symmetry to distinguish P from NP.

The Fisher metric **breaks this symmetry**.  It is canonical (forced by Chentsov uniqueness), distributional (sees ensemble structure invisible to per-edge costs), and assigns exponential thermodynamic length to computations crossing the **satisfiability phase transition** — the point where the Fisher curvature diverges and the statistical landscape shatters.

### The Bottleneck Principle

The Fisher–Rao distance on a finite probability simplex is bounded by π — a constant independent of problem size.  The geodesic between "unsolved" and "solved" can be short.  **The barrier is not about endpoint distance.**

A Turing machine cannot follow the geodesic.  Each step is a pushforward by a local transition — a tiny perturbation constrained to move mass between O(1) configurations.  Near the phase transition, these TM-achievable directions are nearly **orthogonal** to the geodesic direction.  The curvature divergence at α_c quantifies this mismatch and forces the machine to take an exponential detour through distribution space.

The bottleneck is not that all paths from A to B are long, but that all paths from A to B **achievable by sequential local pushforward** are long.

A polynomial-time algorithm has polynomial thermodynamic length (each step contributes bounded Fisher displacement by locality).  The restricted path barrier requires exponential thermodynamic length.  Therefore, no polynomial-time algorithm can cross the barrier.

Heisenberg uncertainty (σ_A σ_B ≥ ℏ/2) and computational hardness (T ≥ e^{cn}/Δ) are **siblings** — both are lower bounds on the Fisher–Rao cost of extracting information.  One limits measurement precision; the other limits computational speed.  Both follow from the Cramér–Rao inequality.  Both are the second law in geometric language.


## Architecture

The proof is organised as a five-file dependency chain, building on the [Information Geometry library](../InformationGeometry/):

```
CostBlind.lean
      │
      ▼
ComputationEmbedding.lean
      │
      ▼
SymmetryBreaking.lean
      │
      ▼
PhaseTransition.lean
      │
      ▼
LocalityBound.lean
```

Each file corresponds to one step of the argument.

### Step 1: Cost-Blind Computation (`CostBlind.lean`)

Formalises the standard Turing machine state graph as a **cost-blind system**: a deterministic transition with no intrinsic metric.  Proves that conjugation by any bijection preserves all structural properties (orbits, cycle structure, reachability) but **scrambles** any externally imposed cost function.

This is why proof barriers exist: the cost-blind model has too much symmetry to carry complexity-theoretic content.

| Result | Statement |
|--------|-----------|
| `conjugate_orbit` | Orbits correspond under conjugation |
| `conjugate_refl` | Conjugation by `id` is the identity |
| `conjugate_conjugate_symm` | Conjugation by φ then φ⁻¹ recovers the original |
| `conjugate_trans` | Conjugation respects composition |
| `conjugate_orbit_length` | Orbit lengths are conjugation-invariant |
| `conjugate_pathCost` | Path costs are scrambled by conjugation |
| `pathCost_preserved_of_invariant` | Only invariant costs survive conjugation |
| `transitionInvariant_of_pathCost_preserved` | Preserved costs must be transition-invariant |
| `pathCost_changed_of_not_invariant` | Non-invariant costs are changed by conjugation |

### Step 2: Computation as a Path on the Fisher Manifold (`ComputationEmbedding.lean`)

Every deterministic computation on a finite configuration space induces a discrete path on the probability simplex.  The **Fisher–Rao distance** gives this path a well-defined **thermodynamic length** — the information-geometric cost of the computation.

Defines the Bhattacharyya coefficient, proves it characterises the Fisher–Rao geodesic distance on finite distributions (d = 2 arccos(BC)), and establishes the fundamental duality:

𝓛[γ] ≤ T · Δ_max   and   d_FR(p₀, p_T) ≤ 𝓛[γ]

Combined: T ≥ 𝓛 / Δ_max.

| Result | Statement |
|--------|-----------|
| `bhattacharyya_self` | BC(p, p) = 1 |
| `bhattacharyya_symm` | BC(p, q) = BC(q, p) |
| `bhattacharyya_nonneg` | 0 ≤ BC(p, q) |
| `bhattacharyya_le_one` | BC(p, q) ≤ 1 (Cauchy–Schwarz) |
| `fisherRao_self` | d(p, p) = 0 |
| `fisherRao_symm` | d(p, q) = d(q, p) |
| `fisherRao_nonneg` | 0 ≤ d(p, q) |
| `fisherRao_le_pi` | d(p, q) ≤ 2π (diameter bound) |
| `fisherRao_eq_zero_iff` | d(p, q) = 0 ↔ p = q (positive definiteness) |
| `fisherRao_triangle` | Triangle inequality |
| `thermodynamicLength_nonneg` | 0 ≤ 𝓛[γ] |
| `thermodynamicLength_mono` | Extending a path only increases length |
| `thermodynamicLength_ge_endpoint_distance` | d_FR(p₀, p_T) ≤ 𝓛 |
| `length_le_steps_mul_bound` | 𝓛 ≤ T · Δ |
| `steps_ge_of_length_ge` | T ≥ L / Δ |
| `poly_time_poly_length` | T = poly(n) ⟹ 𝓛 ≤ poly(n) |

Also defines `FinDist` (finite distributions), `pushforward`, `iteratePush`, `ComputationPath`, `LocallyBoundedTransition`, and the `FisherBridge` (axiomatised connection to the continuous `StatisticalManifold`).

### Step 3: The Fisher Metric Breaks the Symmetry (`SymmetryBreaking.lean`)

The Fisher metric breaks the cost-blind symmetry via two mechanisms:

1. **Canonicality (Chentsov):** The Fisher–Rao metric is the unique Riemannian metric invariant under sufficient statistics.  It is forced, not chosen.

2. **Distributional nature:** The thermodynamic length depends on the initial distribution, not just the transition function.  The same transition with different distributions yields different thermodynamic lengths — impossible for any per-edge cost.

Proves that coherent conjugation (relabeling both dynamics and distribution) preserves thermodynamic length, but incoherent conjugation (relabeling only dynamics) generically does not.  Assembles the `SeparationPrinciple`: the template for converting geometric lower bounds into step-count lower bounds.

| Result | Statement |
|--------|-----------|
| `bhattacharyya_pushforward_bij` | Bijective pushforward preserves BC |
| `fisherRao_pushforward_isometry` | Bijective pushforward is a Fisher–Rao isometry |
| `same_transition_different_length` | Same transition, different distributions → different 𝓛 |
| `coherent_conjugation_preserves_length` | 𝓛(φ ∘ f ∘ φ⁻¹, φ_* D) = 𝓛(f, D) |
| `incoherent_conjugation_changes_length` | 𝓛(φ ∘ f ∘ φ⁻¹, D) ≠ 𝓛(f, D) generically |
| `SeparationPrinciple.step_lower_bound` | T ≥ L / Δ_max |
| `SeparationPrinciple.step_lower_bound_from_ratio` | T ≥ B whenever L/Δ ≥ B |

### Step 4: Restricted Path Barrier at the Phase Transition (`PhaseTransition.lean`)

At the random k-SAT phase transition (α ≈ 4.267 for k = 3), the Fisher curvature diverges — the solution space shatters into exponentially many clusters, creating an information-geometric **bottleneck**.

The geodesic between "unsolved" and "solved" distributions may be short (≤ π).  But a Turing machine cannot follow the geodesic: its steps are local pushforwards, and near the phase transition these directions are nearly orthogonal to the geodesic.  The machine is forced to take an exponential detour.

Any computation that crosses this bottleneck with per-step displacement ≤ `maxStepSize` must accumulate exponential thermodynamic length.  This is the load-bearing step.

Axiomatised at three levels: abstract restricted path barrier, curvature origin, and SAT specialisation.  All logical consequences are **proved** from the axioms.  Includes a **Curie–Weiss proof of concept** showing that the method correctly predicts polynomial (not exponential) barriers for mean-field problems.

| Result | Statement |
|--------|-----------|
| `PhaseTransitionBarrier.length_lower_bound` | 𝓛[γ] ≥ exp(c·n) for locally-constrained paths |
| `PhaseTransitionBarrier.step_lower_bound` | T ≥ exp(c·n) / Δ |
| `PhaseTransitionBarrier.steps_exponential` | T ≥ B whenever exp(cn)/Δ ≥ B |
| `PhaseTransitionBarrier.toSeparationPrinciple` | Barrier → SeparationPrinciple (proved) |
| `CurvatureOrigin.toBarrier` | Curvature divergence → restricted path barrier |
| `CurvatureOrigin.length_lower_bound` | 𝓛 ≥ exp(c'·n) from curvature origin |
| `CurvatureOrigin.step_lower_bound` | T ≥ exp(c'·n) / Δ from curvature origin |
| `SATBarrier.exponential_sat_steps` | T_SAT ≥ exp(c·n) / Δ |
| `SATBarrier.poly_time_contradicts_barrier` | T · Δ < exp(c·n) ⟹ ⊥ |
| `CurieWeissBarrier.toBarrier` | Mean-field → polynomial barrier (proof of concept) |

### Step 5: Locality Bound and Final Assembly (`LocalityBound.lean`)

A Turing machine is a local dynamical system: each step reads one cell, writes one cell, moves one position.  This bounds the per-step Fisher–Rao displacement by a constant depending on the machine but not the problem size — the classical **Lieb–Robinson bound**.

Assembles the `ComplexityHypothesis` (the complete axiom manifest), proves `poly_lt_exp_eventually` (polynomial < exponential for large n), and derives the final theorem.

| Result | Statement |
|--------|-----------|
| `TMTransition.step_displacement_bounded` | d_FR(p_t, p_{t+1}) ≤ Δ |
| `TMTransition.poly_time_poly_length` | T = poly(n) ⟹ 𝓛 ≤ poly(n) |
| `TMTransition.steps_from_barrier` | T ≥ L / Δ from barrier + locality |
| `poly_lt_exp_eventually` | C · n^k < exp(c·n) for large n (**proved**) |
| `ComplexityHypothesis.exponential_steps_required` | T ≥ exp(c·n) / Δ |
| **`ComplexityHypothesis.poly_time_sat_false`** | **T · Δ < exp(c·n) ⟹ ⊥** |
| `asymptotic_sat_exponential` | For all large n, no poly-time machine solves SAT |


## The Axiom Manifest

All unproved physical content is in named fields of Lean 4 structures (Approach A: axiomatise, then backfill).  There are no hidden axioms.

| # | Axiom | Structure | Field | Physical Content |
|---|-------|-----------|-------|-----------------|
| 1 | Restricted path length | `PhaseTransitionBarrier` | `restricted_length_exponential` | 𝓛 ≥ exp(cn) for locally-constrained paths crossing the SAT transition |
| 2 | Fisher info divergence | `CurvatureOrigin` | `info_diverges` | I(α_c) ≥ exp(cn) (curvature singularity) |
| 3 | Restricted path bound | `CurvatureOrigin` | `restricted_path_bound` | 𝓛 ≥ exp(c'n) for locally-constrained paths through the transition |
| 4 | Solver endpoints | `SATBarrier` | `solver_endpoints` | A correct SAT solver maps inputDist to outputDist |
| 5 | TM locality | `TMTransition` | `displacement_bounded` | d_FR(p, f_*p) ≤ Δ for all distributions p |
| 6 | Step compatibility | `ComplexityHypothesis` | `h_step_compat` | TM displacement ≤ barrier maxStepSize |
| 7 | Chentsov invariance | `ChentsovAxioms` | `fisher_markov_invariant` | Fisher–Rao is preserved under sufficient statistics |
| 8 | Chentsov uniqueness | `ChentsovAxioms` | `uniqueness` | Fisher–Rao is the unique such metric (up to scale) |

Axioms 1–3 are the "physics" (thermodynamic content).
Axiom 4 is the "encoding" (computer science content).
Axiom 5 is the "locality" (speed-of-light for computation).
Axiom 6 is the "compatibility" (the barrier applies to this TM).
Axioms 7–8 are the "canonicality" (information-geometric uniqueness).

### Approach B discharge paths

| Axiom | Discharge Route |
|-------|-----------------|
| 1, 3 | Show TM-achievable directions are orthogonal to the geodesic near α_c; integrate divergent Fisher info over the bottleneck |
| 2 | Finite-size scaling of the partition function; susceptibility–Fisher identity χ = I |
| 4 | Standard Turing machine encoding theory |
| 5 | Bhattacharyya bound for distributions differing on O(1) atoms |
| 6 | Follows from (5): Δ = O(1), so any constant maxStepSize suffices |
| 7–8 | Campbell (1986) for finite sample spaces |

### What changed from v1

The old Axiom 1 (`distance_exponential`) asserted `d_FR(input, output) ≥ exp(cn)`.  This was **unsatisfiable**: the file's own `fisherRao_le_pi` proves `d_FR ≤ 2π`, and with `bhattacharyya_nonneg` giving BC ≥ 0, the tight bound is `d_FR ≤ π`.  For any c > 0 and n ≥ 2, exp(cn) > π.  The structure `PhaseTransitionBarrier` was **uninhabitable** — combining the old axiom with `fisherRao_le_pi` would derive `False` directly, no SAT required.  The axiom system was inconsistent on purely geometric grounds.

The new Axiom 1 (`restricted_length_exponential`) asserts that *locally-constrained paths* have exponential **thermodynamic length**.  This is satisfiable: a path can wind through high-curvature regions, accumulating arbitrarily large total length even between nearby endpoints.  The new Axiom 6 (`h_step_compat`) ensures the barrier applies to TM computation paths.


## Sorry Inventory

| File | Count | Statement | Difficulty |
|------|-------|-----------|------------|
| `CostBlind.lean` | 0 | — | — |
| `ComputationEmbedding.lean` | 1 | `arccos_bhattacharyya_triangle` — spherical triangle inequality | Medium |
| `SymmetryBreaking.lean` | 1 | `distribution_dependence_exists` — point mass construction on `Fintype` | Low |
| `PhaseTransition.lean` | 0 | — | — |
| `LocalityBound.lean` | 0 | — | — |

None of the sorries are in the critical proof chain.  Both are standard results with clear proof strategies.

`poly_lt_exp_eventually` (polynomial < exponential for large n) is now **fully proved** via Mathlib's `isLittleO_pow_exp_pos_mul_atTop`.


## Dependency Map

```
                    ┌─────────────────────────────────────────┐
                    │       Information Geometry Library      │
                    │                                         │
                    │  StatisticalModel ─► Score              │
                    │       ─► FisherInformation              │
                    │       ─► FisherMetric                   │
                    │       ─► StatisticalManifold            │
                    │       ─► CramerRao                      │
                    └──────────────┬──────────────────────────┘
                                   │
          ┌────────────────────────┼────────────────────┐
          │                        │                    │
          ▼                        ▼                    │
   CostBlind.lean       ComputationEmbedding.lean       │
          │                        │                    │
          └──────────┬─────────────┘                    │
                     ▼                                  │
           SymmetryBreaking.lean                        │
                     │                                  │
                     ▼                                  │
           PhaseTransition.lean ◄───────────────────────┘
                     │
                     ▼
           LocalityBound.lean
                     │
                     ▼
         poly_time_sat_false : False
```


## The Proof Chain (Corrected)

The old argument:

```
d_FR(input, output) ≥ exp(cn)     ← FALSE (bounded by π)
d_FR(start, end) ≤ 𝓛              ← TRUE but useless
∴ 𝓛 ≥ exp(cn)                     ← doesn't follow
```

The corrected argument:

```
d_FR(input, output) ≤ π           ← TRUE (small!)
geodesic is short                  ← TRUE
but TM can't follow the geodesic  ← THIS is the real argument
TM is forced through a bottleneck ← THIS is where curvature matters
each step ≤ maxStepSize            ← locality (Axiom 5)
maxStepSize ≤ barrier threshold    ← compatibility (Axiom 6)
∴ 𝓛_TM ≥ exp(cn)                  ← restricted path barrier (Axiom 1)
∴ T ≥ exp(cn) / Δ                 ← length–step duality (proved)
∴ T · Δ < exp(cn) → ⊥             ← poly_time_sat_false (proved)
```


## Proof of Concept: Curie–Weiss

The `CurieWeissBarrier` structure validates the method on a model where the answer is known.  For the Curie–Weiss mean-field model with n spins:

- Fisher information at β_c: I(β_c) ~ n^{4/3}
- Restricted path length through the transition: ~ n^{2/3}

This is **polynomial** — correctly reflecting that mean-field problems are computationally easy.  The method produces exponential barriers only when the solution space shatters (as in random k-SAT), not for every phase transition.


## The Sibling Theorems

This proof stack sits alongside the [Quantum Uncertainty from Information Geometry](../CramerRao.lean) development, which derives the **Heisenberg uncertainty principle** from the Cramér–Rao bound:

σ_A σ_B ≥ ℏ/2

Both results flow from the same source:

| | Uncertainty | Computational Hardness |
|---|---|---|
| **Bound** | σ_A σ_B ≥ ℏ/2 | T ≥ exp(cn) / Δ |
| **Source** | Cramér–Rao inequality | Cramér–Rao inequality |
| **Mechanism** | Fisher information of phase shift | Fisher curvature at phase transition |
| **What it limits** | Measurement precision | Computational speed |
| **Physical content** | Can't extract conjugate info for free | Can't cross entropy barriers for free |
| **Violation implies** | ∞ energy → black hole | ∞ entropy production → black hole |

The second law does not merely *permit* quantum uncertainty and computational hardness.  It *requires* them.


## Building

Requires Lean 4 and Mathlib4.  With [elan](https://github.com/leanprover/elan) installed:

```bash
lake build
```

The files live under `LogosLibrary/QuantumComputing/PvNP/` and import each other linearly as shown in the architecture diagram above.


## References

### Information Geometry
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- N. N. Čencov, *Statistical Decision Rules and Optimal Inference*, AMS, 1982.
- L. L. Campbell, "An extended Čencov characterization of the information metric", *Proc. AMS* **98** (1986), 135–141.
- R. A. Fisher, "On the mathematical foundations of theoretical statistics", *Phil. Trans. Roy. Soc. London A* **222** (1922), 309–368.
- C. R. Rao, "Information and accuracy attainable in the estimation of statistical parameters", *Bull. Calcutta Math. Soc.* **37** (1945), 81–91.

### Phase Transitions and Computational Complexity
- D. Achlioptas, A. Coja-Oghlan, "Algorithmic barriers from phase transitions", *FOCS* (2008), 793–802.
- J. Ding, A. Sly, N. Sun, "Proof of the satisfiability conjecture for large k", *Ann. Math.* **196** (2022), 1–388.
- M. Mézard, G. Parisi, R. Zecchina, "Analytic and algorithmic solution of random satisfiability problems", *Science* **297** (2002), 812–815.
- R. Monasson, R. Zecchina et al., "Determining computational complexity from characteristic phase transitions", *Nature* **400** (1999), 133–137.

### Thermodynamic Geometry
- G. Ruppeiner, "Riemannian geometry in thermodynamic fluctuation theory", *Rev. Mod. Phys.* **67** (1995), 605–659.
- W. Janke et al., "Information geometry and phase transitions", *Physica A* **336** (2004), 181–186.

### Computation and Physics
- R. Landauer, "Irreversibility and heat generation in the computing process", *IBM J. Res. Dev.* **5** (1961), 183–191.
- S. Lloyd, "Ultimate physical limits to computation", *Nature* **406** (2000), 1047–1054.
- N. Margolus, L. B. Levitin, "The maximum speed of dynamical evolution", *Physica D* **120** (1998), 188–195.

### Proof Barriers
- T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question", *SIAM J. Comput.* **4** (1975), 431–442.
- A. Razborov, S. Rudich, "Natural proofs", *J. Comput. Syst. Sci.* **55** (1997), 24–35.
- S. Aaronson, A. Wigderson, "Algebrization: A new barrier in complexity theory", *TOCT* **1** (2009), 1–54.

### Quantum Uncertainty
- S. Braunstein, C. Caves, "Statistical distance and the geometry of quantum states", *Phys. Rev. Lett.* **72** (1994), 3439–3443.
- H. P. Robertson, "The uncertainty principle", *Phys. Rev.* **34** (1929), 163–164.

### Speed Limits
- E. H. Lieb, D. W. Robinson, "The finite group velocity of quantum spin systems", *Commun. Math. Phys.* **28** (1972), 251–257.
- L. B. Levitin, T. Toffoli, "Fundamental limit on the rate of quantum dynamics", *Phys. Rev. Lett.* **103** (2009), 160502.


## A Note on Eddington

> *"If someone points out to you that your pet theory of the universe is in disagreement with Maxwell's equations — then so much the worse for Maxwell's equations.  But if your theory is found to be against the second law of thermodynamics I can give you no hope; there is nothing for it but to collapse in deepest humiliation."*
>
> — Sir Arthur Eddington, *The Nature of the Physical World* (1928)

If P = NP, a polynomial-time SAT solver could extract exponential information at polynomial entropy cost.  This violates the second law.  There is nothing for it but to collapse in deepest humiliation — literally, into a black hole.

> *"P ≠ NP for subsystems scrub.  Get Gewd."*
>
> — Doctor Professor Baron von Wobble-Bob


## License

Apache 2.0.  See [LICENSE](LICENSE).

## Authors

Adam Bornemann & contributor
