# Thermal Bell

A formal development of the **thermal hidden variable framework** for Bell's theorem in [Lean 4](https://lean-lang.org/) with [Mathlib4](https://github.com/leanprover-community/mathlib4).

Bell's theorem assumes **measurement independence**: the hidden variable distribution ρ(λ) is independent of the detector settings (a, b). In any universe with a common causal origin, unscreenable gravity, and finite-temperature thermal baths carrying KMS structure, perfect independence is unphysical. This library formalises the minimal relaxation — a single parameter ε controlling the deviation from independence — and proves that the resulting CHSH bound structure is completely determined by modular geometry.

## The Central Results

The CHSH value decomposes additively:

$$S \;=\; S_{\text{classical}} \;+\; S_{\text{thermal}}$$

where $|S_{\text{classical}}| \leq 2$ (Bell's bound on the base measure) and $|S_{\text{thermal}}| \leq 4\varepsilon_{\max}$. Combined:

$$|S| \;\leq\; 2 + 4\varepsilon_{\max}$$

Setting $\varepsilon = 0$ recovers the standard LHV framework exactly, with a verified bridge to the `BellTheorem.LHVModel` type.

The critical deviation value $\varepsilon_{\text{tsirelson}} = (\sqrt{2} - 1)/2$ satisfies

$$2 + 4\varepsilon_{\text{tsirelson}} \;=\; 2\sqrt{2}$$

and is **forced** by KMS periodicity: the modular period $2\pi$, divided among the 8 angle slots of the CHSH structure, gives the per-slot angle $\pi/4$. The cosine-based KMS bound at this angle yields $\varepsilon_{\text{tsirelson}}$ exactly.

### The Geometric Comparison (DecayGap)

Two correlation kernels are compared at the modular separation $\theta = \pi/4$:

| Geometry | Kernel | $\varepsilon_{\max}$ | CHSH bound | Leading term at $\theta = 0$ |
|----------|--------|-----------|------------|------------------------------|
| Flat $\mathbb{R}$ | $e^{-\theta}$ | $\approx 0.456$ | $\approx 3.82$ | Linear: $1 - \theta$ |
| $S^2$ ($\kappa = 2$) | $(1 - \cos\theta)/\sqrt{2}$ | $\approx 0.207$ | $= 2\sqrt{2}$ | Quadratic: $\theta^2 / 2\sqrt{2}$ |

The gap of $\approx 1$ on the CHSH scale is the **curvature correction**: the quantum state space is spherical, not flat. This is proved, not assumed — the key inequality is

$$3 - \pi/2 > \sqrt{2}$$

which, via the first-order Taylor bound $1 - \pi/4 \leq e^{-\pi/4}$, yields `exp_exceeds_tsirelson`: the flat-space propagator strictly overshoots $\varepsilon_{\text{tsirelson}}$. The extra suppression in the cosine kernel comes from the curvature of $S^2$.


## What Is Proved (Zero `sorry`)

### Core (Core.lean)

| Result | Statement |
|--------|-----------|
| `effectiveMeasure_isProbability` | $d\mu_{ij} = (1 + \varepsilon_{ij})\,d\mu_0$ is a probability measure |
| `chsh_pointwise_values` | Pointwise CHSH takes values $\pm 2$ for dichotomic inputs |

### CHSH Bounds (CHSH.lean)

| Result | Statement |
|--------|-----------|
| `CHSH_decomposition` | $S = S_{\text{classical}} + S_{\text{thermal}}$ |
| `CHSH_classical_bound` | $\|S_{\text{classical}}\| \leq 2$ |
| `CHSH_thermal_bound` | $\|S_{\text{thermal}}\| \leq 4\varepsilon_{\max}$ |
| `thermal_chsh_bound` | $\|S\| \leq 2 + 4\varepsilon_{\max}$ |
| `classical_bound_from_thermal` | $\varepsilon = 0 \implies \|S\| \leq 2$ |
| `thermal_CHSH_eq_lhv_CHSH` | $\varepsilon = 0$ model agrees with `LHVModel.CHSH` |
| `classical_bound_via_lhv` | Bell's bound derived via `lhv_chsh_bound` |
| `thermal_bound_tight` | The bound $2 + 4\varepsilon$ is achievable |
| `thermal_covers_quantum_range` | Every $S \in (2,\, 2\sqrt{2}]$ is reachable |
| `thermal_chsh_limit` | $S \to 2$ as thermal separation $\to \infty$ |
| `correlation_decay` | $e^{-t/\tau} \to 0$ as $t \to \infty$ |

### Tsirelson from KMS (Tsirelson.lean)

| Result | Statement |
|--------|-----------|
| `ε_tsirelson_value` | $2 + 4\varepsilon_{\text{tsirelson}} = 2\sqrt{2}$ |
| `ε_tsirelson_unique` | $\varepsilon_{\text{tsirelson}}$ is the unique non-negative value giving $2\sqrt{2}$ |
| `tsirelson_from_modular_geometry` | $4 \cos(2\pi / 8) = 2\sqrt{2}$ |
| `kms_constrains_epsilon` | KMS periodicity forces $\|\varepsilon\| \leq \varepsilon_{\text{tsirelson}}$ pointwise |
| `tsirelson_from_kms` | Every KMS-constrained thermal model obeys $\|S\| \leq 2\sqrt{2}$ |
| `realization_saturates` | A quantum realization achieving $2\sqrt{2}$ forces $\varepsilon_{\max} = \varepsilon_{\text{tsirelson}}$ |
| `thermal_bell_chain` | Period → slots → angle → cosine → $\varepsilon$ → $2\sqrt{2}$, one chain |
| `thermal_determines_bounds` | Classical at $\varepsilon = 0$, Tsirelson at $\varepsilon_{\text{tsirelson}}$, uniqueness |
| `quantum_chsh_optimal` | Singlet at optimal angles achieves $2\sqrt{2}$ |

### Geometric Comparison (DecayGap.lean)

| Result | Statement |
|--------|-----------|
| `exp_exceeds_tsirelson` | $e^{-\pi/4} > \varepsilon_{\text{tsirelson}}$: flat overshoots spherical |
| `exponential_chsh_exceeds_tsirelson` | $2 + 4e^{-\pi/4} > 2\sqrt{2}$ |
| `curvature_correction_positive` | The CHSH gap between flat and spherical is strictly positive |
| `modular_thermal_epsilon_bound` | Pointwise $\varepsilon$ bound from the exponential model |
| `exponential_modular_chsh_bound` | Honest exponential CHSH bound: $\|S\| \leq 2 + 4e^{-\pi/4}$ |
| `exp_bound_strictly_weaker` | Exponential bound is strictly weaker than Tsirelson |
| `both_trivial_at_zero` | Both kernels agree trivially at $\theta = 0$ |

### Constraints (Constraints.lean)

| Result | Statement |
|--------|-----------|
| `chshOptimal_thermal` | Optimal deviation pattern gives $S_{\text{thermal}} = 4\delta$ |
| `chshOptimal_noSignaling_implies_balanced` | No-signaling + optimal pattern $\implies$ balanced marginals |
| `quantum_compatible_constraint` | $E_C = 0$ with $\|E_Q\| = 1$ is incompatible |
| `E_C_nonzero_at_extremes` | At $\theta = 0$ (perfect correlation), $E_C \neq 0$ |
| `classical_correlation_lower_bound` | $\|E_C\| \geq 1 - \varepsilon_{\max}$ at $\theta = 0$ |
| `abs_integral_ABε_lt_one` | The thermal correction is strictly bounded: $\|\int AB\varepsilon\| < 1$ |

### Algebraic Structure (Geometry.lean)

| Result | Statement |
|--------|-----------|
| `quantum_is_sum_of_conjugates` | $2\sqrt{2} = \beta + 1/\beta$ where $\beta = \sqrt{2} - 1$ |
| `classical_is_diff_of_conjugates` | $2 = 1/\beta - \beta$ |
| `ε_from_bounds` | $\varepsilon_{\text{tsirelson}} = 1/(S_{\text{quantum}} + S_{\text{classical}})$ |
| `ε_tsirelson_three_faces` | Algebraic, from-bounds, and $\sin^2(\pi/8)$ characterisations |
| `epsilon_hierarchy` | $0 < \varepsilon_{\text{tsirelson}} < \varepsilon_{\text{PR}} < 1$ |
| `classical_bound_from_complementarity` | Why $\|S_{\text{classical}}\| \leq 2$: Bob's combinations are complementary |
| `tsirelson_as_correlations_times_cosine` | $S_{\text{quantum}} = n_{\text{corr}} \cdot \cos(2\pi / n_{\text{phase}})$ |

### Entropy & Decay (Entropy.lean)

| Result | Statement |
|--------|-----------|
| `zeno_entropy` | $n$ same-setting measurements cost only one $2\pi$ (Zeno effect) |
| `same_setting_perfect_correlation` | Same-setting correlation is exactly 1, regardless of $\varepsilon$ |
| `ε_decreasing` | Longer thermal separation $\implies$ smaller $\varepsilon$ |
| `hot_fast` / `cold_limit_time` | Hot detectors have short thermal time; cold detectors, long |
| `hot_limit_time` | $T \to \infty \implies$ thermal time $\to 0$ |


## Architecture

```
Core.lean                   Model definitions, effective measure, CHSH decomposition setup
    │
    ├──▶ CHSH.lean           Main bounds, classical reduction, decay structure
    │       │
    │       └──▶ DecayGap.lean   Exponential vs cosine: curvature correction
    │
    ├──▶ Tsirelson.lean      KMS-constrained bound, saturation, master theorem
    │
    └──▶ Constraints.lean    No-signaling, optimal patterns, quantum compatibility
            │
            └── (uses Geometry.lean internally)

Entropy.lean                Measurement entropy, Zeno effect, thermal time decay
```

### External Dependencies

```
LogosLibrary.QuantumMechanics.BellsTheorem.LHV     Standard LHV model and |S| ≤ 2
LogosLibrary.QuantumMechanics.ModularTheory.KMS     KMS condition
LogosLibrary.QuantumMechanics.ModularTheory.ThermalTime   Thermal time hypothesis
Mathlib.MeasureTheory.*                              Bochner integral, probability measures
Mathlib.Analysis.SpecialFunctions.*                  exp, cos, sqrt, π bounds
Mathlib.Analysis.Real.Pi.Bounds                      3.1415 < π < 3.1416
```


## Design Decisions

**Single parameter.** The entire framework is controlled by one function $\varepsilon : \text{Fin}\,2 \to \text{Fin}\,2 \to \Lambda \to \mathbb{R}$ measuring the deviation from statistical independence. This is the minimal relaxation: one parameter, four setting pairs, pointwise in the hidden variable space.

**Two correlation structures.** The exponential kernel (`ThermalCorrelationStructure`) captures the physical picture of decoherence over thermal time. The cosine kernel (`KMSCorrelationStructure`) captures the tight constraint from modular geometry. The DecayGap file proves the exponential is strictly weaker and quantifies the gap.

**Honest bookkeeping.** The `CorrelationDeviation` structure carries four fields: measurability, strict boundedness ($|\varepsilon| < 1$), normalisation ($\int \varepsilon = 0$), and integrability. The factored helpers in Constraints.lean (`dichotomic_memLp`, `prod_ε_integrable`, etc.) eliminate ~500 lines of repeated integrability proofs.

**Classical reduction is structural.** Setting $\varepsilon = 0$ doesn't just give the right bound — it gives a definitional `rfl` when comparing `ThermalHVModel.CHSH` with `LHVModel.CHSH`. The thermal framework is a strict generalisation, not an analogy.


## The Physical Picture

The standard Bell argument assumes that the hidden variable distribution $\rho(\lambda)$ is independent of the detector settings $a, b$. In a thermal universe, this cannot be exact: the detectors, the source, and the hidden variables all share a common thermal bath with KMS structure. The deviation $\varepsilon$ quantifies the residual correlation leaking through the thermal bath.

The KMS condition (periodicity of the modular automorphism group with period $2\pi$) constrains how large this leakage can be. The CHSH structure has 8 angle slots (from $2^4 = 16$ sign configurations and 2 CHSH eigenvalues). Distributing the modular period evenly: $\theta = 2\pi/8 = \pi/4$. The cosine at this angle determines everything.

The exponential decay model treats the thermal bath as flat space ($\mathbb{R}$). The cosine model treats it as the Bloch sphere ($S^2$ with Gaussian curvature $\kappa = 2$). The curvature correction — proved in DecayGap.lean — is the difference between $e^{-\pi/4} \approx 0.456$ and $(1 - \cos(\pi/4))/\sqrt{2} \approx 0.207$, which maps to $\approx 1$ unit on the CHSH scale. The $\sqrt{2}$ in the denominator is $\sqrt{\kappa}$.


## Connection to the Broader Library

ThermalBell sits at the intersection of three developments in LogosLibrary:

- **Bell's Theorem** (`BellsTheorem/LHV`): The standard LHV model and $|S| \leq 2$. ThermalBell extends this with `ThermalHVModel.toLHV` and proves agreement at $\varepsilon = 0$.

- **Modular Theory** (`ModularTheory/`): The KMS condition, Tomita-Takesaki theory, and the Connes cocycle. The KMS periodicity $2\pi$ is the structural input to `KMSCorrelationStructure`. The cocycle theorem (`connes_cocycle_identity`) proves the thermal time flow is state-independent, which is why the modular period is physically meaningful.

- **Information Geometry** (`InformationGeometry/`): The Fisher-Rao metric, Cramér-Rao bound, and the quantum uncertainty derivation via `QuantumPhaseModel`. The cosine bound's $\sqrt{2}$ will eventually be derived from the Gaussian curvature of the Fisher-Rao metric on the qubit state space. The saturation theorem `realization_saturates` will unify through Cramér-Rao efficiency.


## Future Work

- **`CHSHEstimationModel`** — Package the CHSH game as a four-parameter estimation problem on the Fisher-Rao sphere. Unify `realization_saturates` through Cramér-Rao efficiency rather than the current squeeze argument.
- **Curvature derivation** — Derive $\sqrt{2} = \sqrt{\kappa}$ from the Fisher-Rao metric on the qubit state space, making the cosine bound a theorem rather than a structural input.
- **Higher-dimensional bounds** — For qutrits on $\mathbb{C}P^2$, the curvature changes and the Tsirelson-type bound generalises accordingly.
- **Antilinear extension** — Push antilinear operators to unbounded observables for the full modular theory connection.


## References

- J. S. Bell, *Speakable and Unspeakable in Quantum Mechanics*, Cambridge, 1987.
- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, "Proposed experiment to test local hidden-variable theories", *Phys. Rev. Lett.* **23** (1969), 880–884.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality", *Lett. Math. Phys.* **4** (1980), 93–100.
- A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation", *Class. Quantum Grav.* **11** (1994), 2899–2917.
- G. 't Hooft, *The Cellular Automaton Interpretation of Quantum Mechanics*, Springer, 2016.
- S. Popescu, D. Rohrlich, "Quantum nonlocality as an axiom", *Found. Phys.* **24** (1994), 379–385.
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- R. E. Summers, R. Werner, "Bell's inequalities and quantum field theory. I. General setting", *J. Math. Phys.* **28** (1987), 2440–2447.


## Building

Requires Lean 4 and Mathlib4. With [elan](https://github.com/leanprover/elan) installed:

```bash
lake build LogosLibrary.QuantumMechanics.BellsTheorem.ThermalBell
```


## License

MIT. See [LICENSE](LICENSE).

## Author

Adam Bornemann & contributors.