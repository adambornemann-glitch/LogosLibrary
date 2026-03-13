# The Sewing Lemma

A formalisation of the Sewing Lemma in four layers of increasing generality, forming the analytic foundation for rough path theory.

## Mathematical Overview

The **Sewing Lemma** constructs additive functionals from almost-additive approximations. Given a two-parameter map $\Xi(s,t)$ whose *defect* $\delta\Xi(s,u,t) = \Xi(s,t) - \Xi(s,u) - \Xi(u,t)$ is controlled by a quantity that vanishes under refinement, there exists a unique additive functional $I(s,t)$ close to $\Xi$.

This is the engine behind:
- **Young integration** ($1/p + 1/q > 1$)
- **Rough integration** (driving signal enhanced with iterated integrals)
- **Regularity structures** (Hairer's generalisation to SPDEs)

### The four layers

| Layer | Defect bound | Proof method | Applications |
|-------|-------------|--------------|--------------|
| **1** | $K \cdot \lvert t - s \rvert^\theta$, $\theta > 1$ | Dyadic geometric series | Hölder paths, Brownian motion |
| **2** | $K \cdot \omega_1(s,u)^\alpha \cdot \omega_2(u,t)^\beta$, $\alpha + \beta > 1$, Lipschitz controls | Dyadic geometric series | Young integration, rough integration |
| **3** | $K \cdot \omega(s,t)^\theta$, $\theta > 1$, continuous super-additive control | Dyadic + theta-energy decay | General theory |
| **4** | Same as Layer 3 | Partition net (directed limit) | General theory, clean additivity |

Layers 1–3 define the sewn map as a limit of dyadic Riemann sums. This gives clean existence proofs but makes general additivity difficult (see [Status](#status)). Layer 4 resolves this by defining the sewn map as a limit over the directed system of *all* partitions ordered by refinement, making additivity essentially definitional.

Layer 1 is the simplest and most concrete. Layer 2 captures the natural product structure arising in integration (integrand variation $\times$ integrator variation). Layer 3 is the full generality of Friz–Hairer and Gubinelli. Layer 4 shares the same hypotheses as Layer 3 but replaces the construction, eliminating the additivity axiom.

## File Structure

```
SewingLemma/
├── Defs.lean                      # Core definitions shared across all layers
├── Condition.lean                 # Layer 1: defect properties, dyadic machinery
│
├── LayerOne/
│   └── Map.lean                   # Sewn map: existence, approximation, uniqueness, additivity
│
├── LayerTwo/
│   └── Map.lean                   # Cross-controlled version: decay, Cauchy, approximation, uniqueness
│
├── LayerThree/
│   ├── Partition.lean             # General partition infrastructure
│   ├── ContinuousControl.lean     # ContControl: monotonicity, super-additive telescoping
│   ├── ThetaEnergy.lean           # Φ_θ: key estimate, mesh→0 convergence, refinement monotonicity
│   ├── DyadicPartition.lean       # Dyadic partitions as Partition objects, Cauchy sequence
│   └── Map.lean                   # Sewn map: existence, approximation, uniqueness, additivity
│
├── LayerFour/                     # 🚧 PLANNED
│   ├── PartitionFilter.lean       # Refinement filter on partitions, directed system
│   ├── RefinementCost.lean        # ‖RS(P) - RS(P')‖ ≤ K · Φ_θ(P) for P' refining P
│   └── Map.lean                   # Sewn map via partition net, additivity, equivalence with Layer 3
│
└── API.lean                       # Convenience interface: sewing_lemma₃
```

## Definitions (`Defs.lean`)

- **`sewingDefect₁`** — The coboundary $\delta\Xi(s,u,t) = \Xi(s,t) - \Xi(s,u) - \Xi(u,t)$.
- **`SewingCondition₁`** / **`SewingCondition₂`** / **`SewingCondition₃`** — The hypothesis bundles for each layer.
- **`dyadicPt`** — The $k$-th point of the $n$-th dyadic partition of $[s,t]$.
- **`dyadicSum₁`** — The $n$-th dyadic Riemann sum $S_n = \sum_{k < 2^n} \Xi(d_k, d_{k+1})$.
- **`sewingMap₁`** / **`sewingMap₂`** / **`sewingMap₃`** — The sewn maps, defined as $\lim_{n \to \infty} S_n$.
- **`Partition`** — A monotone sequence of points with fixed endpoints.
- **`riemannSum`** — The Riemann sum of $\Xi$ over a general partition.
- **`thetaEnergy`** — The theta-energy $\Phi_\theta(P) = \sum_i \omega(t_i, t_{i+1})^\theta$.
- **`ContControl`** — A continuous super-additive control vanishing on the diagonal.
- **`LipControl`** — A Lipschitz-in-length super-additive control.

## Main Results

### Layer 1 (interval-length control)

All proofs complete, no `sorry`.

- **`dyadicSum₁_diff_bound`** — Geometric decay: $\|S_{n+1} - S_n\| \leq K \cdot |t-s|^\theta \cdot 2^{-n(\theta-1)}$.
- **`dyadicSum₁_cauchy`** — Dyadic sums form a Cauchy sequence.
- **`sewingMap₁_dist_le`** — Approximation: $\|I(s,t) - \Xi(s,t)\| \leq K \cdot C_\theta \cdot |t-s|^\theta$.
- **`sewingMap₁_unique`** — Uniqueness among additive functionals with the approximation bound.
- **`sewingMap₁_midpoint`** — Midpoint additivity: $I(s,t) = I(s,m) + I(m,t)$.
- **`sewingMap₁_dyadicSum`** — Dyadic additivity: $I(s,t) = \sum_{k < 2^n} I(d_k, d_{k+1})$.

### Layer 2 (cross-controlled)

All proofs complete, no `sorry`.

- **`dyadicSum₂_diff_bound`** — Geometric decay with rate $2^{-n(\alpha+\beta-1)}$.
- **`dyadicSum₂_cauchy`** — Cauchy sequence.
- **`sewingMap₂_dist_le`** — Approximation bound with explicit constants.
- **`sewingMap₂_unique`** — Uniqueness.

### Layer 3 (general continuous control)

- **`ContControl.mono`** — Super-additivity implies interval monotonicity.
- **`ContControl.sum_le`** — Super-additivity telescopes over partitions: $\sum_i \omega(t_i, t_{i+1}) \leq \omega(s,t)$.
- **`thetaEnergy_le`** — Key estimate: $\Phi_\theta(P) \leq (\max_i \omega_i)^{\theta-1} \cdot \omega(s,t)$.
- **`thetaEnergy_tendsto_zero`** — $\Phi_\theta(P) \to 0$ as mesh $\to 0$ when $\theta > 1$.
- **`thetaEnergy_le_of_refinement`** — Refinement monotonicity: $\Phi_\theta(P') \leq \Phi_\theta(P)$ when $P'$ refines $P$.
- **`dyadicSum₃_diff_bound`** — $\|S_{n+1} - S_n\| \leq K \cdot \Phi_\theta(D_n)$.
- **`dyadicSum₃_cauchy`** — Cauchy via summability of theta-energies.
- **`sewingMap₃_dist_le`** — $\|I(s,t) - \Xi(s,t)\| \leq K \cdot \sum_n \Phi_\theta(D_n)$.
- **`sewingMap₃_unique`** — Uniqueness.
- **`sewingMap₃_midpoint`** — Midpoint additivity.
- **`sewingMap₃_dyadicSum`** — Dyadic additivity.
- **`sewingMap₃_small`** — Continuity near diagonal: $\|I(s,t)\| < \varepsilon$ when $t - s < \delta$.
- **`sewingMap₃_additive`** ⚠️ **axiom** — General additivity at arbitrary points.

### Layer 4 (partition net) — 🚧 Planned

Layer 4 replaces the dyadic limit construction with a limit over the directed system of all partitions of $[s,t]$, ordered by refinement. The sewn map becomes:

$$I(s,t) = \lim_{P \to \infty} \mathrm{RS}(\Xi, P)$$

where the limit is taken in the refinement-directed sense: for any $\varepsilon > 0$, there exists a partition $P_0$ such that $\|\mathrm{RS}(\Xi, P) - I(s,t)\| < \varepsilon$ for all $P$ refining $P_0$.

**Why Layer 4?** General additivity becomes essentially definitional. Given $s \leq u \leq t$, the partitions of $[s,t]$ that contain $u$ form a cofinal subset. On this subnet, $\mathrm{RS}(\Xi, P)$ splits as $\mathrm{RS}(\Xi, P|_{[s,u]}) + \mathrm{RS}(\Xi, P|_{[u,t]})$. Passing to the limit gives $I(s,t) = I(s,u) + I(u,t)$ with no further work.

**What Layer 4 reuses from Layer 3:**
- `SewingCondition₃` — identical hypotheses
- `ContControl` and all its properties (monotonicity, super-additive telescoping)
- `thetaEnergy_le`, `thetaEnergy_tendsto_zero`, `thetaEnergy_le_of_refinement`
- `Partition`, `riemannSum`, `thetaEnergy` — all definitions

**What Layer 4 needs that is new:**
- **Refinement cost bound**: $\|\mathrm{RS}(\Xi, P) - \mathrm{RS}(\Xi, P')\| \leq K \cdot \Phi_\theta(P)$ when $P'$ refines $P$. This is the core analytic lemma — it uses the restriction decomposition (within each interval of $P$, the sub-partition from $P'$ telescopes into defects bounded by $\omega(t_k, t_{k+1})^\theta$ via `range_sum_rpow_le`).
- **Partition filter**: a `Filter` on `Partition s t` generated by the refinement ordering, or equivalently by mesh tending to zero. Needs to be shown directed.
- **Cauchy in the net**: Riemann sums form a Cauchy net, proved via the refinement cost bound and `thetaEnergy_tendsto_zero`.
- **Equivalence with Layer 3**: the partition-net limit agrees with the dyadic limit (both are the unique additive functional with the approximation bound).

**Planned results:**
- `sewingMap₄` — the sewn map as a partition-directed limit
- `sewingMap₄_additive` — general additivity (by cofinal splitting, no axiom)
- `sewingMap₄_eq_sewingMap₃` — equivalence with the dyadic construction
- Discharge of `sewingMap₃_additive` axiom via the equivalence

### API (`API.lean`)

- **`sewing_lemma₃`** — Existence–uniqueness package: produces $I$ with diagonal vanishing, additivity, and the approximation bound.

## Status

### Complete (no `sorry`)
- Layer 1: all results including full additivity
- Layer 2: all results including uniqueness
- Layer 3: existence, approximation, uniqueness, dyadic additivity, diagonal continuity
- Partition infrastructure: monotone embedding from refinement, theta-energy refinement monotonicity
- Coercions: `LipControl → ContControl`

### Open (`axiom`)
- **`sewingMap₃_additive`**: general additivity $I(s,t) = I(s,u) + I(u,t)$ for arbitrary $u \in [s,t]$. Will be discharged by Layer 4.

The dyadic architecture gives additivity at dyadic rationals of $[s,t]$ (via `sewingMap₃_dyadicSum`), but extending to arbitrary points requires comparing Riemann sums over incompatible partition grids. Layer 4 (partition net) resolves this by construction: the sewn map is defined as a directed limit over all partitions, making additivity follow from the cofinal splitting argument. The core analytic input — the refinement cost bound — reuses the theta-energy and `range_sum_rpow_le` machinery already present in Layer 3.

### Planned
- **Layer 4**: partition net construction, general additivity, equivalence with Layer 3.

## Key Design Decisions

**Dyadic-first architecture.** Layers 1–3 define the sewn map as the limit of dyadic Riemann sums. This gives clean inductive proofs (each level pairs into the previous via `dyadicPt_double`) and avoids general partition infrastructure for existence and approximation. The cost is that general additivity requires additional work — resolved by Layer 4's partition net construction.

**Layered hypotheses.** Rather than a single general sewing condition, we provide three increasingly general structures. Layer 1 proofs are simpler and yield sharper constants; Layer 2 captures the product structure natural in integration; Layer 3 handles the abstract theory. Each layer's results are independently useful.

**`rpow` throughout.** Exponents $\theta$, $\alpha$, $\beta$ are real-valued, and all power operations use `Real.rpow`. This avoids coercion issues between `ℕ`, `ℤ`, and `ℝ` exponents at the cost of occasional `rpow_natCast` bridges.

**Partition as structure.** The `Partition` type bundles a number of sub-intervals, a monotone point sequence, and endpoint constraints. This is more structured than Mathlib's `eVariationOn` approach (which uses bare monotone sequences) but provides cleaner access to left/right endpoints and supports the refinement theory.

## Dependencies

- `Mathlib.Analysis.Normed.Group.Basic`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.Topology.Algebra.InfiniteSum.Basic`
- `Mathlib.Topology.Sequences`
- `Mathlib.Topology.UniformSpace.Cauchy`

## References

1. T.J. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoamericana **14** (1998), 215–310.
2. M. Gubinelli, *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140.
3. P.K. Friz, M. Hairer, *A Course on Rough Paths*, 2nd ed., Springer, 2020.
4. P.K. Friz, N.B. Victoir, *Multidimensional Stochastic Processes as Rough Paths*, Cambridge, 2010.