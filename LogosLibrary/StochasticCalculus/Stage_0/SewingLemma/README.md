# The Sewing Lemma

## Overview

The **Sewing Lemma** constructs additive functionals from almost-additive approximations. Given a two-parameter map $\Xi : \mathbb{R} \times \mathbb{R} \to E$ (with $E$ a Banach space) whose failure of additivity — the *defect*

$$\delta\Xi(s, u, t) \;=\; \Xi(s, t) - \Xi(s, u) - \Xi(u, t)$$

is controlled by a quantity that decays under refinement, the sewing lemma produces a unique additive functional $I$ approximating $\Xi$.

This is the foundational construction underlying rough path integration, Young integration, and controlled-path theory. It replaces the classical Riemann–Stieltjes limit with a robust algebraic-analytic framework that extends integration to paths of low regularity — precisely the regime needed for stochastic calculus.

## Mathematical content

The formalization proceeds in three layers of increasing generality. Each layer strengthens the hypotheses on the defect control, with Layer 1 being the simplest and Layer 3 the most general.

### Layer 1: Interval-length control

The defect satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot |t - s|^\theta, \qquad \theta > 1.$$

The interval length distributes perfectly over dyadic subdivision: at level $n$, each sub-interval has length exactly $|t - s| / 2^n$, giving clean geometric decay

$$\|S_{n+1} - S_n\| \;\leq\; K \cdot |t - s|^\theta \cdot 2^{-n(\theta - 1)}$$

with no additional hypotheses on a control function. The condition $\theta > 1$ is sharp — it is precisely what makes the geometric series $\sum 2^{-n(\theta-1)}$ converge.

This version covers all standard Hölder-regularity applications: Brownian motion ($\gamma$-Hölder for $\gamma < 1/2$), fractional Brownian motion ($\gamma$-Hölder for $\gamma < H$), Young integration ($\theta = 1/p + 1/q > 1$), and rough integration with Hölder rough path data.

**Main output.** There exists a unique additive $I$ with

$$\|I(s,t) - \Xi(s,t)\| \;\leq\; \frac{K}{1 - 2^{-(\theta-1)}} \cdot |t - s|^\theta.$$

### Layer 2: Cross-controlled (product) defect bound

The defect satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot \omega_1(s, u)^\alpha \cdot \omega_2(u, t)^\beta, \qquad \alpha + \beta > 1,$$

where each $\omega_i$ is a super-additive control satisfying a Lipschitz-in-length condition $\omega_i(s, t) \leq L_i \cdot (t - s)$.

The product structure is not a mere generalization — it is the *natural* form of the defect in integration theory. When $\Xi(s,t) = Y(s) \cdot (X(t) - X(s))$, the defect

$$\delta\Xi(s, u, t) = -(Y(u) - Y(s)) \cdot (X(t) - X(u))$$

separates into a factor depending on $[s, u]$ (integrand variation) and a factor depending on $[u, t]$ (integrator variation). This separation is what makes the refinement cost bound work — see the discussion under [Open problem](#open-problem-layer-3-general-additivity) below.

Layer 1 is the special case $\omega_1 = \omega_2 = |\cdot|$, $\alpha + \beta = \theta$, $L_1 = L_2 = 1$.

**Main output.** There exists a unique additive $I$ with

$$\|I(s,t) - \Xi(s,t)\| \;\leq\; \frac{K \cdot L_1^\alpha \cdot L_2^\beta}{2^{\alpha+\beta}\,(1 - 2^{-(\alpha+\beta-1)})} \cdot |t - s|^{\alpha + \beta}.$$

Additionally, Riemann sums over *any* sequence of partitions with mesh $\to 0$ converge to $I$ (`riemannSum_tendsto_sewingMap₂`).

### Layer 3: General continuous control

The defect satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot \omega(s, t)^\theta, \qquad \theta > 1,$$

where $\omega$ is a continuous super-additive control (vanishing on the diagonal, with $\omega(s,t) \to 0$ uniformly as $t - s \to 0$). This is the version stated in Friz–Hairer (Theorem 2.2) and used in the general theory of rough paths. It makes no assumption about the relationship between $\omega(s,t)$ and $|t - s|$ beyond continuity.

The key convergence mechanism is the **$\theta$-energy**

$$\Phi_\theta(P) \;=\; \sum_i \omega(t_i, t_{i+1})^\theta,$$

which satisfies

$$\Phi_\theta(P) \;\leq\; \Bigl(\max_i\, \omega(t_i, t_{i+1})\Bigr)^{\theta - 1} \cdot \omega(s, t).$$

Since $\theta > 1$, the max term vanishes as the mesh refines (by continuity of $\omega$), while the sum $\sum \omega_i$ stays bounded by super-additivity. For $\theta = 1$ this mechanism fails — $\Phi_1$ is bounded but does not vanish. This is the analytical reason $\theta > 1$ is necessary.

**Main output.** There exists a unique additive $I$ with

$$\|I(s,t) - \Xi(s,t)\| \;\leq\; K \cdot \sum_{n=0}^{\infty} \Phi_\theta(D_n(s,t)),$$

where $D_n$ is the $n$-th dyadic partition. Full additivity is proved for dyadic split points; general additivity for arbitrary split points is an open formalization problem (see below).

## Main results

### Layer 1 (`SewingCondition₁`)
| Result | Theorem | Status |
|---|---|---|
| Geometric decay of dyadic sums | `dyadicSum₁_diff_bound` | ✓ |
| Cauchy sequence | `dyadicSum₁_cauchy` | ✓ |
| Approximation bound | `sewingMap₁_dist_le` | ✓ |
| Uniqueness | `sewingMap₁_unique` | ✓ |
| Midpoint additivity | `sewingMap₁_midpoint` | ✓ |
| Dyadic additivity | `sewingMap₁_dyadicSum` | ✓ |

### Layer 2 (`SewingCondition₂`)
| Result | Theorem | Status |
|---|---|---|
| Geometric decay | `dyadicSum₂_diff_bound` | ✓ |
| Cauchy sequence | `dyadicSum₂_cauchy` | ✓ |
| Approximation bound | `sewingMap₂_dist_le` | ✓ |
| Uniqueness | `sewingMap₂_unique` | ✓ |
| Right-peeling telescoping | `right_peel_telescope` | ✓ |
| Refinement cost bound | `riemannSum_refinement_bound₂` | ✓ |
| General additivity | `sewingMap₂_additive` | ✓ |
| General convergence (mesh → 0) | `riemannSum_tendsto_sewingMap₂` | ✓ |
| Bundled API | `sewing_lemma₂` | ✓ |

### Layer 3 (`SewingCondition₃`)
| Result | Theorem | Status |
|---|---|---|
| Dyadic sum bound via θ-energy | `dyadicSum₃_diff_bound` | ✓ |
| Cauchy sequence | `dyadicSum₃_cauchy` | ✓ |
| Approximation bound | `sewingMap₃_dist_le` | ✓ |
| Uniqueness | `sewingMap₃_unique` | ✓ |
| Midpoint additivity | `sewingMap₃_midpoint` | ✓ |
| Dyadic additivity | `sewingMap₃_dyadicSum` | ✓ |
| θ-energy vanishes under refinement | `thetaEnergy_tendsto_zero` | ✓ |
| θ-energy monotone under refinement | `thetaEnergy_le_of_refinement` | ✓ |
| General additivity | `sewingMap₃_additive` | **TODO** |

### Supporting infrastructure
| Result | Theorem |
|---|---|
| Partition merge (common refinement) | `Partition.merge` |
| Merge refines both inputs | `merge_refines_left/right` |
| Mesh decreases under refinement | `mesh_refinement_le` |
| Riemann sum splitting at a point | `riemannSum_split` |
| Lipschitz implies continuous control | `contControl_of_lipControl` |
| Super-additivity over partitions | `ContControl.sum_le` |

## Open problem: Layer 3 general additivity

The one unproved result is `sewingMap₃_additive`: full additivity $I(s,t) = I(s,u) + I(u,t)$ for arbitrary $u \in [s,t]$ under a general continuous control.

**Why it's hard.** In Layer 2, the product structure $\omega_1(s,u)^\alpha \cdot \omega_2(u,t)^\beta$ is what makes the refinement cost bound factorable. Right-peeling keeps the left endpoint fixed at $a$, so the $\omega_1(a, q_j)^\alpha$ terms are monotone and factor out; the remaining $\omega_2(q_j, q_{j+1})^\beta$ terms collapse via super-additivity. The product *separates* the two roles.

In Layer 3, the single control $\omega(s,t)^\theta$ does not decompose this way. Super-additivity gives

$$\omega(s,u) + \omega(u,t) \;\leq\; \omega(s,t),$$

but this is an *additive* bound on a quantity raised to the $\theta$-th power. For $\theta > 1$, the inequality $(a + b)^\theta \geq a^\theta + b^\theta$ goes the wrong direction — summing $\omega$-values before raising to $\theta$ gives a *larger* bound, not a smaller one. This is the precise point where the Layer 2 strategy breaks down.

**What's needed.** Either:
1. A **compactness-based argument** (as in Friz–Hairer), using sequential compactness of partition sequences with bounded point count, or
2. A proof that **uniqueness plus dyadic additivity implies full additivity** via continuity of the sewn map — the idea being that dyadic rationals are dense in $[s,t]$, and $I(s,\cdot)$ is continuous (which follows from the approximation bound and continuity of $\Xi$).

See `TODO.lean` for the precise statement and further discussion.

**What's available without it.** Everything *except* general additivity is proved sorry-free. The sewn map exists, satisfies the approximation bound, is unique among additive maps with the bound, and is additive over all dyadic partitions. For applications requiring full additivity, Layer 2 provides it for all Lipschitz-control settings — which covers the standard stochastic processes.

## File structure

```
SewingLemma/
├── Defs.lean                         -- Definitions for all three layers
├── Condition.lean                    -- Layer 1 dyadic machinery, cocycle identity
├── LayerOne/
│   └── Map.lean                      -- Layer 1 sewn map and properties
├── LayerTwo/
│   ├── ContinuousControl.lean        -- ContControl monotonicity, partition sums
│   ├── RightPe.lean                  -- Right-peeling telescoping identity
│   ├── Decay.lean                    -- Layer 2 geometric decay
│   ├── ThetaEnergy.lean              -- θ-energy estimates, refinement monotonicity
│   ├── RefiCo.lean                   -- Refinement cost bound
│   └── Map/
│       ├── Unique.lean               -- Cauchy, approximation, uniqueness
│       ├── Merge.lean                -- Common refinement (partition merge)
│       ├── Partition.lean            -- Splitting, mesh bounds, two-point partition
│       ├── Additive.lean             -- General additivity
│       └── GenConv.lean              -- General convergence (mesh → 0)
├── LayerThree/
│   ├── DyadicPartition.lean          -- Dyadic bounds and Cauchy sequence
│   └── Map.lean                      -- Layer 3 sewn map and properties
└── TODO.lean                         -- Layer 3 general additivity (see inside)
```

## Dependencies

Built on [Mathlib](https://github.com/leanprover-community/mathlib4). Key imports include `Analysis.Normed.Group.Basic`, `Analysis.SpecialFunctions.Pow.Real`, `Topology.UniformSpace.Cauchy`, and `Topology.Algebra.InfiniteSum.Basic`.

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Theorem 2.2
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010)
* Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob