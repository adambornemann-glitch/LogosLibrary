# The Sewing Lemma

## Overview

The **Sewing Lemma** constructs additive functionals from almost-additive approximations. Given a two-parameter map $\Xi : \mathbb{R} \times \mathbb{R} \to E$ (with $E$ a Banach space) whose failure of additivity — the *defect*

$$\delta\Xi(s, u, t) \;=\; \Xi(s, t) - \Xi(s, u) - \Xi(u, t)$$

is controlled by a quantity that decays under refinement, the sewing lemma produces a unique additive functional $I$ approximating $\Xi$.

This is the foundational construction underlying rough path integration, Young integration, and controlled-path theory. It replaces the classical Riemann–Stieltjes limit with a robust algebraic-analytic framework that extends integration to paths of low regularity — precisely the regime needed for stochastic calculus.

The formalization proceeds in three layers of increasing generality. **All three layers are fully proved**, including existence, uniqueness, approximation bounds, and general additivity.

## Mathematical content

### Layer 1: Interval-length control

The defect satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot |t - s|^\theta, \qquad \theta > 1.$$

The interval length distributes perfectly over dyadic subdivision: at level $n$, each sub-interval has length exactly $|t - s| / 2^n$, giving clean geometric decay

$$\|S_{n+1} - S_n\| \;\leq\; K \cdot |t - s|^\theta \cdot 2^{-n(\theta - 1)}$$

with no additional hypotheses on a control function. The condition $\theta > 1$ is sharp — it is precisely what makes the geometric series $\sum 2^{-n(\theta-1)}$ converge.

This version covers all standard Hölder-regularity applications: Brownian motion ($\gamma$-Hölder for $\gamma < 1/2$), fractional Brownian motion ($\gamma$-Hölder for $\gamma < H$), Young integration ($\theta = 1/p + 1/q > 1$), and rough integration with Hölder rough path data.

**Main output.** There exists a unique additive $I$ with

$$\|I(s,t) - \Xi(s,t)\| \;\leq\; \frac{K}{1 - 2^{-(\theta-1)}} \cdot |t - s|^\theta.$$

Full additivity for Layer 1 is obtained by specialization from Layer 2: the two sewn maps are literally the same `limUnder`, so Layer 2's additivity transfers directly.

### Layer 2: Cross-controlled (product) defect bound

The defect satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot \omega_1(s, u)^\alpha \cdot \omega_2(u, t)^\beta, \qquad \alpha + \beta > 1,$$

where each $\omega_i$ is a super-additive control satisfying a Lipschitz-in-length condition $\omega_i(s, t) \leq L_i \cdot (t - s)$.

The product structure is not a mere generalization — it is the *natural* form of the defect in integration theory. When $\Xi(s,t) = Y(s) \cdot (X(t) - X(s))$, the defect

$$\delta\Xi(s, u, t) = -(Y(u) - Y(s)) \cdot (X(t) - X(u))$$

separates into a factor depending on $[s, u]$ (integrand variation) and a factor depending on $[u, t]$ (integrator variation). This separation is what makes the refinement cost bound factorable — right-peeling keeps the left endpoint fixed at $a$, so the $\omega_1(a, q_j)^\alpha$ terms are monotone and factor out; the remaining $\omega_2(q_j, q_{j+1})^\beta$ terms collapse via super-additivity.

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

where $D_n$ is the $n$-th dyadic partition.

#### Proof of general additivity (Layer 3)

General additivity — $I(s,t) = I(s,u) + I(u,t)$ for arbitrary $u \in [s,t]$ — was the last result proved in this module and required substantial new infrastructure. In Layers 1–2, the product structure of the defect bound makes the refinement cost factorable. In Layer 3, the single control $\omega(s,t)^\theta$ does not decompose this way: super-additivity gives $\omega(s,u) + \omega(u,t) \leq \omega(s,t)$, but for $\theta > 1$ the inequality $(a + b)^\theta \geq a^\theta + b^\theta$ goes the wrong direction.

The proof sidesteps this obstruction entirely via a **point-insertion strategy**:

1. **Insert $u$ into each dyadic partition.** Given $D_n$ (the $n$-th dyadic partition of $[s,t]$), find the block $[d_k, d_{k+1}]$ containing $u$ and insert $u$ to form $Q_n = D_n.\text{insertAt}(k, u)$. The Riemann sum changes by exactly one defect: $\text{RS}(D_n) - \text{RS}(Q_n) = \delta\Xi(d_k, u, d_{k+1})$, which vanishes as $n \to \infty$ because $\omega(d_k, d_{k+1}) \to 0$.

2. **Split and compare.** Restrict $Q_n$ at $u$ to obtain $\text{QL}_n$ (a partition of $[s,u]$) and $\text{QR}_n$ (a partition of $[u,t]$). By the Riemann sum splitting identity, $\text{RS}(Q_n) = \text{RS}(\text{QL}_n) + \text{RS}(\text{QR}_n)$.

3. **Show each half converges independently.** Compare $\text{RS}(\text{QL}_n)$ against the independent dyadic partition of $[s,u]$, and $\text{RS}(\text{QR}_n)$ against that of $[u,t]$. The comparison uses the common refinement (merge) and bounds the per-block multiplicity via a **good/bad point decomposition**: most merge points inherit the dyadic spacing $\geq (t-s)/2^n$ ("good"), while at most one inserted point ("bad") can violate it. A pigeonhole argument (`points_in_interval_le`) then bounds the merge gap per block. Both comparison errors are controlled by $\theta$-energies that vanish as $n \to \infty$.

4. **Conclude by uniqueness of limits.** $\text{RS}(Q_n) \to I(s,t)$ from step 1, and $\text{RS}(\text{QL}_n) + \text{RS}(\text{QR}_n) \to I(s,u) + I(u,t)$ from step 3. Since these are the same sequence, $I(s,t) = I(s,u) + I(u,t)$.

This avoids both the compactness argument of Friz–Hairer and any density argument via dyadic rationals, instead giving a direct quantitative comparison at every refinement level.

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
| General additivity (via Layer 2) | `sewingMap₁_additive` | ✓ |

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
| **General additivity** | `sewingMap₃_additive` | ✓ |
| Bundled API | `sewing_lemma₃` | ✓ |

### Cross-layer results
| Result | Theorem | Status |
|---|---|---|
| Layer 1 = Layer 2 (same limit) | `sewingMap₁_eq_sewingMap₂` | ✓ |
| Lipschitz implies continuous control | `contControl_of_lipControl` | ✓ |

### Point insertion infrastructure
| Result | Theorem |
|---|---|
| Insert point into partition block | `Partition.insertAt` |
| Find block containing a point | `Partition.findBlock` |
| Insertion changes RS by one defect | `riemannSum_insertAt` |
| Insertion defect vanishes | `insertion_defect_tendsto` |
| Inserted RS → sewn map | `riemannSum_insertAt_tendsto` |
| Restrict partition at known index (left) | `Partition.restrictLeftAt` |
| Restrict partition at known index (right) | `Partition.restrictRightAt` |
| Split RS at known index | `riemannSum_splitAt` |

### Merge-gap and comparison infrastructure
| Result | Theorem |
|---|---|
| Pigeonhole counting in intervals | `points_in_interval_le` |
| Merge gap (uniform spacing) | `merge_gap_of_min_spacing` |
| Merge gap (with bad points) | `refinement_gap_with_exceptions` |
| Monotone-embedding wrappers | `merge_gap_of_min_spacing_mono` |
| Per-block defect bound (Layer 3) | `block_bound₃` |
| Refinement cost (Layer 3) | `riemannSum_refinement_bound₃` |
| Max ω vanishes with mesh | `maxOmega_tendsto_zero` |
| Left half comparison (per-$n$) | `left_comparison_bound` |
| Left half comparison (limit) | `left_comparison_tendsto` |
| Right half comparison (per-$n$) | `right_comparison_bound` |
| Right half comparison (limit) | `right_comparison_tendsto` |
| Triangle via common refinement | `riemannSum_comparison_bound` |

### Supporting partition infrastructure
| Result | Theorem |
|---|---|
| Partition merge (common refinement) | `Partition.merge` |
| Merge refines both inputs | `merge_refines_left/right` |
| Merge points strictly monotone | `merge_pts_strict_mono` |
| Mesh decreases under refinement | `mesh_refinement_le` |
| Riemann sum splitting at a point | `riemannSum_split` |
| Super-additivity over partitions | `ContControl.sum_le` |
| Per-block multiplicity bound | `merge_block_mult` |
| Dyadic min spacing | `dyadicPartition_min_spacing` |

## File structure

```
SewingLemma/
├── Defs.lean                             -- Definitions for all three layers
├── Condition.lean                        -- Layer 1 dyadic machinery, cocycle identity
├── LayerOne/
│   └── Map.lean                          -- Layer 1 sewn map, properties, full additivity
├── LayerTwo/
│   ├── ContinuousControl.lean            -- ContControl monotonicity, partition sums
│   ├── RightPe.lean                      -- Right-peeling telescoping identity
│   ├── Decay.lean                        -- Layer 2 geometric decay
│   ├── ThetaEnergy.lean                  -- θ-energy estimates, refinement monotonicity
│   ├── RefiCo.lean                       -- Refinement cost bound (Layer 2)
│   └── Map/
│       ├── Unique.lean                   -- Cauchy, approximation, uniqueness
│       ├── Merge.lean                    -- Common refinement (partition merge)
│       ├── Partition.lean                -- Splitting, mesh bounds, two-point partition
│       ├── Additive.lean                 -- General additivity (Layer 2)
│       ├── GenConv.lean                  -- General convergence (mesh → 0)
│       └── Specialize.lean              -- Layer 1 = Layer 2 bridge
├── LayerThree/
│   ├── DyadicPartition.lean              -- Dyadic bounds and Cauchy sequence (Layer 3)
│   ├── RefiCo.lean                       -- Block bound, refinement cost (Layer 3)
│   ├── Insert.lean                       -- Partition.insertAt, findBlock, RS identity
│   ├── MinSpacing.lean                   -- Pigeonhole: points_in_interval_le
│   ├── MergeGap.lean                     -- Refinement gap with good/bad decomposition
│   └── Map/
│       ├── Unique.lean                   -- Cauchy, approximation, uniqueness (Layer 3)
│       ├── MultiBlock.lean               -- insertAt convergence, merge multiplicity
│       ├── Wrappers.lean                 -- Monotone-embedding wrappers
│       ├── LeftComp.lean                 -- Left half comparison lemma
│       ├── RightComp.lean                -- Right half comparison lemma
│       └── Additive.lean                 -- General additivity (Layer 3)
```

## Build status

All files compile without warnings or sorries.

## References

* Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
* Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Theorem 2.2
* Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010)
* Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
