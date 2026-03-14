# Stage 1: Young Integration

## Overview

Young integration constructs the integral $\int Y \, dX$ when $X$ has finite $p$-variation and $Y$ has finite $q$-variation with

$$\frac{1}{p} + \frac{1}{q} > 1.$$

This is the first non-trivial application of the sewing lemma and the base case of the rough path integration hierarchy. It extends classical Riemann–Stieltjes integration beyond bounded variation — reaching paths as rough as (but not including) Brownian motion.

The construction is direct: define the approximation $\Xi(s,t) = Y(s) \cdot (X(t) - X(s))$, verify that its defect has the cross-controlled product structure required by the Layer 2 sewing lemma, and apply the machine. Existence, uniqueness, additivity, and the approximation bound are then *immediate consequences* of the Stage 0 infrastructure.

## Mathematical content

### The defect identity

The approximation map $\Xi(s,t) = \sigma(Y\_s,\, X\_t - X\_s)$, where $\sigma : F \to V \to W$ is a continuous bilinear map, has defect

$$\delta\Xi(s, u, t) \;=\; -\sigma\bigl(Y\_u - Y\_s,\; X\_t - X\_u\bigr).$$

This is pure algebra — expand and use bilinearity.

### The sewing condition

The defect bound takes the *product form* required by `SewingCondition₂`:

$$\|\delta\Xi(s, u, t)\| \;\leq\; \|\sigma\| \cdot \omega\_Y(s, u)^{1/q} \cdot \omega\_X(u, t)^{1/p}$$

where $\omega\_Y(s,t) = \|Y\|\_{q\text{-var};\,[s,t]}^q$ and $\omega\_X(s,t) = \|X\|\_{p\text{-var};\,[s,t]}^p$ are the $p$-variation controls. The exponents satisfy $\alpha = 1/q$, $\beta = 1/p$, with $\alpha + \beta = 1/q + 1/p > 1$.

### The Young integral

The Young integral *is* the sewn map:

$$\int\_s^t Y \, dX \;:=\; \texttt{sewingMap₂}\;\Xi\;\omega\_Y\;\omega\_X\;\tfrac{1}{q}\;\tfrac{1}{p}\;\cdots$$

Everything else — existence, additivity, the approximation bound — falls out of Stage 0.

### The Young–Loève estimate

$$\left\|\int\_s^t Y\, dX \;-\; \sigma(Y\_s,\, X\_t - X\_s)\right\| \;\leq\; C\_{p,q} \cdot \|\sigma\| \cdot \|Y\|\_{q\text{-var};\,[s,t]} \cdot \|X\|\_{p\text{-var};\,[s,t]}$$

This is a direct corollary of `sewingMap₂_dist_le`.

### Regularity of the integral

The indefinite integral $t \mapsto \int\_0^t Y\, dX$ has finite $p$-variation:

$$\left\|\int Y\, dX\right\|\_{p\text{-var};\,[s,t]} \;\leq\; C \cdot \bigl(\|Y\|\_\infty \cdot \|X\|\_{p\text{-var};\,[s,t]} \;+\; \|Y\|\_{q\text{-var};\,[s,t]} \cdot \|X\|\_{p\text{-var};\,[s,t]}\bigr)$$

This result is *essential* for Stage 4: it shows the rough integral preserves regularity, which is what allows iteration in the Picard fixed-point scheme.

## Planned results

### Phase 1.1: $p$-Variation infrastructure
| Result | Status |
|---|---|
| $p$-variation seminorm via `Partition` | Planned |
| Super-additivity of $\omega\_X = \|X\|\_{p\text{-var}}^p$ | Planned |
| Bridge: `pVarControl_is_contControl` | Planned |
| Hölder paths have finite $p$-variation | **Done** (Stage 0) |
| Lipschitz control from Hölder regularity | Planned |

### Phase 1.2: Existence of the Young integral
| Result | Status |
|---|---|
| Approximation map $\Xi(s,t) = \sigma(Y\_s, X\_t - X\_s)$ | Planned |
| Defect identity (algebraic) | Planned |
| Defect bound (Layer 2 form) | Planned |
| Young integral via `sewingMap₂` | Planned |
| Young–Loève approximation bound | Planned |
| Additivity | **Done** (via `sewingMap₂_additive`) |

### Phase 1.3: Properties of the Young integral
| Result | Status |
|---|---|
| Consistency with Riemann–Stieltjes ($p = 1$) | Planned |
| $p$-variation bound on the indefinite integral | Planned |
| Linearity in integrand and integrator | Planned |
| Continuity of $(X, Y) \mapsto \int Y\, dX$ | Planned |
| Integration by parts | Planned |
| Composition with smooth functions | Planned |

### Phase 1.4: Structural lemmas for later stages
| Result | Status |
|---|---|
| Reparametrization invariance | Planned |
| Restriction and concatenation | Planned |
| Abstract $p$-variation bound for sewn maps | Planned |

## The key insight: why Layer 2 is the right tool

The defect $\delta\Xi(s,u,t) = -\sigma(Y\_u - Y\_s,\, X\_t - X\_u)$ naturally *separates* into a factor depending on $[s,u]$ and a factor depending on $[u,t]$. This is not an accident — it is the algebraic structure of integration itself. The integrand's variation on the left of the split point and the integrator's variation on the right are independent quantities with different regularity.

This product structure is precisely what `SewingCondition₂` captures. Layer 1 (with its single control $|t-s|^\theta$) would work only when both paths have the same Hölder exponent. Layer 2 handles the general case where $X$ and $Y$ have genuinely different regularity — which is the situation in every interesting application.

## Dependencies

### From Stage 0
| What | Used for |
|---|---|
| `SewingCondition₂`, `sewingMap₂` | Defining the Young integral |
| `sewingMap₂_additive` | Additivity of the integral |
| `sewingMap₂_dist_le` | Young–Loève estimate |
| `sewingMap₂_unique` | Linearity, integration by parts |
| `riemannSum_tendsto_sewingMap₂` | Riemann–Stieltjes consistency |
| `LipControl`, `ContControl` | Control function packaging |
| `ePVariationOn`, `isControl_ePVariationOn` | $p$-variation infrastructure |

### From Mathlib
| What | Used for |
|---|---|
| `ContinuousLinearMap`, `ContinuousMultilinearMap` | Bilinear map $\sigma$ |
| `NormedSpace`, `NormedAddCommGroup` | Banach space structure |
| Possibly `IntervalIntegral` | Riemann–Stieltjes consistency |

## Build order

The dependency graph has a clear critical path:

```
Phase 1.1 ─── p-variation seminorm ──→ control function ──→ Lipschitz bound ─┐
                                                                             │
Phase 1.2 ─── Ξ definition ──→ defect identity ──→ defect bound ─────────────┤
                                                                             │
              ┌──────────────────────────────────────────────────────────────┘
              ▼
         existence ──→ approximation bound
              │              │
              ▼              ▼
         additivity    p-var estimate (hardest in Stage 1)
              │              │
              ▼              ▼
         linearity     continuity (second hardest)
              │
              ▼
     integration by parts, RS consistency
```

## References

- Young, L.C., *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapter 1
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapter 1

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
