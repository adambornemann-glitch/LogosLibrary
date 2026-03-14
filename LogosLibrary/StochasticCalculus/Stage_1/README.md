# Stage 1: Young Integration

## Overview

This module constructs the **Young integral** $\int Y\, dX$ for paths of complementary Hölder regularity and develops its full theory: existence, uniqueness, additivity, regularity, linearity, integration by parts, and continuity in the input paths.

Young integration is the first non-trivial application of the [Stage 0](../Stage_0/README.md) sewing lemma and the base case of the rough path integration hierarchy. It extends classical Riemann–Stieltjes integration beyond bounded variation, reaching paths as rough as — but not including — Brownian motion.

## Mathematical context

The Riemann–Stieltjes integral $\int Y\, dX$ exists whenever $X$ has bounded variation, but Brownian motion has infinite variation on every interval. Young (1936) observed that an integral can still be defined when the regularity lost by the integrator is compensated by the integrand: if $X$ is $\gamma$-Hölder and $Y$ is $\delta$-Hölder with

$$\gamma + \delta > 1$$

then $\int_s^t Y\, dX$ exists as the limit of left-point Riemann sums. For Brownian motion ($\gamma$ slightly below $1/2$), this requires $\delta > 1/2$ — the integrand must be at least as regular as the integrator. This is the boundary of what can be achieved without the enhanced path-space structure of rough paths (Stage 2).

The construction is direct. Define the left-point approximation

$$\Xi(s, t) = (X(t) - X(s)) \cdot Y(s)$$

and observe that its defect factorises:

$$\delta\Xi(s, u, t) = (X(u) - X(t)) \cdot (Y(u) - Y(s)).$$

This product structure — an integrator increment on $[u, t]$ times an integrand increment on $[s, u]$ — is precisely what the Layer 2 sewing lemma requires. The Hölder bounds give

$$\|\delta\Xi(s, u, t)\| \leq C_X \cdot C_Y \cdot |t - u|^{\gamma} \cdot |u - s|^{\delta}$$

with $\gamma + \delta > 1$, so the sewing machine converges and produces a unique additive functional: the Young integral.

Everything else — the approximation estimate, regularity, linearity, integration by parts, continuity — follows from this construction, most of it through a single structural principle: the Young integral is **characterised** as the unique additive functional with a super-linear approximation bound, and any candidate satisfying this specification must agree with it.

## Modules

### [YoungIntegration/](YoungIntegration/)

The complete Young integration theory, organised into the algebraic core (defect and sewing condition), the integral construction, and its properties. See [YoungIntegration/README.md](YoungIntegration/README.md) for detailed file-by-file documentation with full mathematical statements.

**Proved results:**

- Approximation map and defect identity, in both scalar and bilinear generality
- Verification of `SewingCondition₂` for Hölder paths
- Existence of the Young integral via `sewingMap₂`
- The Young–Loève estimate: $\left\|\int_s^t Y\, dX - (X(t) - X(s)) \cdot Y(s)\right\| \leq C_{\gamma,\delta} \cdot C_X \cdot C_Y \cdot |t - s|^{\gamma + \delta}$
- Additivity (Chasles property)
- Uniqueness: any additive functional with a super-linear approximation bound equals the Young integral
- Regularity: the indefinite integral $t \mapsto \int_a^t Y\, dX$ is $\gamma$-Hölder
- Linearity in the integrand ($\int c Y\, dX = c \int Y\, dX$) and in the integrator ($\int Y\, d(X_1 + X_2) = \int Y\, dX_1 + \int Y\, dX_2$)
- Integration by parts: $\int_s^t Y\, dX + \int_s^t X\, dY = X(t)Y(t) - X(s)Y(s)$
- Continuity estimate for the difference $\int Y_1\, dX_1 - \int Y_2\, dX_2$
- Composition with Lipschitz functions: $\int (f \circ Y)\, dX$ for Lipschitz $f$
- Bundled API (`YoungIntegralData`) packaging the integral with all properties

**Open problems:**

- *Riemann–Stieltjes consistency*: when $X$ has bounded variation ($\gamma = 1$), the Young integral should agree with the classical Riemann–Stieltjes integral. This requires a bridge to Mathlib's `IntervalIntegral` API. (See `Consistency.lean`.)

## File structure

```
Stage_1/
├── README.md
├── API.lean                              -- Bundled Stage 1 → Stage 2 interface
└── YoungIntegration/
    ├── README.md                         -- Detailed documentation
    ├── PVarCont.lean                     -- IsHolderOn, control functions, Lipschitz bridge
    ├── Defect.lean                       -- Approximation map, defect identity, SewingCondition₂
    └── Integral/
        ├── Def.lean                      -- Young integral definition via sewingMap₂
        ├── Properties.lean               -- Diagonal, Young–Loève estimate, additivity
        ├── Unique.lean                   -- Uniqueness (dyadic telescoping argument)
        ├── Regular.lean                  -- Increment bound, p-variation bound
        ├── Linear.lean                   -- Linearity in integrand and integrator
        ├── ByParts.lean                  -- Integration by parts
        └── Consistency.lean              -- Riemann–Stieltjes compatibility (sorry)
```

## Build status

All files compile without warnings. One `sorry` in `Consistency.lean` (Riemann–Stieltjes compatibility), deferred pending a bridge to Mathlib's interval integral. All other results are fully proved.

## What Stage 2 needs

The [API](API.lean) is designed as the import boundary for Stage 2 (rough path integration). It exports five capabilities:

1. **Young–Loève estimate** — bounds the controlled remainder $R^Y_{s,t} = Y_t - Y_s - Y'_s \cdot X_{s,t}$ in the rough integral's defect.
2. **Additivity** — the rough integral inherits additivity from its Young component.
3. **Uniqueness** — identifies the rough integral by the same method, one level up.
4. **$\gamma$-Hölder bound** — closes the Picard contraction for $dY = f(Y)\, d\mathbf{X}$: the Young integral of a $2\gamma$-Hölder remainder against a $\gamma$-Hölder path produces a $\gamma$-Hölder output, since $2\gamma + \gamma = 3\gamma > 1$ for $\gamma > 1/3$.
5. **Continuity** — an ingredient of the Itô–Lyons continuity theorem at the rough level.

## Dependencies

### From [Stage 0](../Stage_0/README.md)

| What | Used for |
|---|---|
| `SewingCondition₂`, `sewingMap₂` | Defining the Young integral |
| `sewingMap₂_additive`, `sewingMap₂_dist_le` | Additivity and Young–Loève estimate |
| `sewingConst₂`, `sewingConst₂_pos` | Explicit constants |
| `dyadicSum₁`, `dyadicPt` | Uniqueness proof |
| `LipControl` | Control function packaging |

### From Mathlib

| What | Used for |
|---|---|
| `NormedAddCommGroup`, `NormedSpace`, `CompleteSpace` | Banach space structure |
| `ContinuousLinearMap` | Bilinear pairing (bilinear defect version) |
| `rpow_le_rpow`, `rpow_add'`, etc. | Power function estimates throughout |

## References

- Young, L.C., *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapter 1
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapter 1
- Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
