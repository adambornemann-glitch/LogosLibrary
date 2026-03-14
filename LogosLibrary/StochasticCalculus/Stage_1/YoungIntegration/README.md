# Young Integration

## Overview

This directory constructs the **Young integral** $\int_s^t Y\, dX$ for paths $X, Y$ of complementary Hölder regularity: $X$ is $\gamma$-Hölder and $Y$ is $\delta$-Hölder with

$$\frac{1}{p} + \frac{1}{q} > 1 \qquad \text{i.e.} \qquad \gamma + \delta > 1.$$

This is the first non-trivial application of the Layer 2 sewing lemma (Stage 0) and the base case of the rough path integration hierarchy. It extends classical Riemann–Stieltjes integration beyond bounded variation, reaching paths as rough as — but not including — Brownian motion.

Everything is built on a single idea: define the left-point Riemann sum approximation $\Xi(s,t) = (X(t) - X(s)) \cdot Y(s)$, show its defect factorises into a product of independent increments, and feed the result to the sewing machine. Existence, uniqueness, additivity, regularity, linearity, and integration by parts then follow — most of them as one-liners delegating to Stage 0.

## Mathematical content

### The approximation map

The starting point is the left-point Riemann sum approximation:

$$\Xi(s, t) \;=\; (X(t) - X(s)) \cdot Y(s)$$

This is the simplest possible guess for $\int_s^t Y\, dX$: evaluate the integrand at the left endpoint, multiply by the increment of the integrator. The entire theory is about understanding how good this guess is.

### The defect identity

The defect $\delta\Xi(s, u, t) := \Xi(s,t) - \Xi(s,u) - \Xi(u,t)$ measures the failure of $\Xi$ to be additive. A direct computation gives:

$$\delta\Xi(s, u, t) \;=\; (X(u) - X(t)) \cdot (Y(u) - Y(s))$$

This factorisation is the algebraic heart of Young integration. The defect splits into an integrator increment on $[u, t]$ and an integrand increment on $[s, u]$ — two independent quantities with different regularity. This **cross structure** is precisely what the Layer 2 sewing lemma is designed to exploit.

### The Hölder defect bound

When $X$ is $\gamma$-Hölder with constant $C_X$ and $Y$ is $\delta$-Hölder with constant $C_Y$:

$$\|\delta\Xi(s, u, t)\| \;\leq\; C_X \cdot C_Y \cdot |t - u|^{\gamma} \cdot |u - s|^{\delta}$$

The exponents satisfy $\gamma + \delta > 1$, which is the super-linear decay that makes the sewing lemma converge.

### The Young integral

The integral is defined as the output of the Layer 2 sewing machine:

$$\int_s^t Y\, dX \;:=\; \texttt{sewingMap}_2\;\Xi\;\omega_1\;\omega_2\;\delta\;\gamma\;(C_X \cdot C_Y)\;\cdots$$

with controls $\omega_1(s,t) = \omega_2(s,t) = |t - s|$ and exponents $\alpha = \delta$, $\beta = \gamma$.

### The Young–Loève estimate

The approximation error is controlled at order $\gamma + \delta$:

$$\left\|\int_s^t Y\, dX \;-\; (X(t) - X(s)) \cdot Y(s)\right\| \;\leq\; C_{\gamma,\delta} \cdot C_X \cdot C_Y \cdot |t - s|^{\gamma + \delta}$$

where $C_{\gamma,\delta}$ is the sewing constant. Since $\gamma + \delta > 1$, this is super-linear — the approximation is better than what additivity alone would give. This estimate is the workhorse of everything that follows.

### Uniqueness

Any additive functional $J(s,t)$ satisfying a super-linear approximation bound

$$\|J(s,t) - (X(t) - X(s)) \cdot Y(s)\| \;\leq\; M \cdot |t - s|^{\theta}, \qquad \theta > 1$$

must equal the Young integral. The proof telescopes $J$ over dyadic partitions and shows the Riemann sums converge geometrically with ratio $2^{-(\theta - 1)}$.

This is the *key structural principle*: the Young integral is the **unique** additive extension of the left-point approximation. Every subsequent result — linearity, integration by parts — is proved by exhibiting a candidate, checking it's additive with the right approximation bound, and invoking uniqueness.

### Regularity of the indefinite integral

The indefinite integral $t \mapsto \int_a^t Y\, dX$ is $\gamma$-Hölder:

$$\left\|\int_s^t Y\, dX\right\| \;\leq\; \left(C_X \cdot \|Y\|_\infty \;+\; C_{\gamma,\delta} \cdot C_X \cdot C_Y \cdot (b - a)^{\delta}\right) \cdot |t - s|^{\gamma}$$

The integral inherits the regularity of the **integrator** $X$, not the integrand $Y$. This is essential for iteration: in the Picard scheme for rough ODEs, the output path must live in the same Hölder class as the driving signal.

### Linearity

Both linearity results follow from uniqueness:

$$\int_s^t (c \cdot Y)\, dX \;=\; c \cdot \int_s^t Y\, dX$$

$$\int_s^t Y\, d(X_1 + X_2) \;=\; \int_s^t Y\, dX_1 \;+\; \int_s^t Y\, dX_2$$

In each case, the candidate is visibly additive, and the Young–Loève estimate on the components gives the required super-linear approximation bound.

### Integration by parts

For scalar-valued paths:

$$\int_s^t Y\, dX \;+\; \int_s^t X\, dY \;=\; X(t) Y(t) - X(s) Y(s)$$

The proof defines $J(s,t) = X(t)Y(t) - X(s)Y(s) - \int_s^t Y\, dX$, verifies it is additive and approximates the Riemann sum for $\int X\, dY$ to order $|t - s|^{\gamma + \delta}$, and concludes by uniqueness. The cross term $(X(t) - X(s))(Y(t) - Y(s))$ contributes at order $\gamma + \delta > 1$, which is absorbed into the constant.

### Continuity estimate

The difference of two Young integrals satisfies:

$$\left\|\int Y_1\, dX_1 - \int Y_2\, dX_2\right\| \;\leq\; \left(C_{\Delta X} \cdot \|Y_1\|_\infty + C_{X_2} \cdot \|Y_1 - Y_2\|_\infty + C_{\text{sew}} \cdot (b-a)^{\delta}\right) \cdot |t - s|^{\gamma}$$

The proof decomposes the difference as $(I_1 - \Xi_1) - (I_2 - \Xi_2) + (\Xi_1 - \Xi_2)$, bounds the first two brackets by Young–Loève, and splits the third into $\Delta X \cdot Y_1 + X_2 \cdot \Delta Y$.

## File structure

### `PVarCont.lean` — Hölder regularity and control functions

Defines `IsHolderOn` (the Hölder continuity structure) and builds the bridge to the sewing lemma's control-function machinery. The Hölder control $\omega(s,t) = C^p \cdot |t - s|^{\gamma p}$ is shown to be super-additive and Lipschitz on bounded intervals, yielding a `LipControl` instance. Also proves that Hölder increments are bounded by the control: $\|X(t) - X(s)\|^p \leq \omega(s,t)$.

| Declaration | Role |
|---|---|
| `IsHolderOn` | Structure: gamma-Hölder continuity with constant C on [a, b] |
| `holderControl` | The control function C^p * \|t - s\|^(gamma * p) |
| `holderControl_nonneg` | Non-negativity |
| `holderControl_diag` | Vanishes on the diagonal |
| `holderControl_superadd` | Super-additivity for gamma * p >= 1 |
| `holderControl_lip` | Lipschitz bound on bounded intervals |
| `holderControl_lipControl` | Packages everything as a `LipControl` |
| `holder_increment_le` | Increment bound: norm^p <= control |

### `Defect.lean` — The algebraic core

Contains the approximation map, the defect identity, and the verification of `SewingCondition₂`. This is where the algebra happens — everything after this file is a consequence of the sewing lemma. Provides both a **scalar version** (integrator in $\mathbb{R}$) and a **bilinear version** (integrator in a Banach space $F$, with a continuous bilinear pairing $\sigma$).

| Declaration | Role |
|---|---|
| `youngApprox` | Scalar approximation: (X(t) - X(s)) * Y(s) |
| `youngApprox_diag` | Vanishes on the diagonal |
| `youngApprox_defect` | Defect identity: (X(u) - X(t)) * (Y(u) - Y(s)) |
| `youngApprox_defect_norm` | Exact norm of the defect (scalar case) |
| `youngApprox_defect_holder_bound` | Hölder defect bound (cross structure) |
| `youngApprox_sewingCondition₂` | Full verification of `SewingCondition₂` |
| `youngApproxBilin` | Bilinear approximation: sigma(Y(s), X(t) - X(s)) |
| `youngApproxBilin_defect` | Bilinear defect identity |
| `youngApproxBilin_defect_norm_le` | Bilinear defect norm bound |

### `Integral/Def.lean` — Definition of the Young integral

A thin file: defines `youngIntegral` as the output of `sewingMap₂` applied to `youngApprox` with the absolute-value controls and the `SewingCondition₂` proof from `Defect.lean`.

| Declaration | Role |
|---|---|
| `youngIntegral` | The Young integral on [s, t] |

### `Integral/Properties.lean` — Basic properties

Three results, all one-liners delegating to the sewing infrastructure.

| Declaration | Role |
|---|---|
| `youngIntegral_diag` | Vanishes on the diagonal |
| `youngIntegral_approx` | Young–Loève estimate |
| `youngIntegral_additive` | Additivity (Chasles property) |

### `Integral/Unique.lean` — Uniqueness

The most substantial proof in the directory. Shows that any additive $J$ with a super-linear approximation bound must equal the Young integral, by telescoping $J$ over dyadic partitions and proving geometric convergence of the Riemann sums. The convergence rate is $r = 2^{-(θ - 1)}$ where $\theta > 1$ is the approximation exponent.

| Declaration | Role |
|---|---|
| `youngIntegral_unique` | Uniqueness: additive + super-linear approx => equals Young integral |

### `Integral/Regular.lean` — Regularity

Shows the indefinite integral inherits the Hölder class of the integrator. The increment bound follows from the triangle inequality: split $\|I(s,t)\|$ into the Young–Loève remainder and the approximation term, then absorb $|t - s|^{\delta}$ into the diameter.

| Declaration | Role |
|---|---|
| `youngIntegral_increment_bound` | Hölder-type increment bound on I(s, t) |
| `youngIntegral_pvar_bound` | Indefinite integral is gamma-Hölder (`IsHolderOn`) |

### `Integral/Linear.lean` — Linearity

Both linearity results are proved via uniqueness: exhibit the candidate, verify additivity, and check the approximation bound using Young–Loève on the components. Also contains the auxiliary results `IsHolderOn.smul` and `IsHolderOn.add_real`.

| Declaration | Role |
|---|---|
| `IsHolderOn.smul` | Scalar multiple of Hölder function is Hölder |
| `youngIntegral_smul_integrand` | Linearity in the integrand |
| `IsHolderOn.add_real` | Sum of Hölder functions is Hölder |
| `youngIntegral_add_integrator` | Linearity in the integrator |

### `Integral/ByParts.lean` — Integration by parts

The classical product rule for Young integrals. The proof is a single application of uniqueness: $J(s,t) = X(t)Y(t) - X(s)Y(s) - \int_s^t Y\, dX$ is additive and approximates $\int X\, dY$ to order $\gamma + \delta$.

| Declaration | Role |
|---|---|
| `youngIntegral_by_parts` | Integration by parts (scalar case) |

### `Integral/Consistency.lean` — Riemann–Stieltjes compatibility

**Status: deferred** (`sorry`). When the integrator has bounded variation ($\gamma = 1$), the Young integral should agree with the classical Riemann–Stieltjes integral. This requires a bridge to Mathlib's `IntervalIntegral` API, which is a separate project.

| Declaration | Status |
|---|---|
| `youngIntegral_eq_riemannStieltjes` | sorry — awaiting Mathlib bridge |

### `API.lean` — Stage 1 → Stage 2 interface

The bundled API that Stage 2 (rough path integration) imports. Packages the integral and all its properties into a single `YoungIntegralData` structure, plus unbundled convenience theorems, a continuity estimate for the difference of two Young integrals, and composition with Lipschitz functions.

| Declaration | Role |
|---|---|
| `YoungIntegralData` | Bundled structure: val, diag, additive, approx, unique, increment_bound |
| `young_integral` | Main constructor: IsHolderOn hypotheses in, YoungIntegralData out |
| `young_integral_approx` | Unbundled Young–Loève estimate |
| `young_integral_additive` | Unbundled additivity |
| `young_integral_holder'` | Indefinite integral is gamma-Hölder (unbundled) |
| `young_integral_continuity_estimate` | Continuity in (X, Y) with explicit constants |
| `isHolderOn_comp_lipschitz` | Lipschitz composition preserves Hölder regularity |
| `young_integral_comp_lipschitz` | Young integral of f(Y) for Lipschitz f |


## The key design insight

Every result after `Properties.lean` is proved by the **same method**: exhibit a candidate functional, verify it is additive with a super-linear approximation bound, and invoke `youngIntegral_unique`. This is not a coincidence — it is the algebraic structure of the theory. The Young integral is **characterised** by being the unique additive extension of the left-point Riemann sum, and this characterisation is the correct tool for proving everything about it.

This pattern will repeat at Stage 2 (rough integration) and Stage 3 (controlled rough paths), each time one level up in the regularity hierarchy.

## Dependencies

### From Stage 0

| What | Used for |
|---|---|
| `SewingCondition₂`, `sewingMap₂` | Defining the Young integral |
| `sewingMap₂_additive` | Additivity |
| `sewingMap₂_dist_le` | Young–Loève estimate |
| `sewingConst₂`, `sewingConst₂_pos` | Explicit constants |
| `dyadicSum₁`, `dyadicPt` | Uniqueness proof (dyadic telescoping) |
| `LipControl` | Control function packaging |

### From Mathlib

| What | Used for |
|---|---|
| `NormedAddCommGroup`, `NormedSpace`, `CompleteSpace` | Banach space structure |
| `ContinuousLinearMap` | Bilinear pairing (bilinear version) |
| `rpow_le_rpow`, `rpow_add'`, etc. | Power function estimates throughout |

## References

- Young, L.C., *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapter 1
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapter 1

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob