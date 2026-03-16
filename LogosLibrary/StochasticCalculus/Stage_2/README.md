# Stage 2: Rough Path Integration

## Overview

A rough path is not just a path — it is a path *enhanced* with iterated integral data. This module builds the complete rough integration theory for paths with $p$-variation regularity in the range $p \in [2,3)$, which covers standard Brownian motion.

The module has four layers:

1. **Algebra** — the truncated tensor algebra $T^{(2)}(V)$, group-like elements $G^{(2)}(V)$, and the homogeneous metric
2. **Rough paths** — the definition `RoughPath`, Chen's identity, component-wise Hölder bounds
3. **Controlled paths** — the Gubinelli derivative framework: paths `(Y, Y')` with controlled remainders
4. **The rough integral** — existence, uniqueness, additivity, $\gamma$-Hölder regularity, the closure theorem (integral of controlled = controlled), and the Itô–Lyons continuity estimate

Everything is fully proved. The API is bundled in `RoughIntegralData` for Stage 3 (rough differential equations).

## Mathematical content

### The truncated tensor algebra

An element of $T^{(2)}(V)$ is a triple $(a^0, a^1, a^2)$ with $a^0 \in \mathbb{R}$, $a^1 \in V$, $a^2 \in V \otimes V$, equipped with the truncated tensor product:

$$(a^0, a^1, a^2) \otimes_t (b^0, b^1, b^2) \;=\; \bigl(a^0 b^0,\;\; a^0 b^1 + a^1 b^0,\;\; a^0 b^2 + a^1 \otimes b^1 + a^2 b^0\bigr).$$

This is associative and unital with unit $\mathbf{1} = (1, 0, 0)$. Elements with $a^0 = 1$ are invertible via the two-term Neumann series (truncation kills degree $\geq 3$):

$$(1, a^1, a^2)^{-1} \;=\; (1,\; -a^1,\; a^1 \otimes a^1 - a^2).$$

The sum norm $|a^0| + \|a^1\| + \|a^2\|$ is submultiplicative (`normT_tmul_le`).

### Group-like elements and Chen's identity

An element $(1, x, \mathfrak{x}) \in T^{(2)}(V)$ is **group-like** if its symmetric part satisfies $\text{Sym}(\mathfrak{x}) = \frac{1}{2}(x \otimes x)$. Every group-like element decomposes as

$$\mathfrak{x} \;=\; \tfrac{1}{2}(x \otimes x) + A, \qquad A \in \Lambda^2(V),$$

where $A$ is the **Lévy area**. The group-like elements $G^{(2)}(V)$ form a group under truncated multiplication.

A **rough path** is a two-parameter function

$$\mathbf{X}(s,t) = (1,\, X_{s,t},\, \mathbb{X}_{s,t}) \;\in\; G^{(2)}(V)$$

satisfying **Chen's identity** and **Hölder regularity**:

$$\mathbf{X}(s,t) = \mathbf{X}(s,u) \otimes_t \mathbf{X}(u,t), \qquad \|\mathbf{X}(s,t)\|_{cc} \leq C \cdot |t - s|^\gamma$$

with $\gamma \in (1/3,\, 1/2]$. In components, Chen's identity gives:

$$X_{s,t} = X_{s,u} + X_{u,t}, \qquad \mathbb{X}_{s,t} = \mathbb{X}_{s,u} + X_{s,u} \otimes X_{u,t} + \mathbb{X}_{u,t}.$$

### The homogeneous metric

The homogeneous (quasi-)norm on $G^{(2)}(V)$ is

$$\|g\|_{cc} \;=\; \max\bigl(\|x\|,\; \|\text{Anti}(\mathfrak{x})\|^{1/2}\bigr),$$

where the $1/2$ exponent on the area reflects parabolic scaling. This defines a left-invariant quasi-metric $d(g, h) = \|g^{-1} \cdot h\|_{cc}$.

### Controlled paths and the Gubinelli derivative

A path $Y : [a,b] \to E$ is **controlled** by a rough path $\mathbf{X}$ if there exists a *Gubinelli derivative* $Y' : [a,b] \to L(V, E)$ such that the remainder

$$R^Y_{s,t} \;=\; Y(t) - Y(s) - Y'(s) \cdot X_{s,t}$$

is $2\gamma$-Hölder: $\|R^Y_{s,t}\| \leq C_R \cdot |t - s|^{2\gamma}$. The derivative $Y'$ captures the leading-order response of $Y$ to the driving signal $\mathbf{X}$, and the remainder $R^Y$ is a higher-order correction.

### The rough integral

Given a controlled path $(Y, Y')$ and a rough path $\mathbf{X}$, the **rough approximation** is

$$\Xi(s, t) \;=\; \sigma(Y(s),\, X_{s,t}) + \tau(Y'(s),\, \mathbb{X}_{s,t}),$$

where $\sigma$ pairs path values with increments and $\tau$ pairs Gubinelli derivatives with areas. The defect $\delta\Xi$ has three terms, each of order $|t-s|^{3\gamma}$:

$$\|\delta\Xi(s, u, t)\| \;\leq\; K \cdot |t - s|^{3\gamma}, \qquad 3\gamma > 1.$$

This is `SewingCondition₁` with $\theta = 3\gamma$, so the Stage 0 sewing lemma produces the unique additive functional $\int Y \, d\mathbf{X}$.

### The closure theorem

The deepest result: if $(Y, Y')$ is controlled by $\mathbf{X}$, then the indefinite rough integral $Z(t) = \int_a^t Y \, d\mathbf{X}$ is also controlled by $\mathbf{X}$, with Gubinelli derivative $Z'(s) = \sigma(Y(s), \cdot)$ and $2\gamma$-Hölder remainder. This is what makes Picard iteration close in Stage 3.

### The Itô–Lyons continuity estimate

The rough integral is **jointly continuous** in the driving rough path and the controlled integrand:

$$\left\|\int Y_1 \, d\mathbf{X}_1 - \int Y_2 \, d\mathbf{X}_2\right\| \;\leq\; C \cdot \bigl(D_{\text{path}} + D_{\text{deriv}} + D_{\text{rough}}\bigr) \cdot |t - s|^\gamma$$

where $D_{\text{path}}$, $D_{\text{deriv}}$, and $D_{\text{rough}}$ measure the distances between the paths, their Gubinelli derivatives, and the driving rough paths respectively. This is the result that classical Itô calculus lacks — continuity in the path rather than dependence on the filtration.

## Main results

### Algebra (`Algebra/`)
| Result | Theorem | File |
|---|---|---|
| Truncated multiplication | `tmul` | `TruncTensor2.lean` |
| Associativity | `tmul_assoc` | `TruncTensor2.lean` |
| Inverse (for $a_0 = 1$) | `tmul_tinv`, `tinv_tmul` | `TruncTensor2.lean` |
| Submultiplicative norm | `normT_tmul_le` | `TruncTensor2.lean` |
| Nilpotency ($n^3 = 0$) | `nilp_cube` | `TruncTensor2.lean` |
| Group-like closure (mul) | `GroupLike₂.instGroup` | `GroupLike.lean` |
| Lévy area extraction | `GroupLike₂.area`, `𝕏_eq` | `GroupLike.lean` |
| Homogeneous norm | `homoNorm` | `HomoNorm.lean` |
| Quasi-triangle inequality | `homoNorm_mul_le` | `HomoNorm.lean` |
| Component extraction | `norm_x_le_homoNorm`, `norm_area_le_homoNorm_sq` | `HomoNorm.lean` |

### Rough paths (`RoughPath/`)
| Result | Theorem | File |
|---|---|---|
| Level-1 Chen (additivity) | `x_additive` | `Defs.lean` |
| Level-2 Chen (area rule) | `area_full_chen`, `area_chen` | `Defs.lean` |
| Level-1 Hölder | `x_holder` | `Defs.lean` |
| Level-2 Hölder ($2\gamma$-order) | `area_holder`, `area_full_holder` | `Defs.lean` |
| Diagonal = identity | `x_diag`, `area_full_diag` | `Defs.lean` |
| Three-gamma condition | `three_gamma_gt_one` | `Defs.lean` |
| Underlying path | `underlyingPath_holder` | `Defs.lean` |
| Restriction to sub-intervals | `RoughPath.restrict` | `Defs.lean` |
| Trivial rough path | `RoughPath.trivial` | `Defs.lean` |

### Controlled paths (`Controlled/`)
| Result | Theorem | File |
|---|---|---|
| Controlled path structure | `ControlledPath` | `Defs.lean` |
| Remainder bound ($2\gamma$-Hölder) | `R_bound` | `Defs.lean` |
| Derivative Hölder bound | `Y'_holder` | `Defs.lean` |
| Path Hölder bound | `Y_holder` | `Defs.lean` |

### Rough integral (`Integral/`)
| Result | Theorem | File |
|---|---|---|
| Approximation map & defect | `roughApproxMap`, `roughDefect_bound` | `Defect.lean` |
| Sewing condition ($3\gamma > 1$) | `roughApprox_sewingCondition₁` | `Defect.lean` |
| Rough integral definition | `roughIntegral` | `Def.lean` |
| Vanishes on diagonal | `roughIntegral_diag` | `Def.lean` |
| Approximation estimate ($3\gamma$) | `roughIntegral_approx` | `Def.lean` |
| Uniqueness | `roughIntegral_unique` | `Def.lean` |
| **Additivity** | `roughIntegral_additive` | `Additive.lean` |
| **$\gamma$-Hölder bound** | `roughIntegral_increment_bound` | `Properties.lean` |
| **Closure** (controlled output) | `roughIntegral_controlled` | `Properties.lean` |
| **Itô–Lyons continuity** | `roughIntegral_continuity_estimate` | `ItoLyons.lean` |
| Bundled API | `RoughIntegralData`, `rough_integral` | `API.lean` |

### Axioms (`Axioms/`)
| Result | File |
|---|---|
| `NormedTensorSquare` typeclass (cross-norm) | `NormedTensorSquare.lean` |
| Sym/Anti projections (derived) | `NormedTensorSquare.lean` |

## Design decisions

**Concrete before general.** Everything is defined for $N = 2$ explicitly. The general truncated tensor algebra $T^{(N)}(V)$ is not needed until $p \geq 3$.

**The `NormedTensorSquare` axiom.** Mathlib does not yet equip the algebraic tensor product with the projective tensor norm satisfying $\|v \otimes w\| \leq \|v\| \cdot \|w\|$. We axiomatize a minimal interface (the type `T₂ V`, a bilinear map `tprod` with cross-norm, and an isometric swap). When Mathlib gains the projective norm, this file becomes a single `instance`.

**Geometric rough paths only.** The group-like condition $\text{Sym}(\mathbb{X}) = \frac{1}{2}(x \otimes x)$ is baked into `GroupLike₂`. This restricts to geometric (Stratonovich) rough paths. Non-geometric (Itô) rough paths would use elements of $T^{(2)}(V)$ with $a_0 = 1$ but without the symmetric constraint.

**Hölder regularity.** We use Hölder exponents ($|t-s|^\gamma$) rather than $p$-variation controls. This matches the Stage 0 sewing lemma interface directly and covers all standard examples. The $p$-variation formulation can be added as a generalization.

**Quasi-metric, not metric.** The homogeneous norm defines a quasi-metric (quasi-triangle inequality with constant $C$), not a genuine metric. The Carnot–Carathéodory distance is a genuine metric but requires a compactness argument for no analytical payoff.

## File structure

```
Stage_2/
├── README.md
├── API.lean                              -- Bundled API: RoughIntegralData, rough_integral
├── Axioms/
│   └── NormedTensorSquare.lean           -- Cross-norm axiomatization for V ⊗ V
├── Algebra/
│   ├── TruncTensor2.lean                 -- T⁽²⁾(V): multiplication, inverse, norm
│   ├── GroupLike.lean                    -- G⁽²⁾(V): group-like elements, Lévy area
│   └── HomoNorm.lean                     -- Homogeneous norm and quasi-metric
├── RoughPath/
│   └── Defs.lean                         -- RoughPath structure, Chen's identity, Hölder
├── Controlled/
│   └── Defs.lean                         -- ControlledPath, Gubinelli derivative, estimates
└── Integral/
    ├── Defect.lean                       -- Pairing, approximation map, sewing condition
    ├── Def.lean                          -- Rough integral via sewingMap₁
    ├── Properties.lean                   -- Hölder bound, closure theorem
    ├── Additive.lean                     -- Additivity (via Layer 3 → Layer 1 bridge)
    └── ItoLyons.lean                     -- Itô–Lyons continuity estimate
```

## Build status

All files compile without warnings or sorries.

## What Stage 3 needs

The [API](API.lean) is designed as the import boundary for Stage 3 (rough differential equations). It exports:

| What | Used for |
|---|---|
| `rough_integral` / `RoughIntegralData` | Constructing the Picard map $Y \mapsto \int f(Y) \, d\mathbf{X}$ |
| `rough_integral_closure` | Closure: the Picard map preserves `ControlledPath` |
| `.increment` | $\gamma$-Hölder bound with explicit constants for the contraction |
| `.additive` | Additivity inherited by the RDE solution |
| `rough_integral_continuity` | Itô–Lyons estimate for uniqueness and stability |

The Picard contraction on small intervals requires: (1) closure (the map stays in `ControlledPath`), (2) explicit constants in the Hölder bound ($C_{\text{output}} \leq \lambda \cdot C_{\text{input}}$ for $\lambda < 1$ on a short interval), and (3) the continuity estimate for uniqueness.

## Dependencies

### From [Stage 0](../Stage_0/README.md)
| What | Used for |
|---|---|
| `SewingCondition₁`, `sewingMap₁` | Defining the rough integral |
| `sewingMap₁_additive` (via Layer 2/3) | Additivity |
| `sewingMap₁_dist_le` | Approximation estimate |
| `SewingCondition₃`, `contControl_of_lipControl` | Layer 3 additivity bridge |
| `sewingConst₁` | Explicit constants |

### From [Stage 1](../Stage_1/README.md)
| What | Used for |
|---|---|
| Young integration infrastructure | Remainder term estimates (optional path) |

### From Mathlib
| What | Used for |
|---|---|
| `NormedAddCommGroup`, `NormedSpace`, `CompleteSpace` | Banach space structure |
| `ContinuousLinearMap` | Bilinear pairings $\sigma$, $\tau$ |
| `rpow_le_rpow`, `rpow_add'`, etc. | Power function estimates throughout |

## References

- Chen, K.T., *Integration of paths, geometric invariants and a generalized Baker–Hausdorff formula*, Ann. of Math. **65** (1957), 163–178
- Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapters 2, 4, 8
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapters 7–9, 12
- Reutenauer, C., *Free Lie Algebras*, Oxford (1993)

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
