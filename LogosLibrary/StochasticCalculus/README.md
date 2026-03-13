# Stochastic Calculus

A Lean 4 formalisation of rough path theory and its analytical foundations, from the sewing lemma through to the Itô–Lyons solution map.

## Overview

Classical stochastic calculus (Itô, Stratonovich) relies on probabilistic machinery — martingales, filtrations, predictability — to define integrals against Brownian motion. Rough path theory, initiated by T.J. Lyons in the 1990s, provides a *deterministic* alternative: the integral $\int Y\,d\mathbf{X}$ is defined pathwise, with no probability required, provided the driving signal $\mathbf{X}$ carries enough regularity data (iterated integrals).

This library formalises the core analytical and algebraic components of this theory in Lean 4, building on Mathlib. The programme is organised in stages, with earlier stages providing the foundations for later ones.

## Current Structure

```
StochasticCalculus/
├── SewingLemma/           # The sewing lemma in four layers (see dedicated README)
│   ├── Defs.lean
│   ├── Condition.lean
│   ├── LayerOne/
│   ├── LayerTwo/
│   ├── LayerThree/
│   ├── LayerFour/         # 🚧 Planned
│   ├── API.lean
│   └── README.md
│
├── PVariation/
│   └── Basic.lean         # p-variation of functions, control functions
│
├── YoungIntegration/      # 🚧 Planned
├── TensorAlgebra/         # 🚧 Planned
├── RoughPath/             # 🚧 Planned
├── ControlledPath/        # 🚧 Planned
└── RDE/                   # 🚧 Planned
```

## Completed Modules

### Sewing Lemma

The analytic engine of the entire theory. Constructs additive functionals from almost-additive approximations, in four layers of increasing generality (interval-length control → cross-controlled → continuous super-additive control → partition net).

See [`SewingLemma/README.md`](SewingLemma/README.md) for full documentation.

**Status:** Layers 1–2 complete. Layer 3 complete modulo one axiom (general additivity). Layer 4 (partition net, discharging the axiom) planned.

### $p$-Variation (`PVariation/Basic.lean`)

The $p$-variation of a function $f$ on a set $s$ generalises total variation ($p = 1$) to the supremum of $\sum_i d(f(t_{i+1}), f(t_i))^p$ over all finite partitions. This is the fundamental regularity notion in rough path theory: standard Brownian motion has finite $p$-variation for $p > 2$ and infinite $p$-variation for $p \leq 2$.

**Definitions:**
- `ePVariationOn p f s` — the $p$-variation valued in $\mathbb{R}_{\geq 0}^\infty$
- `HasFinitePVariationOn p f s` — finiteness predicate
- `pVarNorm p f s` — the $p$-variation norm $(p\text{-var})^{1/p}$
- `IsControl` — super-additive control functions (the bridge to the sewing lemma)

**Main results:**
- Super-additivity of $p$-variation under interval concatenation
- Monotonicity in the exponent: finite $p$-variation implies finite $q$-variation for $q \geq p$
- Hölder continuity implies finite $p$-variation ($\gamma$-Hölder $\Rightarrow$ finite $1/\gamma$-variation)
- Brownian motion has finite $p$-variation a.s. for $p > 2$
- When $p = 1$, `ePVariationOn` agrees with Mathlib's `eVariationOn`

**Status:** Core theory complete. No `sorry`.

---

## Roadmap

The path from the current foundations to the full theory of rough differential equations follows four stages. Stages 1 and 2 can proceed in parallel; Stages 3 and 4 depend on both.

```
Stage 0: Sewing Lemma + p-Variation     ← DONE
        │
        ├──────────────────┐
        ▼                  ▼
Stage 1: Young          Stage 2: Algebra
Integration             (Tensor algebra,
                         Chen's identity)
        │                  │
        └────────┬─────────┘
                 ▼
        Stage 3: Rough Path Space
        (Definition, metric, completeness)
                 │
                 ▼
        Stage 4: Itô–Lyons Map
        (Controlled paths, RDE existence,
         continuity, universal limit)
```

### Stage 1: Young Integration (`YoungIntegration/`)

Young integration defines $\int Y\,dX$ when $X$ has finite $p$-variation and $Y$ has finite $q$-variation with $1/p + 1/q > 1$. This is the sewing lemma applied to $\Xi(s,t) = Y_s \cdot (X_t - X_s)$, whose defect $\delta\Xi(s,u,t) = -(Y_u - Y_s)(X_t - X_u)$ has exactly the cross-controlled product structure of Sewing Layer 2.

**Planned contents:**
- Definition of the Young integral via the sewing lemma
- Consistency with the Riemann–Stieltjes integral for smooth paths
- The Young estimate: $p$-variation bound on the integral
- Continuity of the map $(X, Y) \mapsto \int Y\,dX$
- Integration by parts

**Dependencies:** Sewing Lemma (Layer 2), $p$-variation.

### Stage 2: The Algebraic Layer (`TensorAlgebra/`)

When $p \geq 2$, the path $X$ alone does not determine integrals — one needs "higher-order" data encoding iterated integrals. This data lives in the truncated tensor algebra, and the consistency conditions it must satisfy are algebraic.

For $p \in [2,3)$ (covering Brownian motion), the truncated tensor algebra of step 2 is $T^{(2)}(V) = \mathbb{R} \oplus V \oplus (V \otimes V)$, with elements $(1, x, \mathbb{x})$. The group-like elements satisfying $\mathrm{Sym}(\mathbb{x}) = \frac{1}{2} x \otimes x$ form the free nilpotent group $G^{(2)}(V)$.

**Planned contents:**
- The truncated tensor algebra $T^{(N)}(V)$ as a normed algebra (initially $N = 2$)
- Truncated multiplication, submultiplicative norm, inverse via Neumann series
- The free nilpotent group $G^{(N)}(V)$ and its Lie algebra
- Chen's identity for the signature of smooth paths
- The shuffle product and its relationship to group-like elements
- The Baker–Campbell–Hausdorff formula (truncated)

**Dependencies:** Mathlib's `TensorProduct`, `TensorAlgebra`. The key gap is the *normed* truncated tensor product with submultiplicative estimates.

**Design note:** An initial formalisation targeting $N = 2$ (the concrete case $\mathbb{R} \times V \times (V \otimes V)$) is recommended. The structural arguments generalise to arbitrary $N$ with primarily notational overhead, but the normed algebra and estimate infrastructure is best debugged in the concrete setting first.

### Stage 3: The Rough Path Space (`RoughPath/`)

A $p$-rough path over $V$ (for $p \in [2,3)$) is a pair $\mathbf{X} = (X, \mathbb{X})$ satisfying Chen's identity and graded $p$-variation regularity: $X$ has finite $p$-variation and $\mathbb{X}$ has finite $p/2$-variation.

**Planned contents:**
- The `RoughPath` structure: $(X, \mathbb{X})$ with Chen's identity and regularity bounds
- The `GeometricRoughPath` subtype: adding the shuffle/symmetry constraint
- The homogeneous $p$-variation metric on rough paths
- Completeness of the rough path space
- The signature of a smooth path as a geometric rough path
- The Lyons–Victoir extension theorem (existence of rough path lifts)

**Dependencies:** Stage 2 (truncated tensor algebra, Chen's identity), $p$-variation (for the graded metric).

### Stage 4: The Itô–Lyons Map (`ControlledPath/`, `RDE/`)

The crown jewel: given a rough path $\mathbf{X}$ and a sufficiently regular vector field $f$, the solution $Y$ to $dY_t = f(Y_t)\,d\mathbf{X}_t$ exists, is unique, and depends continuously on $\mathbf{X}$ in the rough path metric. This is the **Universal Limit Theorem**.

**Planned contents:**

*Controlled paths* (`ControlledPath/`):
- The `ControlledPath` structure: $(Y, Y')$ with remainder estimate $\|Y_t - Y_s - Y'_s X_{s,t}\| \leq C \cdot \omega(s,t)^{2/p}$
- Integration of controlled paths against rough paths via the sewing lemma
- Closure of controlled paths under integration (the integral of a controlled path is controlled)
- The Banach space structure on controlled paths

*Rough differential equations* (`RDE/`):
- The Taylor approximation $\Xi(s,t) = f(Y_s) X_{s,t} + Df(Y_s) \mathbb{X}_{s,t}$ and its defect bound
- Local existence and uniqueness via the Banach fixed-point theorem
- Global existence by concatenation
- Continuity of the solution map in the rough path metric
- The universal limit property: smooth ODE solutions converge to the RDE solution when the driving signals converge in the rough path metric

**Dependencies:** Everything — sewing lemma, $p$-variation, Young integration, truncated tensor algebra, rough path space, Mathlib's Banach fixed-point theorem and Fréchet derivatives.

---

## Design Principles

**Deterministic first.** The core theory is entirely deterministic. Stochastic processes (Brownian motion, fractional BM) appear only as *examples* — sources of rough paths satisfying the deterministic hypotheses. The probabilistic content is confined to constructing the rough path lift $\mathbf{B}$ of a Brownian motion $B$; everything downstream is pathwise.

**Parametric in the bilinear structure.** Integration is parametric in a continuous bilinear map $\sigma : F \times V \to W$ rather than assuming scalar or matrix multiplication. This costs nothing at the definition level and avoids re-proving the same estimates for different pairings.

**Graded regularity.** The $p$-variation infrastructure handles non-integer exponents via `Real.rpow` and supports the graded structure of rough paths: level-$k$ components have $p/k$-variation. All exponents are real-valued throughout.

**Layered generality.** Results are proved at the minimal generality needed for each application, then generalised. This means Layer 1 of the sewing lemma (sufficient for Hölder paths) is complete and usable long before the abstract Layer 3 is finalised. Similarly, $N = 2$ truncated tensor algebras will be operational before the general-$N$ theory.

## References

1. T.J. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoamericana **14** (1998), 215–310.
2. T.J. Lyons, Z. Qian, *System Control and Rough Paths*, Oxford University Press, 2002.
3. M. Gubinelli, *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140.
4. P.K. Friz, M. Hairer, *A Course on Rough Paths*, 2nd ed., Springer, 2020.
5. P.K. Friz, N.B. Victoir, *Multidimensional Stochastic Processes as Rough Paths*, Cambridge, 2010.
6. T.J. Lyons, A.D. McLeod, *Signature Methods in Machine Learning*, EMS Surveys Math. Sci., 2025.
7. L.C. Young, *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282.
