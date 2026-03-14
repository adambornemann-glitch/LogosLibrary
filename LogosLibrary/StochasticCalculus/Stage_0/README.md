# Stage 0: Foundations of Stochastic Calculus

## Overview

This module provides the analytical foundations for rough path integration and stochastic calculus in Lean 4. It contains two closely related components:

- **The Sewing Lemma** — constructs additive functionals from almost-additive approximations
- **$p$-Variation** — defines and develops the regularity theory for paths of finite $p$-variation

Together, these form the base layer of the rough paths programme: $p$-variation provides the *regularity framework* that measures how rough a path is, while the sewing lemma provides the *integration machine* that constructs integrals against such paths.

## Mathematical context

Classical Riemann–Stieltjes integration requires the integrator to have bounded variation (finite $1$-variation). But the paths of standard stochastic processes — Brownian motion, fractional Brownian motion, solutions of SDEs — have infinite $1$-variation almost surely. They do, however, have finite $p$-variation for suitable $p > 1$: Brownian motion has finite $p$-variation for all $p > 2$.

The sewing lemma replaces the classical Riemann–Stieltjes limit with an algebraic-analytic construction that works in this low-regularity regime. Given a two-parameter map $\Xi(s,t)$ that is "almost additive" — meaning the defect $\delta\Xi(s,u,t) = \Xi(s,t) - \Xi(s,u) - \Xi(u,t)$ is small in a quantifiable sense — the sewing lemma produces a genuinely additive functional $I$ that approximates $\Xi$.

The interplay is direct: if $X$ is $\gamma$-Hölder and $Y$ is $\delta$-Hölder with $\gamma + \delta > 1$, then $\Xi(s,t) = Y(s) \cdot (X(t) - X(s))$ satisfies a sewing condition, and the sewn map $I$ is the Young integral $\int Y \, dX$. This application is proved as `young_integral_holder` in the API.

## Modules

### [SewingLemma/](SewingLemma/)

A three-layer formalization of the sewing lemma with increasing generality:

- **Layer 1** — defect controlled by $K \cdot |t-s|^\theta$, $\theta > 1$. Fully proved, with general additivity obtained via specialization from Layer 2.
- **Layer 2** — defect controlled by $K \cdot \omega\_1(s,u)^\alpha \cdot \omega\_2(u,t)^\beta$, $\alpha + \beta > 1$ with Lipschitz controls. Fully proved, including general additivity and mesh-convergence.
- **Layer 3** — defect controlled by $K \cdot \omega(s,t)^\theta$ with continuous super-additive control. Fully proved except general additivity (see `TODO.lean`).

See [SewingLemma/README.md](SewingLemma/README.md) for detailed documentation.

### [PVariation/](PVariation/)

The $p$-variation of a function $f$ on a set $s$:

$$\|f\|\_{p\text{-var}; s}^p \;=\; \sup\_{\mathcal{P}} \sum\_i d\bigl(f(t\_{i+1}),\, f(t\_i)\bigr)^p$$

where the supremum is over all finite partitions $\mathcal{P}$ of $s$.

**Proved results:**

- Core definition (`ePVariationOn`) as a supremum over monotone $\mathbb{N}$-indexed sequences, following Mathlib's `eVariationOn` convention
- Agreement with Mathlib's `eVariationOn` at $p = 1$ (`ePVariationOn_one_eq_eVariationOn`)
- Super-additivity over interval concatenation (`ePVariationOn_add_le`)
- Monotonicity in the exponent: finite $p$-variation implies finite $q$-variation for $q \geq p$ with bounded diameter (`ePVariationOn_le_mul_of_le_exponent`)
- Hölder continuity implies finite $p$-variation: $\gamma$-Hölder on a bounded set gives finite $1/\gamma$-variation (`hasFinitePVariationOn_of_holder`)
- Brownian motion has finite $p$-variation a.s. for $p > 2$ (`brownianMotion_hasFinitePVariationAE`)
- The $p$-variation defines a control function in the sense of rough path theory (`isControl_ePVariationOn`)

**Open problems (see `TODO.lean`):**

- *Continuity of $p$-variation*: for continuous $f$ with finite $p$-variation ($p \geq 1$), the map $t \mapsto \|f\|\_{p\text{-var}; [a,t]}^p$ is continuous. This is Friz–Victoir Proposition 5.3.

### [API.lean](API.lean)

Bundled convenience theorems wrapping the sewing lemma infrastructure:

- `sewing_lemma₁` — Layer 1 existence, uniqueness, approximation, and additivity (the last via Layer 2)
- `sewing_lemma₂` — Layer 2 existence, uniqueness, approximation, and additivity
- `young_integral_holder` — **Young integration for Hölder paths** as a direct application of Layer 2: given $\gamma$-Hölder $X : \mathbb{R} \to \mathbb{R}$ and $\delta$-Hölder $Y : \mathbb{R} \to E$ with $\gamma + \delta > 1$, there exists a unique additive functional $I$ satisfying

$$\|I(s,t) - (X(t) - X(s)) \cdot Y(s)\| \;\leq\; C \cdot |t - s|^{\gamma + \delta}.$$

This is the first concrete integration result and the bridge to Stage 1 (full Young integration with $p$-variation controls).

## File structure

```
Stage_0/
├── README.md
├── API.lean                          -- Bundled sewing lemma + Young integration
├── SewingLemma/
│   ├── README.md
│   ├── Defs.lean
│   ├── Condition.lean
│   ├── LayerOne/ ...
│   ├── LayerTwo/ ...
│   ├── LayerThree/ ...
│   └── TODO.lean
└── PVariation/
    ├── Basic.lean                    -- Definitions, core properties, Hölder, BM
    └── TODO.lean                     -- Continuous p-variation (open)
```

## Build status

All files compile without warnings or sorries. Open problems are isolated in commented-out `TODO.lean` files with proof sketches and references.

## Dependencies

Built on [Mathlib](https://github.com/leanprover-community/mathlib4). Key imports include `Analysis.BoundedVariation`, `Analysis.Normed.Group.Basic`, `Analysis.SpecialFunctions.Pow.Real`, `Topology.UniformSpace.Cauchy`, and `Topology.Algebra.InfiniteSum.Basic`.

## References

- Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020)
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010)
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Young, L.C., *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
