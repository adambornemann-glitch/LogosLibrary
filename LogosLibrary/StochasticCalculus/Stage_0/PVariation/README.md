# $p$-Variation of Paths

## Overview

The **$p$-variation** of a function $f$ on a set $s$ is the supremum

$$\|f\|_{p\text{-var};\, s}^p \;=\; \sup_{\mathcal{P}} \sum_{i} d\bigl(f(t_{i+1}),\, f(t_i)\bigr)^p$$

over all finite partitions $\mathcal{P}$ of $s$. This generalizes the classical total variation (the case $p = 1$) to a family of regularity measures indexed by a real exponent $p > 0$.

The $p$-variation is the fundamental regularity notion in rough path theory. A path has finite $p$-variation when the supremum above is finite. The key dichotomy for standard Brownian motion: it has finite $p$-variation almost surely for all $p > 2$, and infinite $p$-variation for $p \leq 2$. This is the analytical reason that classical Riemann–Stieltjes integration fails for Brownian paths and that Itô calculus (or more generally, rough path theory) is necessary.

## Relationship to the Sewing Lemma

The $p$-variation provides the *regularity framework* that feeds into the sewing lemma's *integration machine*:

- If $X$ is $\gamma$-Hölder, then $X$ has finite $p$-variation for $p = 1/\gamma$. The control $\omega(s,t) = \|X\|_{p\text{-var};\,[s,t]}^p$ is super-additive and continuous, satisfying the hypotheses of the sewing lemma.

- **Young integration**: if $X$ has finite $p$-variation and $Y$ has finite $q$-variation with $1/p + 1/q > 1$, then $\Xi(s,t) = Y(s) \cdot (X(t) - X(s))$ satisfies a Layer 2 sewing condition with $\alpha = 1/q$, $\beta = 1/p$, and the sewn map is the Young integral $\int Y\, dX$.

- **Rough integration**: for rougher paths ($p \geq 2$), the $p$-variation controls the size of the iterated integrals in the rough path lift, and the sewing lemma constructs the integral against the enhanced path.

## Design decisions

**Following Mathlib conventions.** The definition uses the supremum over all monotone $\mathbb{N}$-indexed sequences with values in $s$, paired with a natural number $n$ giving the number of intervals. This matches Mathlib's `eVariationOn` and avoids introducing a separate partition type. The agreement is verified: `ePVariationOn 1 f s = eVariationOn f s`.

**Extended nonneg reals.** The $p$-variation is valued in $\mathbb{R}_{\geq 0}^\infty$ (`ℝ≥0∞`), following Mathlib's `eVariationOn`. This avoids case splits on finiteness in monotonicity and super-additivity results.

**Real exponent.** The exponent $p$ is taken as $\mathbb{R}$ (rather than $\mathbb{R}_{>0}$ or $\mathbb{N}$) to interface cleanly with `ENNReal.rpow`. Most results require `0 < p` or `1 ≤ p`.

## Main definitions

- `ePVariationOn p f s` — the $p$-variation of $f$ on the set $s$, valued in $\mathbb{R}_{\geq 0}^\infty$
- `HasFinitePVariationOn p f s` — predicate asserting $\|f\|_{p\text{-var};\, s}^p < \infty$
- `pVarNorm p f s` — the $p$-variation norm $\bigl(\text{ePVariationOn}\; p\; f\; s\bigr)^{1/p}$
- `HasContinuousPVariationOn p f a b` — continuity of $t \mapsto \|f\|_{p\text{-var};\,[a,t]}^p$ on $[a,b]$
- `IsControl ω` — a super-additive control function vanishing on the diagonal
- `HasFinitePVariationAE p X a b μ` — finite $p$-variation almost surely for stochastic processes

## Main results

### Core properties
| Result | Theorem | Status |
|---|---|---|
| Constant has zero p-variation | `ePVariationOn_const` | ✓ |
| Monotone in set inclusion | `ePVariationOn_mono_set` | ✓ |
| Empty set and singleton | `ePVariationOn_empty`, `ePVariationOn_singleton` | ✓ |
| Agrees with Mathlib at p = 1 | `ePVariationOn_one_eq_eVariationOn` | ✓ |
| Lower bound from any partition | `le_ePVariationOn` | ✓ |

### Structural properties
| Result | Theorem | Status |
|---|---|---|
| Super-additivity over concatenation | `ePVariationOn_add_le` | ✓ |
| Iterated super-additivity | `ePVariationOn_sum_le` | ✓ |
| p-variation is a control function | `isControl_ePVariationOn` | ✓ |

### Exponent monotonicity
| Result | Theorem | Status |
|---|---|---|
| q-variation bounded by p-variation | `ePVariationOn_le_mul_of_le_exponent` | ✓ |
| Finite p-var implies finite q-var | `HasFinitePVariationOn.of_le_exponent` | ✓ |

### Hölder continuity
| Result | Theorem | Status |
|---|---|---|
| γ-Hölder implies finite (1/γ)-variation | `hasFinitePVariationOn_of_holder` | ✓ |

### Stochastic processes
| Result | Theorem | Status |
|---|---|---|
| Brownian motion: finite p-var a.s. for p > 2 | `brownianMotion_hasFinitePVariationAE` | ✓ |

### Continuity of p-variation
| Result | Theorem | Status |
|---|---|---|
| p-variation on small intervals tends to zero | `ePVariationOn_Icc_tendsto_zero` | **TODO** |
| Continuous finite p-var implies continuous p-var | `hasContinuousPVariationOn_of_continuous` | **TODO** |

## Open problems

### Continuity of $p$-variation (see `TODO.lean`)

For a continuous function $f$ with finite $p$-variation ($p \geq 1$) on $[a,b]$, the map $t \mapsto \|f\|_{p\text{-var};\,[a,t]}^p$ is continuous. This is Friz–Victoir Proposition 5.3.

The proof decomposes into two steps:

1. **Small-interval vanishing**: $\|f\|_{p\text{-var};\,[s,t]}^p \to 0$ as $|t - s| \to 0$, uniformly for $s, t \in [a,b]$. The argument is by contradiction: if not, extract a sequence of intervals with $|t_n - s_n| \to 0$ but $p$-variation $\geq \delta$. By compactness, pass to a subsequence converging to a common limit point. Greedily extract disjoint sub-intervals; by iterated super-additivity their $p$-variations sum to at most $\|f\|_{p\text{-var};\,[a,b]}^p < \infty$, contradicting infinitely many terms $\geq \delta$.

2. **Left- and right-continuity of the cumulative $p$-variation**: left-continuity follows from monotonicity plus lower semicontinuity (as a supremum of continuous functions). Right-continuity uses the splitting $\|f\|_{p\text{-var};\,[a,t_0+\varepsilon]}^p \leq \|f\|_{p\text{-var};\,[a,t_0]}^p + \Delta(\varepsilon) + \|f\|_{p\text{-var};\,[t_0,t_0+\varepsilon]}^p$ where both correction terms vanish by uniform continuity and step 1.

### Planned extensions

As the module grows, planned additions include:

- $p$-variation norm properties (triangle inequality for $p \geq 1$, quasi-triangle for $p < 1$)
- Reparametrization by $p$-variation (Lipschitz reparametrization theorem)
- Compactness criteria in $p$-variation topology
- Interpolation between Hölder and $p$-variation regularity
- Fractional Brownian motion regularity ($H$-dependent $p$-variation bounds)

## File structure

```
PVariation/
├── Basic.lean        -- Definitions, core properties, Hölder, exponent
│                        monotonicity, BM regularity, control functions
└── TODO.lean         -- Continuous p-variation (commented out, with proof sketches)
```

## References

- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010)
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020)
- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob