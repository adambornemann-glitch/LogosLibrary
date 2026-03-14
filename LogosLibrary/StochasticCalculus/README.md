# Stochastic Calculus

## Overview

A formalization of rough path theory and stochastic calculus in Lean 4, from first principles to the Universal Limit Theorem.

The goal is to construct a complete, formally verified proof that the solution map

$$\mathbf{X} \;\mapsto\; Y^{\mathbf{X}}, \qquad dY = f(Y)\, d\mathbf{X}, \quad Y_0 = a$$

sending a rough path $\mathbf{X}$, a vector field $f$, and an initial condition $a$ to the solution of the rough differential equation is **well-defined and continuous** in the $p$-variation rough path metric. This is the Itô–Lyons map — the central theorem of rough path theory — and it has never been formalized in any proof assistant.

## Architecture

The formalization is organized into five stages, each building on the previous:

### [Stage 0: Foundations](Stage_0/README.md)
The sewing lemma and $p$-variation theory. The sewing lemma constructs additive functionals from almost-additive approximations — it is the integration machine that powers everything downstream. The $p$-variation provides the regularity framework that measures how rough a path is.

**Status**: Substantially complete. Three layers of the sewing lemma (interval-length control, cross-controlled, general continuous control) are formalized, with full additivity proved for Layers 1–2. The $p$-variation module includes the core definition, super-additivity, exponent monotonicity, Hölder regularity, and Brownian motion finite $p$-variation.

### [Stage 1: Young Integration](Stage_1/README.md)
Constructs $\int Y\, dX$ when $X$ has finite $p$-variation and $Y$ has finite $q$-variation with $1/p + 1/q > 1$. The Young integral is defined as the sewn map from Stage 0 — existence, uniqueness, and additivity are immediate consequences of the sewing lemma infrastructure.

**Status**: Planned.

### [Stage 2: The Algebraic Layer](Stage_2/README.md)
The truncated tensor algebra $T^{(2)}(V)$, Chen's identity, group-like elements, and the free step-2 nilpotent group. This is the algebraic framework that houses the "area" data of a rough path. Largely independent of Stage 1 and can be developed in parallel.

**Status**: Planned.

### [Stage 3: The Space of Rough Paths](Stage_3/README.md)
Merges the analytical infrastructure (Stages 0–1) with the algebraic infrastructure (Stage 2) to define the space of $p$-rough paths, equip it with a $p$-variation metric, and prove completeness. This is where the two streams of development meet, producing the `RoughPath` structure that Stage 4 consumes.

**Status**: Planned.

### [Stage 4: The Itô–Lyons Map](Stage_4/README.md)
Controlled paths, the rough integral, the Picard fixed-point argument for rough differential equations, and the Universal Limit Theorem. This is the summit: every previous stage feeds into it, and the ULT is the payoff theorem that justifies the entire programme.

**Status**: Planned.

## The big picture

Classical stochastic calculus constructs integrals using probability — martingale theory, filtrations, conditional expectations. The resulting integral depends on the probabilistic structure of the noise, which is why different approximation schemes (Itô vs. Stratonovich) produce different limits.

Rough path theory takes a different approach: enhance the driving signal with sufficient algebraic data (the iterated integrals / "area"), and the integral becomes a **continuous function of the enhanced path**. Probability enters only at the very end, in identifying which enhancement a particular stochastic process selects. Everything else — existence, uniqueness, stability, approximation — is deterministic analysis.

The dependency flow:

```
Stage 0 ─── sewing lemma + p-variation
  │
  ├──→ Stage 1 ─── Young integration
  │                      │
  │                      ├──────────────────┐
  │                      │                  │
  │    Stage 2 ─── tensor algebra           │
  │         │            │                  │
  │         └────────────┤                  │
  │                      ▼                  │
  │              Stage 3 ─── rough paths ◄──┘
  │                      │
  │                      ▼
  └────────────→ Stage 4 ─── Itô–Lyons map + ULT
```


## Dependencies

Built on [Mathlib](https://github.com/leanprover-community/mathlib4). Key areas used include normed spaces and functional analysis, tensor products, metric space completeness, the Banach fixed-point theorem, and Fréchet differentiation.

## References

- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020)
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010)
- Lyons, T.; Caruana, M.; Lévy, T., *Differential Equations Driven by Rough Paths*, Springer LNM **1908** (2007)
- Young, L.C., *An inequality of the Hölder type, connected with Stieltjes integration*, Acta Math. **67** (1936), 251–282
- Chen, K.T., *Integration of paths, geometric invariants and a generalized Baker–Hausdorff formula*, Ann. of Math. **65** (1957), 163–178

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob

