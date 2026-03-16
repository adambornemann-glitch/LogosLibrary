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

**Status**: Complete. All three layers of the sewing lemma (interval-length control, cross-controlled, general continuous control) are fully proved, including existence, uniqueness, approximation bounds, and general additivity. Layer 3 additivity uses a direct point-insertion strategy rather than compactness or density arguments. The $p$-variation module includes the core definition, super-additivity, exponent monotonicity, Hölder regularity, Brownian motion finite $p$-variation, and the control function bridge to rough path theory.

### [Stage 1: Young Integration](Stage_1/README.md)
Constructs $\int Y\, dX$ when $X$ is $\gamma$-Hölder and $Y$ is $\delta$-Hölder with $1/p + 1/q > 1$ (equivalently $\gamma + \delta > 1$). The Young integral is defined as the sewn map from Stage 0, and the full theory is developed: the Young–Loève estimate, additivity, uniqueness, $\gamma$-Hölder regularity of the indefinite integral, linearity in both integrand and integrator, integration by parts, continuity in the input paths, and composition with Lipschitz functions.

**Status**: Complete. One `sorry` remains in Riemann–Stieltjes consistency (compatibility with Mathlib's `IntervalIntegral` when $X$ has bounded variation), deferred pending a bridge to Mathlib's interval integral API. All other results are fully proved.

### [Stage 2: Rough Path Integration](Stage_2/README.md)
The complete integration theory for rough paths with $p$-variation regularity in the range $p \in [2,3)$. This module builds four layers: the truncated tensor algebra $T^{(2)}(V)$ and its group-like elements $G^{(2)}(V)$; the definition of $p$-rough paths with Chen's identity and Hölder regularity; the Gubinelli derivative framework for controlled paths; and the rough integral itself, constructed via the Stage 0 sewing lemma. The main results are the closure theorem (the integral of a controlled path is controlled), the Itô–Lyons continuity estimate (the integral depends continuously on both the driving rough path and the integrand), and a bundled API packaging everything Stage 3 needs for the Picard fixed-point argument.

**Status**: Complete. All files compile without warnings or sorries. The tensor product cross-norm is axiomatised via a `NormedTensorSquare` typeclass pending Mathlib's projective tensor norm.

### [Stage 3: Rough Differential Equations](Stage_3/README.md)
Controlled paths, the Picard fixed-point argument for rough differential equations on small intervals, and the patching construction that extends local solutions to a global existence and uniqueness theorem. This is where the closure theorem and contraction estimates from Stage 2 pay off.

**Status**: Planned.

### [Stage 4: The Universal Limit Theorem](Stage_4/README.md)
The Itô–Lyons continuity theorem: the solution map $\mathbf{X} \mapsto Y^{\mathbf{X}}$ is continuous in the $p$-variation rough path metric. This is the summit — every previous stage feeds into it, and the ULT is the payoff theorem that justifies the entire programme.

**Status**: Planned.

## The big picture

Classical stochastic calculus constructs integrals using probability — martingale theory, filtrations, conditional expectations. The resulting integral depends on the probabilistic structure of the noise, which is why different approximation schemes (Itô vs. Stratonovich) produce different limits.

Rough path theory takes a different approach: enhance the driving signal with sufficient algebraic data (the iterated integrals / "area"), and the integral becomes a **continuous function of the enhanced path**. Probability enters only at the very end, in identifying which enhancement a particular stochastic process selects. Everything else — existence, uniqueness, stability, approximation — is deterministic analysis.

The dependency flow:

```
Stage 0 ─── sewing lemma + p-variation
  │
  ├──→ Stage 1 ─── Young integration
  │         │
  │         ├──→ Stage 2 ─── rough path integration
  │         │         │
  └─────────┘         │
                      ▼
              Stage 3 ─── rough differential equations (planned)
                      │
                      ▼
              Stage 4 ─── Universal Limit Theorem (planned)
```

## Dependencies

Built on [Mathlib](https://github.com/leanprover-community/mathlib4). Key areas used include normed spaces and functional analysis, tensor products, metric space completeness, the Banach fixed-point theorem, and Fréchet differentiation.

## Citation

```bibtex
@software{bornemann2026stochastic,
  author = {Bornemann, Adam},
  title = {Rough Path Theory and Stochastic Calculus:
           A Machine-Verified Formalization in Lean 4},
  year = {2026},
  url = {https://gitlab.com/pedagogical/logos_library}
}
```

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
