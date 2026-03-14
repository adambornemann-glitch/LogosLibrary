# Stage 2: The Algebraic Layer

## Overview

A rough path is not just a path — it is a path *enhanced* with iterated integral data. This module builds the algebraic framework that houses that data: the truncated tensor algebra $T^{(2)}(V)$, its group-like elements $G^{(2)}(V)$, Chen's identity, and the homogeneous metric.

For paths with $p$-variation regularity in the range $p \in [2,3)$ — which covers standard Brownian motion — the enhancement requires exactly two levels: the path increment $X_{s,t} \in V$ and the "area" $\mathbb{X}_{s,t} \in V \otimes V$. The level-1 data is what you see; the level-2 data is the genuinely new information that rough path theory provides beyond classical analysis.

This module is largely independent of Stage 1 (Young integration) and can be developed in parallel.

## Mathematical content

### The truncated tensor algebra

An element of $T^{(2)}(V)$ is a triple $(a^0, a^1, a^2)$ with $a^0 \in \mathbb{R}$, $a^1 \in V$, $a^2 \in V \otimes V$, equipped with the truncated tensor product:

$$(a^0, a^1, a^2) \otimes_t (b^0, b^1, b^2) \;=\; \bigl(a^0 b^0,\;\; a^0 b^1 + a^1 b^0,\;\; a^0 b^2 + a^1 \otimes b^1 + a^2 b^0\bigr).$$

This is associative and unital with unit $\mathbf{1} = (1, 0, 0)$, but not commutative (since $a^1 \otimes b^1 \neq b^1 \otimes a^1$ in general). Elements with $a^0 = 1$ are invertible: the nilpotent part $(0, a^1, a^2)$ satisfies $n^3 = 0$ by truncation, so the Neumann series terminates at two terms:

$$(1, a^1, a^2)^{-1} \;=\; (1,\; -a^1,\; a^1 \otimes a^1 - a^2).$$

### Chen's identity

A two-parameter element $\mathbf{X}(s,t) = (1, X_{s,t}, \mathbb{X}_{s,t})$ satisfies **Chen's identity** if

$$\mathbf{X}(s,t) \;=\; \mathbf{X}(s,u) \otimes_t \mathbf{X}(u,t) \qquad \text{for all } s \leq u \leq t.$$

In components, this unpacks to:

$$X_{s,t} \;=\; X_{s,u} + X_{u,t}$$

$$\mathbb{X}_{s,t} \;=\; \mathbb{X}_{s,u} + \mathbb{X}_{u,t} + X_{s,u} \otimes X_{u,t}$$

The level-1 identity is ordinary additivity of increments. The level-2 identity is the key new content: the cross-term $X_{s,u} \otimes X_{u,t}$ encodes the fact that iterated integrals do not split additively — they have a correction from the ordering of integration variables.

For a smooth path $\gamma$, the canonical enhancement $\mathbb{X}_{s,t} = \int_s^t (\gamma(r) - \gamma(s)) \otimes d\gamma(r)$ satisfies Chen's identity by splitting the integration domain.

### Group-like elements

An element $(1, x, \mathfrak{x}) \in T^{(2)}(V)$ is **group-like** if

$$	ext{Sym}(\mathfrak{x}) \;=\; \frac{x \otimes x}{2},$$

where $	ext{Sym}(\mathfrak{x}) = (\mathfrak{x} + \tau(\mathfrak{x}))/2$ is the symmetric part and $\tau$ is the tensor swap. Equivalently, every group-like element decomposes as

$$\mathfrak{x} \;=\; \frac{x \otimes x}{2} + A, \qquad A \in \Lambda^2(V),$$

where $A = 	ext{Anti}(\mathfrak{x})$ is the **Lévy area** — the antisymmetric part, representing the signed area swept out by the path. This is the genuinely free parameter: a group-like element is completely determined by $(x, A) \in V \times \Lambda^2(V)$.

The group-like elements $G^{(2)}(V)$ form a group under truncated multiplication. In the coordinates $(x, A)$, the group law is

$$(x, A) \cdot (y, B) \;=\; \bigl(x + y,\;\; A + B + \tfrac{1}{2}(x \otimes y - y \otimes x)\bigr),$$

which is the group law of the **free step-2 nilpotent group** — a generalization of the Heisenberg group.

### The homogeneous metric

The Carnot–Carathéodory (quasi-)metric on $G^{(2)}(V)$ is

$$d_{cc}(g, h) \;=\; \|g^{-1} \otimes_t h\|_{cc}, \qquad \|(1, x, \mathfrak{x})\|_{cc} \;=\; \max\bigl(\|x\|,\; \|\mathfrak{x} - x \otimes x / 2\|^{1/2}\bigr).$$

The $1/2$ exponent on the area term reflects parabolic scaling: area scales as length$^2$. This metric controls all the estimates in rough path theory.

## Planned results

### Phase 2.1: The truncated tensor algebra $T^{(2)}(V)$
| Result | Status |
|---|---|
| Type definition: $\mathbb{R} \times V \times (V \otimes V)$ | Planned |
| Addition, scalar multiplication, normed space instance | Planned |
| Truncated multiplication $\otimes_t$ and associativity | Planned |
| Unit element and inverse (for $a^0 = 1$) | Planned |
| Submultiplicative norm | Planned |

### Phase 2.2: Chen's identity
| Result | Status |
|---|---|
| Multiplicative form: $\mathbf{X}(s,t) = \mathbf{X}(s,u) \otimes_t \mathbf{X}(u,t)$ | Planned |
| Component form: additivity + area rule | Planned |
| Verification for smooth paths | Planned |
| Diagonal: $\mathbf{X}(s,s) = \mathbf{1}$ | Planned |
| Inverse relation | Planned |

### Phase 2.3: Group-like elements and the free nilpotent group
| Result | Status |
|---|---|
| Symmetric/antisymmetric decomposition | Planned |
| Group-like condition | Planned |
| Closure under multiplication | Planned |
| Closure under inversion | Planned |
| Lévy area characterization | Planned |
| Exponential and logarithm maps | Planned |
| Baker–Campbell–Hausdorff (exact for $N = 2$) | Planned |

### Phase 2.4: Homogeneous metric
| Result | Status |
|---|---|
| Homogeneous norm definition | Planned |
| Left-invariant quasi-metric | Planned |
| (Quasi-)triangle inequality | Planned |

## Design decisions

**Concrete before general.** Everything is defined for $N = 2$ explicitly. The general truncated tensor algebra $T^{(N)}(V)$ is not needed until $p \geq 3$ — which is beyond the scope of this formalization. When $N = 2$, the algebra is a triple, the group-like condition is a single equation, and the BCH formula is exact (no higher-order terms).

**The $G^{(2)}(V) = V \times \Lambda^2(V)$ shortcut.** An alternative formalization defines the free nilpotent group directly as $V \times \Lambda^2(V)$ with the Heisenberg-type group law, bypassing the tensor algebra and group-like condition. This is simpler but less canonical — it works perfectly for $N = 2$ but does not generalize to higher levels. The plan is to build the tensor algebra properly, with the direct-coordinates formulation available as a convenience.

**Norm choice.** The exact norm on $T^{(2)}(V)$ does not matter for the structural theory — any two submultiplicative norms on a finite-dimensional algebra are equivalent, and all rough path estimates depend on the norm only up to constants. The plan is to use whichever norm is easiest to prove submultiplicative (likely the sum-based norm $|a^0| + \|a^1\| + \|a^2\|^{1/2}$).

**Tensor product pragmatism.** Submultiplicativity requires the cross-norm property $\|v \otimes w\| \leq \|v\| \cdot \|w\|$. The projective tensor norm gives this automatically. If Mathlib's `Analysis.NormedSpace.TensorProduct` provides it, use it. If not, the identification $V \otimes V \cong V \to_L V$ (valid in finite dimensions) is a pragmatic alternative.

## Dependencies

### From Mathlib
| What | Used for |
|---|---|
| `TensorProduct`, `TensorProduct.comm` | $V \otimes V$ and the swap map |
| `NormedAddCommGroup`, `NormedSpace`, `NormedAlgebra` | Algebra instances |
| Projective tensor norm (if available) | Submultiplicativity |
| `LinearMap.lTensor`, `LinearMap.rTensor` | Tensor operations |

### From Stage 0
| What | Used for |
|---|---|
| `Partition`, `riemannSum` | Verification of Chen's identity for smooth paths |

### From Stage 1 (optional)
| What | Used for |
|---|---|
| Young integral | Chen's identity verification (or use classical RS) |

## Build order

The dependency graph is relatively linear:

```
Phase 2.1 ─── type + algebra ──→ multiplication + associativity ──→ inverse ──→ norm
                                          │
                                          ▼
Phase 2.2 ──────────────── Chen's identity (components) ──→ smooth verification
                                          │
                                          ▼
Phase 2.3 ────── Sym/Anti ──→ group-like ──→ closure ──→ exp/log ──→ BCH
                                                │
                                                ▼
Phase 2.4 ──────────────────────── homogeneous norm ──→ metric
```


## References

- Chen, K.T., *Integration of paths, geometric invariants and a generalized Baker–Hausdorff formula*, Ann. of Math. **65** (1957), 163–178
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapter 2
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapters 7–9
- Reutenauer, C., *Free Lie Algebras*, Oxford (1993)

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
