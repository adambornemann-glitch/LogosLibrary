# Stage 3: The Space of Rough Paths

## Overview

This is where the two streams converge. The analytical infrastructure of Stage 1 ($p$-variation, Young integration) and the algebraic infrastructure of Stage 2 (truncated tensor algebra, Chen's identity, group-like elements) merge to define the central object of the theory: the **space of $p$-rough paths**, equipped with a metric in which it is complete.

A $p$-rough path is not just a path — it is a path *enhanced* with area data, satisfying Chen's algebraic identity and a $p$-variation regularity condition. The enhancement is what makes integration possible for paths too rough for classical or Young theory. For $p \in [2,3)$ — covering Brownian motion — the enhancement is a single additional layer: the Lévy area $\mathbb{X}_{s,t} \in V \otimes V$.

The critical output of this stage is the `RoughPath` structure that Stage 4 consumes: a complete metric space of driving signals, ready for the integration and differential equation machinery.


## Mathematical content

### The rough path

A **$p$-rough path** over $V$ on $[0, T]$ (for $p \in [2,3)$) is a pair $\mathbf{X} = (X, \mathbb{X})$ where $X_{s,t} \in V$ and $\mathbb{X}_{s,t} \in V \otimes V$ satisfy:

**Chen's identity:**

$$X_{s,t} = X_{s,u} + X_{u,t}$$

$$\mathbb{X}_{s,t} = \mathbb{X}_{s,u} + \mathbb{X}_{u,t} + X_{s,u} \otimes X_{u,t}$$

**Regularity:**

$$\|X\|_{p\text{-var};\,[s,t]} < \infty, \qquad \|\mathbb{X}\|_{p/2\text{-var};\,[s,t]} < \infty.$$

The level-1 identity is ordinary additivity. The level-2 identity — with its cross-term $X_{s,u} \otimes X_{u,t}$ — is the algebraic heart of rough path theory: it encodes the fact that iterated integrals do not split additively.

### The rough path control

The **rough path control** combines both levels:

$$\omega_{\mathbf{X}}(s,t) \;=\; \|X\|_{p\text{-var};\,[s,t]}^p \;+\; \|\mathbb{X}\|_{p/2\text{-var};\,[s,t]}^{p/2}.$$

This is a super-additive control satisfying the graded bounds

$$\|X_{s,t}\| \;\leq\; \omega_{\mathbf{X}}(s,t)^{1/p}, \qquad \|\mathbb{X}_{s,t}\| \;\leq\; \omega_{\mathbf{X}}(s,t)^{2/p},$$

which are the analytical content of rough path regularity. The exponents $1/p$ and $2/p$ reflect the grading: area scales as length$^2$.

### Geometric rough paths

A rough path $\mathbf{X}$ is **geometric** if $(1, X_{s,t}, \mathbb{X}_{s,t}) \in G^{(2)}(V)$ for all $s \leq t$, i.e.,

$$\operatorname{Sym}(\mathbb{X}_{s,t}) \;=\; \frac{X_{s,t} \otimes X_{s,t}}{2}.$$

Every geometric rough path is determined by its path increment $X$ and its Lévy area $A_{s,t} = \operatorname{Anti}(\mathbb{X}_{s,t})$. Smooth paths always produce geometric rough paths via the iterated integral construction. The geometric condition is preserved by limits — so the geometric rough paths form a closed (hence complete) subspace.

### The rough path metric

The $p$-variation distance between rough paths $\mathbf{X}$ and $\mathbf{Y}$ is

$$d_p(\mathbf{X}, \mathbf{Y}) \;=\; \|X - Y\|_{p\text{-var}} \;+\; \|\mathbb{X} - \mathbb{Y}\|_{p/2\text{-var}}^{1/2}.$$

The square root on the level-2 term ensures correct homogeneity: under $\mathbf{X} \mapsto \lambda \mathbf{X}$ (scaling $X$ by $\lambda$ and $\mathbb{X}$ by $\lambda^2$), both terms scale like $|\lambda|$.

### Completeness

The space of $p$-rough paths with $d_p$ is **complete**. The proof extracts pointwise limits from a Cauchy sequence (using completeness of $V$ and $V \otimes V$), verifies that Chen's identity passes to the limit, and checks that $p$-variation is lower semicontinuous:

$$\|X\|_{p\text{-var}} \;\leq\; \liminf_n \|X_n\|_{p\text{-var}}.$$

This follows because for any fixed partition, the Riemann sum of the limit equals the limit of the Riemann sums, and the supremum over partitions is a supremum of continuous functions — hence lower semicontinuous.

The geometric rough paths form a closed subspace (the geometric condition is a continuous equation), hence are also complete.

### The Young lift

For $p < 2$, the situation simplifies dramatically: a path $\gamma$ with finite $p$-variation has a **unique** geometric rough path lift, defined by the Young integral

$$\mathbb{X}_{s,t} \;=\; \int_s^t (\gamma(r) - \gamma(s)) \otimes d\gamma(r).$$

This exists because $1/p + 1/p = 2/p > 1$ when $p < 2$. For $p \geq 2$, the lift is *not* unique — different choices of $\mathbb{X}$ (different Lévy areas) give different rough paths above the same $\gamma$. This non-uniqueness is the fundamental reason rough path theory exists: for Brownian motion, the Stratonovich and Itô lifts differ by $\delta^{ij}(t-s)/2$ in the area, producing different integrals.

## Planned results

### Phase 3.1: The `RoughPath` structure
| Result | Status |
|---|---|
| Core definition with Chen's identity + regularity | Planned |
| Diagonal vanishing and inversion | Planned |
| Rough path control function | Planned |
| Equivalence: $p$-variation vs. control-based definition | Planned |

### Phase 3.2: Geometric rough paths
| Result | Status |
|---|---|
| `GeometricRoughPath` extending `RoughPath` | Planned |
| Geometricity consistent with Chen's identity | Planned |
| Lévy area decomposition | Planned |
| Smooth paths give geometric rough paths | Planned |

### Phase 3.3: The rough path metric
| Result | Status |
|---|---|
| Level-1 $p$-variation distance | Planned |
| Level-2 $p/2$-variation distance (with square root) | Planned |
| Combined metric $d_p$ | Planned |
| Metric space instance | Planned |

### Phase 3.4: Completeness
| Result | Status |
|---|---|
| Completeness of the rough path metric space | Planned |
| Geometric rough paths form a closed subspace | Planned |
| Completeness of geometric rough paths | Planned |

### Phase 3.5: The signature map
| Result | Status |
|---|---|
| Smooth path $\mapsto$ geometric rough path | Planned |
| Continuity / Lipschitz estimate | Planned |
| Density of smooth signatures (may be deferred) | Planned |

### Phase 3.6: Lifting
| Result | Status |
|---|---|
| Young lift for $p < 2$ (unique) | Planned |
| Non-uniqueness for $p \geq 2$ | Planned |
| Brownian rough path existence (axiom) | Planned |

## Design decisions

**Bundle $p$.** The space of $p$-rough paths is the natural object — it carries a metric and is complete. Bundling $p$ into the structure makes "this is a complete metric space" a clean statement. Coercion from $p$-rough paths to $p'$-rough paths for $p' > p$ is straightforward.

**Two-parameter maps, not paths into $G^{(2)}(V)$.** The current two-parameter representation $(X_{s,t}, \mathbb{X}_{s,t})$ matches the sewing lemma's interface and makes Chen's identity easy to state. Encoding a rough path as a single path into the group $G^{(2)}(V)$ would obscure the connection to integration.

**Both regularity formulations.** The $p$-variation form (supremum over partitions) is standard and defines the metric. The control-based form ($\|X_{s,t}\| \leq \omega^{1/p}$) is what the sewing lemma consumes. The bridge between them is a key structural lemma — provide both and prove equivalence.

**General before geometric.** Develop the full theory for general rough paths first. Add geometricity as a hypothesis only where mathematically required: the chain rule form, density of smooth paths, and the relationship to signatures.

## Dependencies

### From Stage 1
| What | Used for |
|---|---|
| `ePVariationOn`, `HasFinitePVariationOn` | Regularity conditions |
| `ContControl`, `isControl_ePVariationOn` | Control function packaging |
| Young integral | Smooth path signatures, Young lift |
| Integration by parts | Geometricity of smooth lifts |
| Continuity of Young integral | Continuity of the signature map |

### From Stage 2
| What | Used for |
|---|---|
| `TruncTensor₂`, truncated multiplication | Encoding $(1, X, \mathbb{X})$ |
| Chen's identity (component form) | Core axiom of the structure |
| `GroupLike₂`, closure under multiplication | Geometric rough paths |
| Sym/Anti decomposition | Lévy area, geometric condition |
| Homogeneous norm | Rough path metric |

### From Mathlib
| What | Used for |
|---|---|
| Complete metric spaces, `CauchySeq`, `limUnder` | Completeness proof |
| Lower semicontinuity of suprema | $p$-variation of limits |

## Build order

```
Phase 3.1 ─── RoughPath structure ──→ diagonal, inversion ──→ control function
                    │                                              │
                    ▼                                              ▼
Phase 3.2 ─── GeometricRoughPath ──→ consistency ──→ smooth lifts (needs Stage 1)
                    │
                    ▼
Phase 3.3 ─── d₁, d₂ distances ──→ combined metric ──→ metric space instance
                                                              │
                                                              ▼
Phase 3.4 ────────────────── pointwise limits ──→ Chen passes to limit
                                                       │
                                                       ▼
                                              p-var semicontinuity ──→ completeness
                                                                           │
                                                                           ▼
                                                              geometric subspace closed
                                                                           │
Phase 3.5 ─── signature map ──→ continuity                                 │
                                                                           ▼
Phase 3.6 ─── Young lift (p < 2) ──→ non-uniqueness (p ≥ 2) ──→ BM axiom
```

## References

- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapters 2–3
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapters 8–9
- Lyons, T.; Qian, Z., *System Control and Rough Paths*, Oxford (2002)

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob