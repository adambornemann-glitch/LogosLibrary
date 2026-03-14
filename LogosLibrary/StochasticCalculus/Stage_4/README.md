# Stage 4: The Itô–Lyons Map

## Overview

This is the summit. Everything converges here.

The **Universal Limit Theorem** (ULT) states that the solution map sending a rough path $\mathbf{X}$, a vector field $f$, and an initial condition $a$ to the solution of the rough differential equation

$$dY = f(Y)\, d\mathbf{X}, \qquad Y\_0 = a$$

is well-defined and **continuous** in the rough path metric. This single theorem contains, as corollaries, the Wong–Zakai theorem, support theorems for SDEs, large deviations principles, and the entire pathwise approach to stochastic calculus.

No proof assistant has formalized the Universal Limit Theorem.

**Dependencies**: All of Stages 0–3

## Why this matters

Classical stochastic calculus constructs the Itô integral $\int Y\, dB$ using probability — martingale theory, filtrations, stopping times. The resulting integral depends on the *probabilistic structure* of Brownian motion, not just its path properties. This is why changing the approximation scheme (piecewise linear vs. midpoint vs. other) changes the limiting integral.

The rough path approach resolves this: the integral depends only on the **rough path lift** $\mathbf{B} = (B, \mathbb{B})$, and the solution map $\mathbf{B} \mapsto Y$ is continuous. Different approximation schemes converge to different rough path lifts (Stratonovich vs. Itô), explaining the discrepancy *deterministically*. Probability enters only in identifying which lift a given approximation scheme selects.

The ULT is what makes this programme rigorous. Without it, rough path theory is just a language. With it, it's a machine.

## Mathematical content

### Controlled paths

The key analytical structure is the **controlled path**. Let $\mathbf{X} = (X, \mathbb{X})$ be a $p$-rough path. A path $Y : [0,T] \to W$ is **controlled by $X$** if there exists a *Gubinelli derivative* $Y' : [0,T] \to L(V, W)$ such that the remainder

$$R^Y_{s,t} \;:=\; Y\_t - Y\_s - Y'\_s \cdot X_{s,t}$$

has finite $p/2$-variation — i.e., is more regular than $Y$ itself.

This is a *linearization*: $Y'\_s \cdot X_{s,t}$ is the first-order Taylor approximation of $Y\_t - Y\_s$ relative to the driving signal, and $R^Y$ is the higher-order remainder. The space of controlled paths $\mathcal{D}\_X^{2\gamma}$ (where $\gamma = 1/p$) is a Banach space under the norm

$$\|(Y, Y')\|\_X \;=\; \|Y'\|\_\infty \;+\; \|Y'\|\_{p\text{-var}} \;+\; \|R^Y\|\_{p/2\text{-var}}.$$

### The rough integral

Given a controlled path $(Y, Y')$ and a rough path $\mathbf{X} = (X, \mathbb{X})$, the approximation map is

$$\Xi(s,t) \;=\; Y\_s \cdot X_{s,t} \;+\; Y'\_s \cdot \mathbb{X}_{s,t}.$$

The first term is the Euler step (as in Young integration). The second term — the **area correction** $Y'\_s \cdot \mathbb{X}_{s,t}$ — is the genuinely new ingredient. For $p < 2$, the Euler step alone suffices (the defect is $O(\omega^{2/p})$ with $2/p > 1$). For $p \geq 2$, the defect of the Euler step is only $O(\omega^{2/p}) \leq O(\omega)$, which is *not enough* for the sewing lemma. The area correction pushes the defect to $O(\omega^{3/p})$ with $3/p > 1$ since $p < 3$.

### The critical defect estimate

The defect of $\Xi$ satisfies

$$\|\delta\Xi(s, u, t)\| \;\leq\; C \cdot \omega(s,t)^{3/p}.$$

The proof expands the defect using Chen's identity and the controlled path decomposition:

$$\delta\Xi(s,u,t) \;=\; -R^Y_{s,u} \cdot X_{u,t} \;-\; (Y'\_u - Y'\_s) \cdot \mathbb{X}_{u,t}.$$

The two terms contribute:

$$\|R^Y_{s,u}\| \cdot \|X_{u,t}\| \;\leq\; [R^Y]\_{p/2} \cdot \omega^{2/p} \cdot [X]\_p \cdot \omega^{1/p} \;=\; C \cdot \omega^{3/p}$$

$$\|Y'\_u - Y'\_s\| \cdot \|\mathbb{X}_{u,t}\| \;\leq\; [Y']\_p \cdot \omega^{1/p} \cdot [\mathbb{X}]\_{p/2} \cdot \omega^{2/p} \;=\; C \cdot \omega^{3/p}$$

The exponent $3/p$ comes from: 2 from the remainder (which has $p/2$-variation) plus 1 from the path increment, or 1 from the Gubinelli derivative variation plus 2 from the area. Both routes give $3/p > 1$ for $p < 3$. This is exactly the sewing lemma threshold.

### The rough integral via sewing

The sewing lemma applied to $\Xi$ produces the **rough integral**:

$$\int\_s^t Y\_r\, d\mathbf{X}\_r \;:=\; \mathrm{Sew}(\Xi)(s,t)$$

with approximation bound

$$\left\|\int\_s^t Y\, d\mathbf{X} - Y\_s \cdot X_{s,t} - Y'\_s \cdot \mathbb{X}_{s,t}\right\| \;\leq\; C \cdot \omega(s,t)^{3/p}.$$

Crucially, the indefinite rough integral $Z\_t = \int\_0^t Y\_r\, d\mathbf{X}\_r$ is itself a controlled path with Gubinelli derivative $Z' = Y$. This **closure property** is what makes iteration possible.

### The Picard fixed-point scheme

The rough differential equation $dY = f(Y)\, d\mathbf{X}$ is solved by finding a fixed point of the Picard map

$$\mathcal{M}(Y, Y')(t) \;=\; a + \int\_s^t f(Y\_r)\, d\mathbf{X}\_r, \qquad \mathcal{M}(Y,Y')' = f(Y).$$

The composition theorem (smooth $f$ applied to a controlled path gives a controlled path) and the integration closure property together show that $\mathcal{M}$ maps controlled paths to controlled paths. The contraction estimate

$$\|\mathcal{M}(Y\_1, Y'\_1) - \mathcal{M}(Y\_2, Y'\_2)\|\_X \;\leq\; C \cdot \|f\|\_{C^2} \cdot \omega(s, s{+}h)^{1/p} \cdot \|(Y\_1, Y'\_1) - (Y\_2, Y'\_2)\|\_X$$

shows that on a sufficiently short interval $[s, s{+}h]$ (where $\omega(s, s{+}h)$ is small enough), $\mathcal{M}$ is a contraction. The Banach fixed-point theorem gives local existence and uniqueness; time-stepping gives global existence.

### The Universal Limit Theorem

The solution map

$$\Phi \;:\; \mathbf{X} \;\mapsto\; Y^{\mathbf{X}}$$

is (locally Lipschitz) continuous in the rough path metric:

$$\sup\_{t \in [0,T]} \|Y^{\mathbf{X}}\_t - Y^{\mathbf{Y}}\_t\| \;\leq\; C \cdot d\_p(\mathbf{X}, \mathbf{Y}).$$

As a corollary: if $\gamma^n$ are smooth paths with $d\_p(S(\gamma^n), \mathbf{X}) \to 0$, and $Y^n$ solves the classical ODE $dY^n = f(Y^n)\, d\gamma^n$, then $Y^n \to Y^{\mathbf{X}}$ uniformly. This is the **universal limit property** — it says that rough path convergence of the driving signal implies convergence of the solutions, regardless of the approximation scheme.

## Planned results

### Phase 4.1: Controlled paths
| Result | Status |
|---|---|
| `ControlledPath` structure with Gubinelli derivative | Planned |
| Controlled path norm, Banach space instance | Planned |
| Driving path $X$ is controlled by itself | Planned |
| Composition with $C^2$ functions | Planned |

### Phase 4.2: The rough integral
| Result | Status |
|---|---|
| Approximation map $\Xi(s,t) = Y\_s \cdot X_{s,t} + Y'\_s \cdot \mathbb{X}_{s,t}$ | Planned |
| Defect estimate: $O(\omega^{3/p})$ | Planned |
| Rough integral via sewing lemma | Planned |
| Rough integral is a controlled path (closure) | Planned |
| Quantitative $p$-variation estimates | Planned |

### Phase 4.3: Local existence (RDE fixed point)
| Result | Status |
|---|---|
| Picard map definition | Planned |
| Contraction estimate on short intervals | Planned |
| Local existence and uniqueness (Banach) | Planned |
| A priori estimates on the solution | Planned |

### Phase 4.4: Global existence
| Result | Status |
|---|---|
| Time-stepping via control function | Planned |
| Concatenation of controlled paths | Planned |
| Global existence and uniqueness | Planned |

### Phase 4.5: The Universal Limit Theorem
| Result | Status |
|---|---|
| Stability estimate | Planned |
| Continuity of the Itô–Lyons map | Planned |
| Universal limit property (approximation form) | Planned |

### Phase 4.6: Consequences
| Result | Status |
|---|---|
| Chain rule / Itô formula for rough paths | Planned |
| Wong–Zakai theorem (corollary of ULT) | Planned |

## Where the bodies are buried

Every formalization project has hard parts that look easy on paper. Here they are, in order of expected pain:

**The defect estimate (4.2.2)** involves tracking which terms are $O(\omega^{1/p})$, which are $O(\omega^{2/p})$, and how they combine to give $O(\omega^{3/p})$. Every factor of $\omega^{1/p}$ comes from a different source — path increment, Gubinelli variation, area bound — and you need all three exponents to add up to $3/p$. The algebra is straightforward; the bookkeeping is relentless.

**The contraction estimate (4.3.2)** requires comparing two rough integrals with different integrands but the same rough path. The sewing lemma gives the difference, but extracting the Lipschitz constant requires careful tracking of which norms appear in which positions. The factor $\omega(s, s{+}h)^{1/p}$ that makes it a contraction comes from the local smallness of the control — this is where the sewing lemma's additivity is load-bearing.

**Concatenation of controlled paths (4.4.2)** is the sewing lemma additivity problem reincarnated for controlled paths. The $p$-variation of the concatenated remainder depends on both halves *and* the Gubinelli derivative matching at the junction. Getting the quantitative estimates right is where formalization earns its keep.

**The $C^3\_b$ hypothesis** on $f$ is used in exactly one place: the Taylor remainder in the composition theorem (4.1.4). Three derivatives are needed because one goes to the Gubinelli derivative $Df(Y) \cdot Y'$, one to estimating the variation of $Df(Y) \cdot Y'$, and one to the second-order Taylor remainder $O(\|Y\_t - Y\_s\|^2)$.

**Measurability of the Gubinelli derivative** $Y'\_t$ as a function of $t$ is often glossed over. In practice $Y' = f(Y)$ for the solution, which is continuous by the a priori estimates — but proving continuity requires those estimates, creating a mild circularity that must be resolved carefully.

## Dependencies

### From Stage 0
| What | Used for |
|---|---|
| Sewing lemma (Layer 2 or 3) | Constructing the rough integral |
| All sewing estimates and additivity | Approximation bounds, Picard argument |

### From Stage 1
| What | Used for |
|---|---|
| $p$-variation infrastructure | Controlled path norms, regularity |
| Young integral estimates | Composition, regularity bounds |

### From Stage 2
| What | Used for |
|---|---|
| $T^{(2)}(V)$, truncated multiplication | Encoding the area correction |
| Chen's identity | Defect computation |

### From Stage 3
| What | Used for |
|---|---|
| `RoughPath`, $d\_p$ metric, completeness | Domain of the Itô–Lyons map |

### From Mathlib
| What | Used for |
|---|---|
| `ContractingWith`, Banach fixed-point | Local existence |
| `fderiv`, `HasFDerivAt`, `ContDiff` | Composition with smooth functions |
| `BoundedContinuousFunction` | $C^k\_b$ vector fields |

## Build order

The dependency chain is essentially linear — this is a summit, not a plateau:

```
Phase 4.1 ─── controlled paths ──→ norm ──→ composition theorem
                                                    │
Phase 4.2 ─── Ξ definition ──→ defect estimate ─────┤
                                       │            │
                                       ▼            ▼
                               rough integral ──→ closure (integral is controlled)
                                                    │
                                                    ▼
Phase 4.3 ──────────── Picard map ──→ contraction ──→ local existence
                                                           │
                                                           ▼
Phase 4.4 ─────────── concatenation ──→ time-stepping ──→ global existence
                                                              │
                                                              ▼
Phase 4.5 ──────────── stability ──→ continuity ──→ Universal Limit Theorem
                                                         │
                                                         ▼
Phase 4.6 ──────────── chain rule, Wong–Zakai (corollaries)
```

## References

- Lyons, T., *Differential equations driven by rough signals*, Rev. Mat. Iberoam. **14** (1998), 215–310
- Gubinelli, M., *Controlling rough paths*, J. Funct. Anal. **216** (2004), 86–140
- Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Springer (2020), Chapters 4–8
- Friz, P.; Victoir, N., *Multidimensional Stochastic Processes as Rough Paths*, Cambridge (2010), Chapters 10–12
- Lyons, T.; Caruana, M.; Lévy, T., *Differential Equations Driven by Rough Paths*, Springer LNM **1908** (2007)

## Authors

Adam Bornemann & Doctor Professor Baron von Wobble-Bob
