# Information Geometry in Lean 4

A formal development of **information geometry** — the differential geometry of statistical models — in [Lean 4](https://lean-lang.org/) with [Mathlib4](https://github.com/leanprover-community/mathlib4).

This library constructs the **Fisher–Rao metric** from first principles: starting from a parametric family of probability distributions, defining the score function and proving its vanishing expectation, assembling the Fisher information matrix, establishing its algebraic and analytic properties, and finally packaging the result as a Riemannian metric on the parameter space.

## Mathematical Content

The central object is the **statistical manifold**: a smooth parameter space $\Theta \subseteq \mathbb{R}^n$ indexing a family of probability densities $p(\theta, \omega)$ on a sample space $\Omega$, equipped with the **Fisher information metric**

$$g_{ij}(\theta) \;=\; \mathbb{E}_\theta\!\bigl[s_i \, s_j\bigr] \;=\; \int_\Omega \frac{\partial_i p(\theta, \omega)}{p(\theta, \omega)} \cdot \frac{\partial_j p(\theta, \omega)}{p(\theta, \omega)} \cdot p(\theta, \omega) \; d\mu(\omega)$$

where $s_i(\theta, \omega) = \partial_i \log p(\theta, \omega)$ is the **score function**.

### What is proved

| Result | Statement |
|--------|-----------|
| **Leibniz integral rule** | $\frac{d}{d\theta} \int p(\theta, \omega)\, d\mu = \int \frac{\partial p}{\partial \theta}\, d\mu$, justified by dominated convergence |
| **Score has zero mean** | $\mathbb{E}_\theta[s_i] = 0$ — the fundamental identity from which everything flows |
| **Fisher matrix symmetry** | $g_{ij} = g_{ji}$ |
| **Positive semidefiniteness** | $g_\theta(v, v) \geq 0$ for all tangent vectors $v$ — unconditional, no integrability needed |
| **Positive definiteness** | $g_\theta(v, v) = 0 \implies v = 0$ under score-injectivity |
| **Cross-integrability** | $s_i s_j \cdot p \in L^1(\mu)$ from $s_i^2 \cdot p \in L^1(\mu)$ via AM–GM |
| **Bilinearity** | $g_\theta$ is a genuine $\mathbb{R}$-bilinear form on $T_\theta\Theta$ |
| **Fisher = covariance** | $g_{ij} = \mathrm{Cov}_\theta(s_i, s_j)$ since $\mathbb{E}[s] = 0$ |
| **Alternative formula** | $g_{ij} = \int (\partial_i p)(\partial_j p) / p \; d\mu$ |
| **Self-adjointness** | The Fisher linear map $G: \mathbb{R}^n \to \mathbb{R}^n$ is self-adjoint |
| **Riemannian metric** | Smooth, symmetric, positive-definite family of bilinear forms on $\Theta$ |
| **Fisher norm** | $\lVert v \rVert_\theta = \sqrt{g_\theta(v,v)}$ with $\lVert v \rVert = 0 \iff v = 0$ |
| **Infinitesimal identifiability** | Score-injectivity implies distinct tangent directions yield distinct distributions |
| **KL self-divergence** | $D_{\mathrm{KL}}(\theta \,\|\, \theta) = 0$ |


## Architecture

The library is organized as a five-file dependency chain, each building on the last:

```
StatisticalModel.lean
        │
        ▼
    Score.lean
        │
        ▼
FisherInformation.lean
        │
        ▼
  FisherMetric.lean
        │
        ▼
StatisticalManifold.lean
```

### File Descriptions

**`StatisticalModel.lean`** — The foundational structure. Defines `StatisticalModel n Ω` as a smooth $n$-parameter family of probability densities on a measurable space $\Omega$ relative to a $\sigma$-finite reference measure. Carries nonnegativity, measurability, normalization ($\int p = 1$), a.e. positivity, and $C^\infty$ dependence on $\theta$. Also defines `RegularStatisticalModel`, which adds dominated-convergence bounds and score square-integrability — the regularity needed to differentiate under the integral sign. Derives the induced probability measure $P_\theta$, proves it is a probability measure, defines the log-density and expectation, and establishes identifiability.

**`Score.lean`** — The score function and its vanishing expectation. The main theorem is `score_expectation_eq_zero`: $E_\theta[s_i] = 0$. The proof applies Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` to differentiate $\int p(\theta, \omega)\, d\mu = 1$ in $\theta$, yielding $\int \partial_i p\, d\mu = 0$, then uses $\partial_i p = s_i \cdot p$ a.e. This is the first genuine exchange of limits in the development, and every subsequent result traces back to it.

**`FisherInformation.lean`** — The Fisher information matrix and bilinear form. Defines $g_{ij}(\theta) = E_\theta[s_i s_j]$ and $g_\theta(v, w) = E_\theta[\langle v, s \rangle \langle w, s \rangle]$. Proves symmetry (from commutativity of multiplication), positive semidefiniteness (from `integral_nonneg`), cross-integrability (from AM–GM), the bilinear expansion $g_\theta(v,w) = \sum_{ij} v_i w_j g_{ij}$, and positive definiteness under score-injectivity. Also establishes the covariance characterization and the alternative formula via density derivatives.

**`FisherMetric.lean`** — Promotion to a Riemannian metric. Proves bilinearity of $g_\theta$ by reducing to algebra on the matrix expansion (via `fisherBilin_eq_sum_fisherMatrix`), constructs `fisherBilinForm` as a `LinearMap.BilinForm ℝ`, defines a lightweight `RiemannianMetric` structure (symmetric + positive-definite + smooth family of bilinear forms on an open domain), and builds `fisherRiemannianMetric` under the `SmoothFisherModel` regularity bundle. Also defines the Fisher linear map and proves its self-adjointness.

**`StatisticalManifold.lean`** — The capstone. Assembles `StatisticalManifold n Ω` as a `RegularStatisticalModel` satisfying `SmoothFisherModel` globally: score-injectivity, score square-integrability, and smooth Fisher entries everywhere. Derives the Fisher inner product $\langle v, w \rangle_\theta$, Fisher norm $\lVert v \rVert_\theta$, and proves the norm-zero-iff characterization. Defines KL divergence and proves $D_{\mathrm{KL}}(\theta \| \theta) = 0$. States future directions (Cramér–Rao, $\alpha$-connections, Chentsov's theorem).


## Design Decisions

**Parameter space.** Concretely modeled as an open subset of `EuclideanSpace ℝ (Fin n)` rather than an abstract smooth manifold. This keeps proofs grounded in Mathlib's `ContDiffOn`, `fderiv`, and inner-product infrastructure without chart/atlas bookkeeping. Generalization to abstract manifolds via charts is a future layer.

**Density codomain.** Real-valued (`ℝ`), not `ℝ≥0∞`. The calculus layer — `log`, `fderiv`, bilinear forms — is native to `ℝ`. The bridge to measure theory uses `ENNReal.ofReal`, and nonnegativity is a carried field. This avoids coercion overhead in every differential-geometric statement.

**Layered regularity.** Following Mathlib's typeclass pattern:
- `StatisticalModel` — smoothness and measurability only
- `RegularStatisticalModel` — adds dominated-convergence bounds for differentiation under the integral
- `SmoothFisherModel` — adds smooth dependence of Fisher entries on $\theta$
- `StatisticalManifold` — the full package with global score-injectivity

Each theorem states exactly the regularity it needs.

**Unconditional vs. conditional results.** Algebraic properties (symmetry, positive semidefiniteness) hold unconditionally — they are pointwise identities or consequences of `integral_nonneg`, which returns 0 for non-integrable functions. Results needing finite Fisher entries carry explicit `ScoreSqIntegrableModel θ` hypotheses.

**Custom `RiemannianMetric`.** Mathlib's abstract Riemannian geometry targets `SmoothManifoldWithCorners` and does not yet provide a turnkey Riemannian metric structure. The lightweight `RiemannianMetric n` defined here carries exactly the needed data (matrix entries + symmetry + positive definiteness + smoothness) and is forward-compatible with a future Mathlib upgrade.


## Mathlib Dependencies

The development draws on three areas of Mathlib:

- **Measure theory & probability**: `MeasureSpace`, `WithDensity`, `Integrable`, `SigmaFinite`, `IsProbabilityMeasure`, `AEStronglyMeasurable`, Bochner integral
- **Analysis & calculus**: `ContDiffOn`, `fderiv`, `hasFDerivAt_integral_of_dominated_of_fderiv_le` (the Leibniz rule), `ContinuousLinearMap`, `EuclideanSpace`, `InnerProductSpace`
- **Special functions**: `Real.log`, `Real.exp`, `Real.sqrt`


## Building

Requires Lean 4 and Mathlib4. With [elan](https://github.com/leanprover/elan) installed:

```bash
lake build LogosLibrary.InformationGeometry
```

The files live under `LogosLibrary/InformationGeometry/` and import each other linearly as shown in the architecture diagram above.


## Future Work

- **`KLDivergence.lean`** — The Fisher metric as the Hessian of KL divergence: $D_{\mathrm{KL}}(p_\theta \| p_{\theta + \varepsilon v}) = \tfrac{1}{2}\varepsilon^2 g_\theta(v,v) + O(\varepsilon^3)$
- **`CramerRao.lean`** — The Cramér–Rao inequality $\mathrm{Cov}_\theta(T) \geq G(\theta)^{-1}$ for unbiased estimators
- **`Connections.lean`** — The $\alpha$-connections and dually flat structure of exponential/mixture families
- **`Chentsov.lean`** — Uniqueness of the Fisher metric among all metrics invariant under sufficient statistics
- **Exponential families** — Concrete instances satisfying all regularity conditions


## References

- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
- N. N. Čencov, *Statistical Decision Rules and Optimal Inference*, AMS, 1982.
- R. A. Fisher, "On the mathematical foundations of theoretical statistics", *Phil. Trans. Roy. Soc. London A* **222** (1922), 309–368.
- R. A. Fisher, "Theory of statistical estimation", *Proc. Cambridge Phil. Soc.* **22** (1925), 700–725.
- C. R. Rao, "Information and accuracy attainable in the estimation of statistical parameters", *Bull. Calcutta Math. Soc.* **37** (1945), 81–91.
- L. L. Campbell, "An extended Čencov characterization of the information metric", *Proc. Amer. Math. Soc.* **98** (1986), 135–141.


## License

Apache 2.0. See [LICENSE](LICENSE).

## Authors

Adam Bornemann & contributors.
