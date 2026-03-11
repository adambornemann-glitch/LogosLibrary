# Information Geometry in Lean 4

A formal development of **information geometry** and its application to **quantum mechanics** in [Lean 4](https://lean-lang.org/) with [Mathlib4](https://github.com/leanprover-community/mathlib4).

Starting from a parametric family of probability distributions, the library constructs the **Fisher–Rao metric**, proves the **Cramér–Rao bound**, and then bridges to quantum mechanics — deriving the **Robertson**, **Schrödinger**, and **Heisenberg** uncertainty relations as corollaries of information-geometric inequalities. The capstone is a formal proof that the **Kähler structure** of the quantum state manifold (Riemannian metric + symplectic form) arises from the **RLD Fisher information**, with the Schrödinger uncertainty relation as its Cauchy–Schwarz inequality.

---

## The Main Theorem (Informally)

The library proves, in a formally verified chain from axioms to conclusions:

> **The Schrödinger uncertainty relation is the Cramér–Rao bound for the Right Logarithmic Derivative Fisher information.**

Concretely, given observables $A$ and $B$ on a quantum state $\psi$:

$$\sigma_A^2 \, \sigma_B^2 \;\geq\; \underbrace{\mathrm{Cov}(A,B)^2}_{\text{Riemannian (SLD)}} \;+\; \underbrace{\tfrac{1}{4}\bigl|\langle[A,B]\rangle\bigr|^2}_{\text{symplectic}}$$

The first term is the **covariance** — the real part of $\langle\tilde{A}\psi, \tilde{B}\psi\rangle$, corresponding to the **SLD Fisher metric** $g$.

The second term is the **commutator expectation** — the imaginary part, corresponding to the **symplectic form** $\omega$.

Together they form the **Kähler metric** $G^{\mathrm{RLD}} = g + i\omega$ on the quantum state manifold. The Schrödinger bound is its Cauchy–Schwarz inequality:

$$g(v,v)\,g(w,w) \;\geq\; g(v,w)^2 + \omega(v,w)^2$$

Robertson's inequality drops the covariance term. Classical statistics drops the symplectic term. Quantum mechanics requires both.


---

## Mathematical Content

### Part I: The Fisher–Rao Metric

The foundational object is the **statistical manifold**: a smooth parameter space $\Theta \subseteq \mathbb{R}^n$ indexing a family of probability densities $p(\theta, \omega)$ on a sample space $\Omega$, equipped with the **Fisher information metric**

$$g_{ij}(\theta) \;=\; \mathbb{E}_\theta\!\bigl[s_i \, s_j\bigr] \;=\; \int_\Omega \frac{\partial_i p(\theta, \omega)}{p(\theta, \omega)} \cdot \frac{\partial_j p(\theta, \omega)}{p(\theta, \omega)} \cdot p(\theta, \omega) \; d\mu(\omega)$$

where $s_i(\theta, \omega) = \partial_i \log p(\theta, \omega)$ is the **score function**.

| Result | Statement | File |
|--------|-----------|------|
| **Leibniz integral rule** | $\frac{d}{d\theta} \int p\, d\mu = \int \frac{\partial p}{\partial \theta}\, d\mu$ | `Score.lean` |
| **Score has zero mean** | $\mathbb{E}_\theta[s_i] = 0$ | `Score.lean` |
| **Fisher matrix symmetry** | $g_{ij} = g_{ji}$ | `FisherInformation.lean` |
| **Positive semidefiniteness** | $g_\theta(v, v) \geq 0$ | `FisherInformation.lean` |
| **Positive definiteness** | $g_\theta(v, v) = 0 \Rightarrow v = 0$ under score-injectivity | `FisherInformation.lean` |
| **Cross-integrability** | $s_i s_j \cdot p \in L^1(\mu)$ via AM–GM | `FisherInformation.lean` |
| **Bilinearity** | $g_\theta(v,w) = \sum_{ij} v_i w_j\, g_{ij}(\theta)$ | `FisherMetric.lean` |
| **Fisher = covariance** | $g_{ij} = \mathrm{Cov}_\theta(s_i, s_j)$ | `FisherInformation.lean` |
| **Riemannian metric** | Smooth, symmetric, positive-definite on $\Theta$ | `FisherMetric.lean` |
| **Fisher norm** | $\lVert v \rVert_\theta = 0 \iff v = 0$ | `StatisticalManifold.lean` |
| **Infinitesimal identifiability** | Score-injectivity $\Rightarrow$ locally injective parametrization | `StatisticalManifold.lean` |
| **KL self-divergence** | $D_{\mathrm{KL}}(\theta \,\Vert\, \theta) = 0$ | `StatisticalManifold.lean` |


### Part II: The Cramér–Rao Bound

The **Cramér–Rao inequality** is the fundamental precision limit for statistical estimation. For a scalar parameter $\theta$ and unbiased estimator $T$ with $\mathbb{E}_\theta[T] = \tau(\theta)$:

$$\mathrm{Var}_\theta(T) \;\geq\; \frac{\bigl(\partial_\theta \tau\bigr)^2}{I(\theta)}$$

where $I(\theta) = g_{\theta\theta}$ is the Fisher information. Equality holds if and only if $T$ is **efficient**: $T(\omega) = a + b\, s(\theta, \omega)$ a.e.

| Result | Statement | File |
|--------|-----------|------|
| **Covariance–score identity** | $\mathrm{Cov}_\theta(T, s_i) = \partial_i \mathbb{E}_\theta[T]$ | `Cross.lean` |
| **Cauchy–Schwarz** | $({\textstyle\int} f g\, p\, d\mu)^2 \leq ({\textstyle\int} f^2 p\, d\mu)({\textstyle\int} g^2 p\, d\mu)$ | `CauchySchwarz.lean` |
| **CS equality** | Equality $\iff$ $f = c \cdot g$ a.e. | `CauchySchwarz.lean` |
| **Cramér–Rao bound** | $\mathrm{Var}(T) \geq (\partial_i \tau)^2 / g_{ii}(\theta)$ | `Bound.lean` |
| **Equality characterization** | Saturation $\iff$ $T = a + b\, s_i$ a.e. | `Bound.lean` |


### Part III: Quantum Uncertainty from Information Geometry

The **quantum phase model** bridges classical information geometry and quantum mechanics. A one-parameter statistical model is induced by measuring observable $B$ on the phase-shifted state $\psi(\theta) = e^{-i\theta A}\psi$. Three identities connect the two worlds:

$$I(\theta_0) = 4\,\mathrm{Var}_\psi(A) \qquad\qquad \mathrm{Var}_{\mathrm{stat}}(T) = \mathrm{Var}_\psi(B) \qquad\qquad \frac{d\tau}{d\theta}\bigg|_{\theta_0} = \mathrm{Im}\langle\psi, [A,B]\psi\rangle$$

Substituting into the Cramér–Rao bound yields the **Robertson uncertainty relation**; specializing to canonical conjugates yields Heisenberg.

| Result | Statement | File |
|--------|-----------|------|
| **Robertson from Fisher** | $\sigma_A \sigma_B \geq \tfrac{1}{2}\lvert\langle[A,B]\rangle\rvert$ | `CramerRao.lean` |
| **Heisenberg from Fisher** | $\sigma_X \sigma_P \geq \hbar/2$ for $[X,P] = i\hbar$ | `CramerRao.lean` |
| **Commutator purely imaginary** | $\mathrm{Re}\langle\psi, [A,B]\psi\rangle = 0$ | `Robertson.lean` |


### Part IV: The Schrödinger Inequality and Kähler Geometry

The **Schrödinger uncertainty relation** (1930) strengthens Robertson by retaining the covariance term that Robertson discards. The inner product $\langle\tilde{A}\psi, \tilde{B}\psi\rangle$ decomposes as:

$$\langle\tilde{A}\psi, \tilde{B}\psi\rangle \;=\; \underbrace{\mathrm{Cov}(A,B)}_{\text{real part}} \;+\; \underbrace{\tfrac{i}{2}\,\mathrm{Im}\langle\psi,[A,B]\psi\rangle}_{\text{imaginary part}}$$

Cauchy–Schwarz on the full complex inner product gives:

$$\sigma_A^2\,\sigma_B^2 \;\geq\; |\langle\tilde{A}\psi, \tilde{B}\psi\rangle|^2 \;=\; \mathrm{Cov}(A,B)^2 + \tfrac{1}{4}|\langle[A,B]\rangle|^2$$

| Result | Statement | File |
|--------|-----------|------|
| **Re = covariance** | $\mathrm{Re}\langle\tilde{A}\psi, \tilde{B}\psi\rangle = \mathrm{Cov}(A,B)$ | `Schrodinger.lean` |
| **Schrödinger inequality** | $\sigma_A^2 \sigma_B^2 \geq \tfrac{1}{4}\lvert\langle[A,B]\rangle\rvert^2 + \mathrm{Cov}(A,B)^2$ | `Schrodinger.lean` |
| **Robertson as corollary** | Dropping $\mathrm{Cov}^2 \geq 0$ recovers Robertson | `Schrodinger.lean` |


### Part V: The RLD Fisher Information and the Kähler Structure

The **Right Logarithmic Derivative** (RLD) Fisher information is a complex-valued extension of the SLD Fisher metric:

$$G^{\mathrm{RLD}}_{ij}(\theta) \;=\; \underbrace{g_{ij}(\theta)}_{\text{Riemannian (SLD)}} \;+\; i\,\underbrace{\omega_{ij}(\theta)}_{\text{symplectic}}$$

where $g_{ij}$ is the ordinary (real, symmetric) Fisher metric and $\omega_{ij}$ is an antisymmetric **symplectic form**. Classically, $\omega = 0$ and $G^{\mathrm{RLD}} = G^{\mathrm{SLD}}$ (Chentsov's theorem). The nonvanishing of $\omega$ is a purely quantum phenomenon.

The **Schrödinger–Cramér–Rao bound** is the Cauchy–Schwarz inequality for this complex Hermitian form:

$$g(v,v)\,g(w,w) \;\geq\; g(v,w)^2 + \omega(v,w)^2$$

The **Pythagorean decomposition** makes the two terms "orthogonal" — they are the real and imaginary parts of a single complex inner product:

$$|G^{\mathrm{RLD}}(v,w)|^2 = g(v,w)^2 + \omega(v,w)^2$$

| Result | Statement | File |
|--------|-----------|------|
| **Symplectic antisymmetry** | $\omega(v,w) = -\omega(w,v)$ | `SchrodingerRLD.lean` |
| **Symplectic self-pairing** | $\omega(v,v) = 0$ | `SchrodingerRLD.lean` |
| **RLD Hermitianity** | $G^{\mathrm{RLD}}_{ji} = \overline{G^{\mathrm{RLD}}_{ij}}$ | `SchrodingerRLD.lean` |
| **Pythagorean decomposition** | $\lvert G^{\mathrm{RLD}}(v,w)\rvert^2 = g(v,w)^2 + \omega(v,w)^2$ | `SchrodingerRLD.lean` |
| **Schrödinger–CR bound** | $g_{ii}\,g_{jj} \geq g_{ij}^2 + \omega_{ij}^2$ | `SchrodingerRLD.lean` |
| **Robertson from Schrödinger** | $g_{ii}\,g_{jj} \geq \omega_{ij}^2$ (drop $g_{ij}^2$) | `SchrodingerRLD.lean` |
| **SLD Cauchy–Schwarz** | $g_{ii}\,g_{jj} \geq g_{ij}^2$ (drop $\omega_{ij}^2$) | `SchrodingerRLD.lean` |
| **Determinant form** | $g_{ii}\,g_{jj} - g_{ij}^2 - \omega_{ij}^2 \geq 0$ | `SchrodingerRLD.lean` |


### Part VI: The Quantum–Geometric Bridge

The **composite observable** $O_v = \sum_i v_i O_i$ contracts a real tangent vector against a family of self-adjoint operators — the quantum analogue of the **directional score** $\langle v, s(\theta,\omega)\rangle = \sum_i v_i s_i$ in information geometry.

Three bilinearity lemmas establish that the covariance matrix and commutator matrix are genuine tensor fields on the parameter space:

$$\mathrm{Cov}(O_v, O_w)_\psi = \sum_{ij} v_i w_j\, \mathrm{Cov}(O_i, O_j)_\psi$$

$$\mathrm{Im}\langle\psi, [O_v, O_w]\psi\rangle = \sum_{ij} v_i w_j\, \mathrm{Im}\langle\psi, [O_i, O_j]\psi\rangle$$

$$\mathrm{Var}(O_v)_\psi = \sum_{ij} v_i v_j\, \mathrm{Cov}(O_i, O_j)_\psi$$

The **quantum Schrödinger–Cauchy–Schwarz theorem** then applies the Schrödinger inequality to $O_v$ and $O_w$, yielding the RLD Cauchy–Schwarz condition at the level of the component matrices.

This **discharges** the `rld_cauchy_schwarz` axiom of `RLDFisherModel`, constructing a formally verified `quantumRLDFisherModel` with:

$$g_{ij} = 4\,\mathrm{Cov}(O_i, O_j)_\psi \qquad\qquad \omega_{ij} = 2\,\mathrm{Im}\langle\psi, [O_i, O_j]\psi\rangle$$

| Result | Statement | File |
|--------|-----------|------|
| **Composite self-adjointness** | $O_v = \sum v_i O_i$ is symmetric | `CompositeObservable.lean` |
| **Expectation linearity** | $\langle O_v\rangle = \sum v_i \langle O_i\rangle$ | `CompositeObservable.lean` |
| **Covariance bilinearity** | $\mathrm{Cov}(O_v, O_w) = \sum_{ij} v_i w_j \,\mathrm{Cov}(O_i, O_j)$ | `CompositeObservable.lean` |
| **Commutator bilinearity** | $\mathrm{Im}\langle[O_v, O_w]\rangle = \sum_{ij} v_i w_j\, \mathrm{Im}\langle[O_i, O_j]\rangle$ | `CompositeObservable.lean` |
| **Variance bilinearity** | $\mathrm{Var}(O_v) = \sum_{ij} v_i v_j\, \mathrm{Cov}(O_i, O_j)$ | `CompositeObservable.lean` |
| **Quantum Schrödinger–CS** | RLD Cauchy–Schwarz from Hilbert-space CS | `QuantumFisherModel.lean` |
| **Model construction** | `RLDFisherModel` from quantum data with axiom discharged | `QuantumFisherModel.lean` |


---

## Architecture

```
                    ┌──────────────────────┐
                    │  StatisticalModel    │  Parametric family of densities
                    └──────────┬───────────┘
                               │
                    ┌──────────▼───────────┐
                    │      Score           │  E[sᵢ] = 0 (Leibniz rule)
                    └──────────┬───────────┘
                               │
                    ┌──────────▼───────────┐
                    │  FisherInformation   │  gᵢⱼ = E[sᵢsⱼ], bilinear form
                    └──────────┬───────────┘
                               │
                    ┌──────────▼───────────┐
                    │    FisherMetric      │  Riemannian metric on Θ
                    └──────────┬───────────┘
                               │
                ┌──────────────┼──────────────┐
                │              │              │
     ┌──────────▼──────┐ ┌────▼────────┐ ┌───▼────────────────┐
     │ StatisticalMfld │ │ CramerRao   │ │ SchrodingerRLD     │
     │ (KL, norm, id.) │ │ (Var ≥ …)   │ │ (g + iω, Kähler)   │
     └─────────────────┘ └──────┬──────┘ └───────┬────────────┘
                                │                │
                         ┌──────▼──────┐  ┌──────▼─────────────┐
                         │  Robertson  │  │ CompositeObservable │
                         │  Heisenberg │  │ (O_v, bilinearity)  │
                         │  Schrödinger│  └──────┬─────────────┘
                         └─────────────┘         │
                                          ┌──────▼─────────────┐
                                          │ QuantumFisherModel │
                                          │ (bridge: QM → IG)  │
                                          └────────────────────┘
```

### File Descriptions

#### Information Geometry Core

**`StatisticalModel.lean`** — The foundational structure. Defines `StatisticalModel n Ω` as a smooth $n$-parameter family of probability densities on a measurable space $\Omega$ relative to a $\sigma$-finite reference measure. Carries nonnegativity, measurability, normalization ($\int p = 1$), a.e. positivity, and $C^\infty$ dependence on $\theta$. Also defines `RegularStatisticalModel` with dominated-convergence bounds. Derives the induced probability measure, log-density, and expectation.

**`Score.lean`** — The score function and its vanishing expectation. The main theorem `score_expectation_eq_zero` ($\mathbb{E}_\theta[s_i] = 0$) is proved by applying Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` to differentiate $\int p\, d\mu = 1$ in $\theta$. This is the first genuine exchange of limits, and every subsequent result traces back to it.

**`FisherInformation.lean`** — The Fisher information matrix $g_{ij}(\theta) = \mathbb{E}_\theta[s_i s_j]$ and the bilinear form $g_\theta(v,w) = \mathbb{E}_\theta[\langle v,s\rangle \langle w,s\rangle]$. Proves symmetry, positive semidefiniteness, cross-integrability via AM–GM, the bilinear expansion, positive definiteness under score-injectivity, the covariance characterization, and the alternative formula via density derivatives.

**`FisherMetric.lean`** — Promotes the Fisher bilinear form to a Riemannian metric. Proves bilinearity by reducing to finite sums via `fisherBilin_eq_sum_fisherMatrix`, constructs the `LinearMap.BilinForm`, defines `RiemannianMetric n`, and builds the Fisher–Rao metric under `SmoothFisherModel` regularity. Also defines the Fisher linear map and proves self-adjointness.

**`StatisticalManifold.lean`** — Assembles the full `StatisticalManifold n Ω` with global score-injectivity, score square-integrability, and smooth Fisher entries. Derives the Fisher inner product, Fisher norm, norm-zero-iff, KL divergence, and infinitesimal identifiability.

#### Cramér–Rao Bound

**`Cross.lean`** — The covariance–score identity: $\mathrm{Cov}_\theta(T, s_i) = \partial_i \mathbb{E}_\theta[T]$. This is the Leibniz rule applied to the unbiasedness constraint.

**`CauchySchwarz.lean`** — Cauchy–Schwarz for density-weighted integrals, with a full equality characterization: $(\int fg\,p)^2 = (\int f^2 p)(\int g^2 p)$ iff $f = c \cdot g$ a.e.

**`Bound.lean`** — The Cramér–Rao inequality $\mathrm{Var}_\theta(T) \geq (\partial_i \tau)^2 / g_{ii}(\theta)$ and its equality characterization (efficient estimators).

**`CramerRao.lean`** — The quantum bridge. Defines `QuantumPhaseModel` carrying three axioms ($I = 4\,\mathrm{Var}(A)$, $\mathrm{Var}_{\mathrm{stat}} = \mathrm{Var}_{\mathrm{QM}}$, $d\tau/d\theta = \mathrm{Im}\langle[A,B]\rangle$) and derives Robertson and Heisenberg from Cramér–Rao.

#### Quantum Uncertainty

**`Robertson.lean`** — The Robertson uncertainty relation $\sigma_A \sigma_B \geq \frac{1}{2}|\langle[A,B]\rangle|$ via Cauchy–Schwarz in Hilbert space.

**`Schrodinger.lean`** — The Schrödinger uncertainty relation. Identifies $\mathrm{Re}\langle\tilde{A}\psi, \tilde{B}\psi\rangle = \mathrm{Cov}(A,B)$ and retains both real and imaginary parts of the inner product to obtain $\sigma_A^2 \sigma_B^2 \geq \mathrm{Cov}^2 + \frac{1}{4}|\langle[A,B]\rangle|^2$.

#### The Kähler Bridge

**`SchrodingerRLD.lean`** — The RLD Fisher information $G^{\mathrm{RLD}} = g + i\omega$ as a complex Hermitian matrix on the parameter space. Defines `RLDFisherModel` with a symplectic form and the RLD Cauchy–Schwarz axiom. Proves the Pythagorean decomposition, the Schrödinger–Cramér–Rao bound, and derives Robertson and standard Cauchy–Schwarz as corollaries.

**`CompositeObservable.lean`** — The composite observable $O_v = \sum_i v_i O_i$ and the `QuantumRLDData` structure packaging $n$ observables with an invariant domain. Proves that covariance, commutator expectation, and variance are bilinear over composites — establishing that these matrices are genuine tensor fields on the parameter space.

**`QuantumFisherModel.lean`** — The bridge. Applies the Schrödinger uncertainty relation to composite observables and substitutes the bilinearity lemmas to discharge the `rld_cauchy_schwarz` axiom. Constructs a formally verified `RLDFisherModel` from quantum data with $g_{ij} = 4\,\mathrm{Cov}(O_i, O_j)$ and $\omega_{ij} = 2\,\mathrm{Im}\langle\psi,[O_i,O_j]\psi\rangle$.


---

## The Physical Picture

### Why information geometry?

The Fisher information metric $g_{ij}(\theta) = \mathbb{E}_\theta[s_i s_j]$ measures the **statistical distinguishability** of nearby distributions. Moving from $p_\theta$ to $p_{\theta + d\theta}$ costs an amount of information proportional to $g_{ij}\, d\theta^i\, d\theta^j$. This is why:

- The **Cramér–Rao bound** says no estimator can beat the geometric resolution of the manifold.
- The **Fisher metric is unique** (Chentsov's theorem): it is the only Riemannian metric on probability simplices that is monotone under coarse-graining.
- The **KL divergence** is the geodesic potential: $D_{\mathrm{KL}}(p_\theta \| p_{\theta+\varepsilon v}) = \frac{1}{2}\varepsilon^2 g_\theta(v,v) + O(\varepsilon^3)$.

### Why quantum mechanics?

A quantum measurement on a state $\psi$ produces a classical probability distribution over outcomes. Varying $\psi$ traces out a family of distributions — a statistical manifold. The Fisher metric on this manifold inherits the geometry of Hilbert space, but with a twist: the **complex structure** of Hilbert space splits the Fisher information into two pieces.

| | **Riemannian** ($g$) | **Symplectic** ($\omega$) |
|---|---|---|
| **Operator** | Anticommutator $\frac{1}{2}\lbrace L_i, L_j\rbrace$ | Commutator $\frac{1}{2i}[L_i, L_j]$ |
| **Inner product** | $\mathrm{Re}\langle\tilde{A}\psi, \tilde{B}\psi\rangle$ | $\mathrm{Im}\langle\tilde{A}\psi, \tilde{B}\psi\rangle$ |
| **Uncertainty bound** | Covariance (Cramér–Rao) | Commutator (Robertson) |
| **Classical limit** | Survives | Vanishes |

The symplectic form $\omega$ is invisible classically — it is the geometric signature of quantum mechanics. The Schrödinger uncertainty relation is the statement that **both** contributions must be accounted for. The Kähler structure $G^{\mathrm{RLD}} = g + i\omega$ packages them into a single complex-valued metric whose real part is the Riemannian geometry of estimation and whose imaginary part is the symplectic geometry of noncommutativity.

### The factor of 4

The quantum Fisher information for pure states is $I(\theta) = 4\,\mathrm{Var}_\psi(A)$ — four times the classical formula. The factor of 4 arises because quantum states live in a *complex* Hilbert space: differentiating $|\langle b | e^{-i\theta A} | \psi \rangle|^2$ in $\theta$ produces a factor of 2 from the absolute-value square and another from $|f|^2 = f\bar{f}$. This is the Braunstein–Caves normalization, and it propagates throughout the bridge: $g_{ij} = 4\,\mathrm{Cov}(O_i, O_j)$ and $\omega_{ij} = 2\,\mathrm{Im}\langle\psi, [O_i, O_j]\psi\rangle$.


---

## Design Decisions

**Parameter space.** Concretely modeled as an open subset of `EuclideanSpace ℝ (Fin n)` rather than an abstract smooth manifold. This keeps proofs grounded in Mathlib's `ContDiffOn`, `fderiv`, and inner-product infrastructure. Generalization to abstract manifolds via charts is a future layer.

**Density codomain.** Real-valued (`ℝ`), not `ℝ≥0∞`. The calculus layer — `log`, `fderiv`, bilinear forms — is native to `ℝ`. The bridge to measure theory uses `ENNReal.ofReal`, and nonnegativity is a carried field.

**Layered regularity.** Following Mathlib's typeclass pattern:
- `StatisticalModel` — smoothness and measurability only
- `RegularStatisticalModel` — adds dominated-convergence bounds
- `SmoothFisherModel` — adds smooth dependence of Fisher entries on $\theta$
- `StatisticalManifold` — the full package with global score-injectivity
- `RLDFisherModel` — extends with symplectic form and RLD Cauchy–Schwarz

Each theorem states exactly the regularity it needs.

**Axiomatize, then discharge.** The quantum bridge follows a two-phase design. Phase A (`QuantumPhaseModel`, `RLDFisherModel`) axiomatizes the physical identities as structure fields. Phase B (`QuantumFisherModel`) constructs instances that discharge the axioms from Hilbert-space data. This cleanly separates the geometric content (which is universal) from the quantum content (which is model-specific).

**Unconditional vs. conditional results.** Algebraic properties (symmetry, positive semidefiniteness) hold unconditionally. Results needing finite Fisher entries carry explicit `ScoreSqIntegrableModel θ` hypotheses.


---

## Mathlib Dependencies

- **Measure theory & integration**: `MeasureSpace`, `WithDensity`, `Integrable`, `SigmaFinite`, `IsProbabilityMeasure`, Bochner integral, `hasFDerivAt_integral_of_dominated_of_fderiv_le`
- **Analysis & calculus**: `ContDiffOn`, `fderiv`, `ContinuousLinearMap`, `EuclideanSpace`, `InnerProductSpace`
- **Linear algebra**: `LinearMap.BilinForm`, `Submodule`, `Submodule.iInf`
- **Special functions**: `Real.log`, `Real.exp`, `Real.sqrt`, `Complex.normSq`


---

## Building

Requires Lean 4 and Mathlib4. With [elan](https://github.com/leanprover/elan) installed:

```bash
lake build LogosLibrary.InformationGeometry
lake build LogosLibrary.QuantumMechanics
```


---

## Future Work

- **`KLDivergence.lean`** — Fisher metric as Hessian of KL divergence: $D_{\mathrm{KL}}(p_\theta \| p_{\theta + \varepsilon v}) = \frac{1}{2}\varepsilon^2 g_\theta(v,v) + O(\varepsilon^3)$
- **`Connections.lean`** — The $\alpha$-connections and dually flat structure of exponential/mixture families
- **`Chentsov.lean`** — Uniqueness of the Fisher metric under sufficient statistics
- **`ConnesCocycle.lean`** — The Connes cocycle $(D\rho : D\sigma)_t = \rho^{it}\sigma^{-it}$ for density matrices, relative entropy via its derivative, and the RLD metric as the Hessian of relative entropy
- **`Tsirelson.lean`** — CHSH bound $|S| \leq 2\sqrt{2}$ from the Kähler Cramér–Rao bound on the singlet manifold
- **Exponential families** — Concrete instances; dual flatness; efficiency of the MLE


---

## References

### Information Geometry
- S. Amari, *Information Geometry and Its Applications*, Springer, 2016.
- S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
- N. N. Čencov, *Statistical Decision Rules and Optimal Inference*, AMS, 1982.
- C. R. Rao, "Information and accuracy attainable in the estimation of statistical parameters", *Bull. Calcutta Math. Soc.* **37** (1945), 81–91.

### Quantum Estimation and Fisher Information
- S. L. Braunstein, C. M. Caves, "Statistical distance and the geometry of quantum states", *Phys. Rev. Lett.* **72** (1994), 3439–3443.
- C. W. Helstrom, *Quantum Detection and Estimation Theory*, Academic Press, 1976.
- A. S. Holevo, *Probabilistic and Statistical Aspects of Quantum Theory*, North-Holland, 1982.
- D. Petz, "Monotone metrics on matrix spaces", *Linear Algebra Appl.* **244** (1996), 81–96.

### Uncertainty Relations
- W. Heisenberg, "Über den anschaulichen Inhalt der quantentheoretischen Kinematik und Mechanik", *Z. Phys.* **43** (1927), 172–198.
- H. P. Robertson, "The uncertainty principle", *Phys. Rev.* **34** (1929), 163–164.
- E. Schrödinger, "Zum Heisenbergschen Unschärfeprinzip", *Sitzungsber. Preuss. Akad. Wiss.* (1930), 296–303.

### Kähler Geometry of Quantum States
- A. Ashtekar, T. A. Schilling, "Geometrical formulation of quantum mechanics", in *On Einstein's Path* (1999), 23–65.
- D. C. Brody, L. P. Hughston, "Geometric quantum mechanics", *J. Geom. Phys.* **38** (2001), 19–53.
- J. P. Provost, G. Vallee, "Riemannian structure on manifolds of quantum states", *Comm. Math. Phys.* **76** (1980), 289–301.


---

## License

Apache 2.0. See [LICENSE](LICENSE).

## Authors

Adam Bornemann
