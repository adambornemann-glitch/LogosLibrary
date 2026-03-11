# Economic Gauge Theory

## Disclaimer

All errors and misinterpretations are solely the responsibility of the
author (Adam Bornemann). This is an independent project. It has not been
reviewed or endorsed by Pia Malaney, or any other physicist or
mathematician whose work is referenced.

## The Malaney–Weinstein Connection, Formalized

This module formalizes and extends the gauge-theoretic approach to
economic index numbers introduced by Pia Malaney in her 1996 Harvard
thesis *The Index Number Problem: A Differential Geometric Approach*
(advisor: Eric Maskin; co-authored with Eric Weinstein).

The central result is the **Classification Theorem**: the topological
type of an economy—the irreducible obstruction to consistent price
comparison—is a single integer, the first Chern number c₁ ∈ ℤ of
the purchasing power bundle.

---

## The Problem

Economists have struggled for over a century with the *index number
problem*: given prices and quantities at two different times, what is
the "correct" price index comparing them?  Laspeyres, Paasche, Fisher,
Törnqvist, and others give different answers.  No canonical choice
exists in general.

Malaney and Weinstein showed that this is not a deficiency of the
indices.  It is a *geometric* phenomenon.  The failure of different
price indices to agree is the *curvature* of a gauge connection on
a fiber bundle over the space of economic states.

---

## The Construction

### The Gauge Symmetry

An economy with n goods has prices p = (p₁, …, pₙ) and quantities
q = (q₁, …, qₙ).  The **numéraire freedom**—the arbitrary choice
of unit of account—is a gauge symmetry: rescaling all prices by a
positive constant λ does not change the economic content.  This is a
U(1) symmetry (the positive reals under multiplication are isomorphic
to U(1) via the exponential map).

### The Connection

The Malaney–Weinstein connection 1-form is:

    A = Σᵢ wᵢ · d(log pᵢ)

where wᵢ = pᵢqᵢ / Σⱼ pⱼqⱼ are the expenditure shares.  The
covariant derivative:

    (D/Dt) S = (d/dt) S − (d/dt)(log P) · S

says that a salary S has **constant purchasing power** if and only if
it grows at the Divisia price index rate.  This is parallel transport.

### The Curvature

The curvature 2-form F = dA = Σᵢ dwᵢ ∧ d(log pᵢ) measures path
dependence of the Divisia index.

- **F = 0** (flat): all price indices agree, the index number problem
  has a solution, and the purchasing power bundle is trivial.

- **F ≠ 0** (curved): indices *must* disagree—this is topologically
  forced—and the Divisia index around a closed loop is the *holonomy*
  of the connection.

### The Chern Number

For a 3-good economy, the expenditure shares live on the simplex Δ².
The square-root embedding ξᵢ = √wᵢ maps Δ² isometrically (up to a
factor of 4) onto S², the Bloch sphere boundary.  The MW connection
lives on a U(1) bundle over S².  Such bundles are classified by a
single integer c₁ ∈ ℤ, the first Chern number:

    c₁ = (1/2π) ∫_{S²} F

This integer is computable from price data, topologically stable (it
cannot change under continuous deformations), and quantized (if c₁ ≠ 0,
then |c₁| ≥ 1; there is no "slightly inconsistent" economy).

---

## The Pipeline

The full classification pipeline, from raw data to a topological
invariant, proceeds in seven stages:

```
1. DATA         Observe prices p(t) and quantities q(t)
2. SHARES       Compute wᵢ = pᵢqᵢ / Σ pⱼqⱼ (sum to 1)
3. EMBEDDING    Map ξᵢ = √wᵢ onto S² (Fisher = Fubini–Study)
4. CONNECTION   MW 1-form A = Σ wᵢ d(log pᵢ)
5. CURVATURE    F = dA = Σ dwᵢ ∧ d(log pᵢ)
6. INTEGRATION  c₁ = (1/2π) ∫ F   (Chern–Weil)
7. OUTPUT       c₁ ∈ ℤ — one number classifying the economy
```

Stages 1–5 are continuous operations.  Stage 6 is topological
quantization: the Chern–Weil theorem forces the integral to be an
integer.  This is the economic analogue of charge quantization in
electrodynamics.

---

## What Is Formalized

### Machine-Checked (zero axioms in these proofs)

- **Expenditure shares** sum to 1 and are nonneg for positive prices
  and quantities (`expenditureShare_sum_one`).

- **The MW connection form** A = Σ wᵢ (ṗᵢ/pᵢ) and its expression
  in log-price coordinates.

- **Gauge transformation**: under numéraire change p → λp, the
  connection transforms as A → A + dΛ, exactly as in electrodynamics
  (`connectionForm_gauge_transform`).

- **The covariant derivative** (D/Dt)f = ḟ − A·f and its **gauge
  covariance**: (D/Dt)(λf) = λ·(D/Dt)f (`covariantDeriv_gauge_covariant`).

- **Parallel transport** = constant purchasing power: (D/Dt)S = 0
  iff ṡ/S equals the Divisia growth rate (`parallelTransport_growth_rate`).

- **Self-financing portfolios** are parallel-transported
  (`selfFinancing_is_parallel`).

- **Curvature** F = Σ dwᵢ ∧ d(log pᵢ) is antisymmetric, gauge-invariant,
  and vanishes for constant shares (Cobb–Douglas) or proportional
  price changes (`curvature_gauge_invariant`, `curvature_zero_of_constant_shares`).

- **No arbitrage ⟺ zero curvature** (`noArbitrage`).

- **Fisher metric on the share simplex** g(v,v) = Σ vᵢ²/wᵢ, its
  positivity, and the spherical form g = 4 Σ (dξᵢ)² showing it equals
  the round metric on S² (`fisherMetricSimplex_eq_spherical`).

- **Bloch ball geometry**: density matrix parameterization, eigenvalues,
  purity, pure/mixed trichotomy, Bures metric at the origin and its
  positivity.

- **The simplex-to-Bloch embedding** ξᵢ = √wᵢ lands on S²
  (`sqrtEmbed_on_sphere`).

- **Fisher = Fubini–Study** on the Bloch sphere boundary, with the
  Braunstein–Caves factor of 4 (`fisher_eq_fubiniStudy`).

- **Unique 3D state space**: the qubit (n=2) is the only density
  matrix system whose state space is 3-dimensional
  (`unique_3d_state_space`).

- **KU vs KO information loss**: distinct Chern numbers can collapse
  to the same Stiefel–Whitney class under the forgetful map from
  complex to real K-theory (`information_loss`).

- **The Classification Theorem**: economies are classified by c₁ ∈ ℤ,
  the index number problem has a solution iff c₁ = 0, and the minimum
  nontrivial obstruction is |c₁| = 1 (`grand_unified`).

### Axiomatized (awaiting upstream infrastructure)

- **Chern–Weil integral**: (1/2π) ∫_{S²} F ∈ ℤ.  This requires smooth
  manifold integration and the Chern–Weil homomorphism, both beyond
  current Mathlib scope.  It is the single load-bearing axiom in the
  economic pipeline.  All other results are either fully proved or
  proved conditional on this step.

---

## What Is New (Beyond Malaney–Weinstein 1996)

The original Malaney–Weinstein thesis established the connection, the
covariant derivative, and the identification of the Divisia index as
its holonomy.  This formalization extends their work in several
directions:

1. **The Bloch ball identification.**  The expenditure share simplex,
   via the square-root embedding, maps isometrically into the Bloch
   sphere S².  The Fisher metric on shares equals the Fubini–Study
   metric (quantum Fisher information) with the Braunstein–Caves factor.
   This embeds the MW construction into quantum information geometry.

2. **Topological classification by Chern number.**  U(1) bundles over
   S² are classified by c₁ ∈ ℤ.  The MW curvature integrates to an
   integer, quantizing the failure of price comparison.

3. **The Bott periodicity connection.**  The Chern number lives in
   KU(S²) = ℤ (complex K-theory, period 2).  The forgetful map to
   KO(S²) = ℤ/2 (real K-theory, period 8) loses information: the
   full integer reduces to an orientation bit.

4. **Machine verification.**  The gauge transformation law, covariance
   of the derivative, the Fisher metric calculation, and the uniqueness
   of the 3D quantum state space are Lean 4 theorems, not calculations
   on paper.

---

## File Structure

```
EconomicGauge/
├── MalaneyWeinstein.lean    The MW connection, covariant derivative,
│                            Divisia index, curvature, arbitrage,
│                            Fisher metric on the simplex
│
├── BlochBridge.lean         Bloch ball, density matrices, Bures metric,
│                            simplex-to-Bloch embedding,
│                            Fisher = Fubini–Study, dimensional
│                            coincidence, algebra/commutant
│
├── ChernBridge.lean         Purchasing power bundle, topological charge,
│                            quantization, Bott periodicity bridge,
│                            KU vs KO information loss
│
└── Classification.lean      Full pipeline, classification theorem,
                             economic meaning of c₁, index number
                             resolution, phase transitions,
                             grand unified theorem
```

### Upstream Dependencies

- `InformationGeometry/Fisher/StatisticalManifold` — Fisher metric
  and statistical manifold infrastructure
- `CommonResources/HopfTower/` — Hopf fibration and Chern class
  foundations
- `CommonResources/CliffordPeriodicity/Clock` — Bott periodicity table
- `QuantumMechanics/ModularTheory` — Tomita–Takesaki, KMS conditions

### Downstream: The Quantum–Geometric Bridge

The `InformationGeometry/` module independently establishes that the
Schrödinger uncertainty relation *is* the RLD Cramér–Rao bound
(see `QuantumFisherModel.lean`).  This means the Fisher metric on
the economic state space is not merely analogous to the quantum Fisher
information—it is the *same* mathematical object, derived from the
same Cauchy–Schwarz inequality in Hilbert space.  The MW connection
sits on top of this metric.

---

## How to Read This

**If you are an economist**: start with `MalaneyWeinstein.lean`.
The connection form, covariant derivative, and Divisia index are the
economic core.  The gauge transformation theorem (Part III) is the
formal statement that numéraire freedom is a symmetry.  The curvature
section (Part VI) is the formal statement of the index number problem
as a geometric phenomenon.

**If you are a mathematician or physicist**: start with
`BlochBridge.lean` and `ChernBridge.lean`.  The embedding of the
share simplex into S² via the square-root map, the identification
Fisher = Fubini–Study, and the Chern number classification are the
mathematical substance.  The connection to Bott periodicity and K-theory
is in `ChernBridge.lean` §II and `Classification.lean` §V.

**If you want the one-sentence summary**: *The complete topological
information about any economy is a single integer.*

---

## References

### Primary

- P. Malaney, *The Index Number Problem: A Differential Geometric
  Approach*, PhD thesis, Harvard University, 1996.

- P. Malaney and E. Weinstein, "An Extension of Intertemporal Ordinal
  Welfare to Changing Tastes: Economics as Gauge Theory," draft for
  University of Chicago Money and Banking Workshop, 2020.

### The Arbitrage Extension

- S. E. Vázquez and S. Farinelli, "Gauge Invariance, Geometry and
  Arbitrage," *Journal of Investment Strategies* 1(2), 23–66, 2012.

### Information Geometry

- S. L. Braunstein and C. M. Caves, "Statistical distance and the
  geometry of quantum states," *Phys. Rev. Lett.* 72 (1994), 3439.

- D. Petz, "Monotone metrics on matrix spaces," *Linear Algebra Appl.*
  244 (1996), 81–96.

- N. N. Chentsov, *Statistical Decision Rules and Optimal Inference*,
  AMS, 1982.

### Context

- L. Smolin, "Time and symmetry in models of economic markets,"
  arXiv:0902.4274, 2009.

- J. O. Weatherall, *The Physics of Wall Street*, Houghton Mifflin
  Harcourt, 2013.  (Chapter 8 and Epilogue cover the Malaney–Weinstein
  program.)

---

## Axiom Budget

**1 axiom** in the economic gauge pipeline proper: `chernWeil_integral`
(the Chern–Weil theorem for U(1) bundles over S²).

All other results are machine-checked.  The Chern–Weil gap is a
limitation of current Lean/Mathlib infrastructure for smooth manifold
integration, not a mathematical uncertainty.