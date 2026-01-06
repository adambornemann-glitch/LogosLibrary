# Connes' Spectral Triples.  The skelington.

**Layer 0: Algebraic Foundations**

```
Foundations/
├── Quaternions/
│   ├── Basic.lean           -- ℍ as ℝ-algebra
│   ├── Conjugation.lean     -- q ↦ q*
│   ├── Embedding.lean       -- ℍ ↪ M₂(ℂ)
│   └── Automorphisms.lean   -- Aut(ℍ) ≅ SO(3)
│
├── MatrixAlgebras/
│   ├── Basic.lean           -- M_n(ℂ) structure
│   ├── Trace.lean           -- Tr properties
│   ├── Adjoint.lean         -- A ↦ A†
│   └── Unitaries.lean       -- U(n), SU(n)
│
├── DirectSums/
│   ├── Algebras.lean        -- A ⊕ B as algebra
│   ├── Representations.lean -- Reps of A ⊕ B
│   └── Projections.lean     -- Projection to factors
│
└── GradedStructures/
    ├── Z2Grading.lean       -- Even/odd decomposition
    └── SuperAlgebras.lean   -- Graded commutators
```

Estimated: ~40 lemmas.

**Layer 1: Finite Spectral Triples**

```
FiniteTriples/
├── Definition.lean
│   -- structure FiniteSpectralTriple where
│   --   A : Type*            -- algebra
│   --   H : Type*            -- Hilbert space (finite-dim)
│   --   D : H →ₗ[ℂ] H        -- Dirac operator
│   --   J : H →ₐ[ℂ] H        -- antilinear, J² = ε
│   --   γ : H →ₗ[ℂ] H        -- grading, γ² = 1
│
├── Axioms/
│   ├── Reality.lean         -- J² = ε, JD = ε'DJ, Jγ = ε''γJ
│   ├── FirstOrder.lean      -- [[D, a], JbJ⁻¹] = 0
│   ├── Grading.lean         -- γ² = 1, γD = -Dγ
│   └── Compatibility.lean   -- All signs consistent (KO-dim)
│
├── KODimension.lean         -- The mod 8 structure
│   -- Table of (ε, ε', ε'') for each dimension
│
└── Examples/
    ├── Point.lean           -- A = ℂ, trivial triple
    ├── TwoPoint.lean        -- A = ℂ ⊕ ℂ
    └── Quaternionic.lean    -- A = ℍ
```

Estimated: ~50 lemmas.

**Layer 2: The Standard Model Algebra**

```
StandardModel/
├── Algebra/
│   ├── Definition.lean      -- A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)
│   ├── Dimension.lean       -- dim_ℝ(A_F) = 2 + 4 + 18 = 24
│   ├── Center.lean          -- Z(A_F) = ℂ ⊕ ℂ ⊕ ℂ
│   └── Involution.lean      -- The *-structure
│
├── HilbertSpace/
│   ├── Definition.lean      -- H_F = ℂ⁹⁶
│   ├── Decomposition.lean   -- 96 = 3 × 32 (generations)
│   ├── Representation.lean  -- How A_F acts on H_F
│   └── Fermions.lean        -- Matching to SM fermions
│       -- Left quarks, right quarks
│       -- Left leptons, right leptons
│       -- Color indices
│
├── DiracOperator/
│   ├── Definition.lean      -- D_F as 96×96 matrix
│   ├── Yukawa.lean          -- Entries are Yukawa couplings
│   ├── Symmetry.lean        -- D_F = D_F†
│   └── Eigenvalues.lean     -- Spectrum = fermion masses
│
├── Reality/
│   ├── JOperator.lean       -- J : H_F → H_F antilinear
│   ├── ChargeConjugation.lean -- Physical interpretation
│   └── Verification.lean    -- Check J² = 1, JD = DJ
│
└── Grading/
    ├── Chirality.lean       -- γ = chirality operator
    ├── LeftRight.lean       -- Left/right decomposition
    └── Verification.lean    -- Check γ² = 1, γD = -Dγ
```

Estimated: ~80 lemmas. 

**Layer 3: Emergence of Gauge Group**

```
GaugeGroup/
├── Automorphisms/
│   ├── Definition.lean      -- Aut(A_F)
│   ├── Unitaries.lean       -- U(A_F) = U(1) × U(1) × U(2) × U(3)
│   └── Inner.lean           -- Inn(A_F) ⊂ Aut(A_F)
│
├── Constraints/
│   ├── Unimodularity.lean   -- det = 1 condition
│   ├── RealStructure.lean   -- Commutes with J
│   └── Combined.lean        -- Both constraints together
│
├── Emergence/
│   ├── GaugeGroup.lean      
│   -- THEOREM: Aut_J(A_F) ∩ SU = SU(3) × SU(2) × U(1)
│   -- This is the main result of this layer
│   ├── ColorSU3.lean        -- SU(3) from M₃(ℂ)
│   ├── WeakSU2.lean         -- SU(2) from ℍ
│   └── Hypercharge.lean     -- U(1) from the traces
│
└── Representations/
    ├── FermionReps.lean     -- How gauge group acts on H_F
    ├── LeftQuarks.lean      -- (3, 2, 1/6)
    ├── RightUpQuark.lean    -- (3, 1, 2/3)
    ├── RightDownQuark.lean  -- (3, 1, -1/3)
    ├── LeftLeptons.lean     -- (1, 2, -1/2)
    ├── RightElectron.lean   -- (1, 1, -1)
    ├── RightNeutrino.lean   -- (1, 1, 0)
    └── Verification.lean    -- Match to SM exactly
```

Estimated: ~70 lemmas. The theorem that says SU(3) × SU(2) × U(1) *emerges* from the algebra structure.

**Layer 4: The Higgs**

```
Higgs/
├── InnerFluctuations/
│   ├── Definition.lean      -- D ↦ D + A + JAJ*
│   ├── GaugeFields.lean     -- A from manifold directions
│   └── FiniteFluctuation.lean -- A from internal directions
│
├── HiggsField/
│   ├── Emergence.lean       
│   -- THEOREM: The finite fluctuation IS a Higgs doublet
│   ├── Doublet.lean         -- SU(2) doublet structure
│   ├── Hypercharge.lean     -- Y = 1/2
│   └── Transformation.lean  -- How it transforms under gauge
│
└── Verification/
    ├── Degrees.lean         -- 4 real = 2 complex = 1 doublet
    └── MatchesSM.lean       -- Exactly the SM Higgs
```

Estimated: ~40 lemmas. Another major result: the Higgs is not input, it is *forced* by the geometry.

**Layer 5: The Spectral Action (Finite Part)**

```
SpectralAction/
├── Finite/
│   ├── Definition.lean      -- S_F = Tr(f(D_F/Λ))
│   ├── Expansion.lean       -- For finite dims, just polynomial
│   └── Computation.lean     -- Actually compute it
│
├── HiggsPotential/
│   ├── Emergence.lean       -- V(H) from spectral action
│   ├── QuarticTerm.lean     -- λ|H|⁴ term
│   ├── MassTerm.lean        -- μ²|H|² term
│   └── Relation.lean        -- λ, μ related to Yukawas
│
├── YukawaCouplings/
│   ├── Definition.lean      -- From D_F entries
│   ├── Masses.lean          -- m_f = y_f v/√2
│   └── CKMMatrix.lean       -- Mixing from off-diagonals
│
└── GaugeKinetic/
    ├── FieldStrength.lean   -- F_μν terms
    └── Normalization.lean   -- Coupling constants
```

Estimated: ~60 lemmas.

**Total for finite spectral Standard Model: ~340 lemmas.**

