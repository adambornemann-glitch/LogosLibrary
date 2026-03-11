/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/SchrodingerRLD.lean
-/
import LogosLibrary.InformationGeometry.Fisher.FisherMetric
import LogosLibrary.InformationGeometry.Fisher.StatisticalManifold
/-!
# RLD Fisher Information and the Schrödinger–Cramér–Rao Bound

The **Right Logarithmic Derivative** (RLD) Fisher information is a
complex-valued extension of the (real, symmetric) SLD Fisher information
matrix.  It decomposes into a **Riemannian** part — the ordinary Fisher
metric `g` — and a **symplectic** part — an antisymmetric 2-form `ω`:

  `G^RLD_{ij}(θ) = g_{ij}(θ) + i · ω_{ij}(θ)`

In quantum statistics, `g` is the SLD (Symmetric Logarithmic Derivative)
metric and `ω` is the commutator form.  Classically, `ω = 0` and
`G^RLD = G^SLD` (Chentsov's theorem).

The central result is the **Schrödinger–Cramér–Rao bound**:

  `g_{ii} · g_{jj} ≥ g_{ij}² + ω_{ij}²`

This is the information-geometric form of Schrödinger's uncertainty
relation (1930).  It strengthens the ordinary Cauchy–Schwarz/Cramér–Rao
bound `g_{ii} · g_{jj} ≥ g_{ij}²` by the symplectic term `ω_{ij}²`.

## Mathematical structure

The RLD Cauchy–Schwarz condition

  `g(v,w)² + ω(v,w)² ≤ g(v,v) · g(w,w)`

is equivalent to the complex Hermitian matrix `G^RLD` being positive
semidefinite.  In the quantum case this follows from the Gram matrix
structure `G^RLD_{ij} = Tr(ρ R_i† R_j)`.  We carry it as an axiom
(field of `RLDFisherModel`) to be discharged from quantum data in
the bridge file.

The Pythagorean decomposition `|G^RLD(v,w)|² = g(v,w)² + ω(v,w)²`
is the geometric reason the two terms in Schrödinger's bound are
"orthogonal" — they are the real and imaginary parts of a single
complex inner product.

## Main definitions

* `RLDFisherModel` — a `RegularStatisticalModel` extended with a
  symplectic form `ω` and the RLD Cauchy–Schwarz condition.
* `sldBilin` — the SLD bilinear form `g(v,w) = ∑_{ij} vᵢ wⱼ g_{ij}`.
* `symplecticBilin` — the symplectic form `ω(v,w) = ∑_{ij} vᵢ wⱼ ω_{ij}`.
* `rldBilin` — the complex RLD form `G^RLD(v,w) = g(v,w) + i · ω(v,w)`.
* `rldMatrix` — the complex RLD matrix `G^RLD_{ij} = g_{ij} + i · ω_{ij}`.

## Main results

* `symplecticBilin_antisymm` — `ω(v,w) = -ω(w,v)`.
* `symplecticBilin_self` — `ω(v,v) = 0`.
* `rldMatrix_hermitian` — `G^RLD_{ji} = conj(G^RLD_{ij})`.
* `rld_pythagorean` — `|G^RLD(v,w)|² = g(v,w)² + ω(v,w)²`.
* `schrodinger_bilin_bound` — `g(v,v) · g(w,w) ≥ g(v,w)² + ω(v,w)²`.
* `schrodinger_fisher_bound` — `g_{ii} · g_{jj} ≥ g_{ij}² + ω_{ij}²`.
* `robertson_fisher_bound` — `g_{ii} · g_{jj} ≥ ω_{ij}²`
  (Robertson as a corollary of Schrödinger).
* `sld_cauchy_schwarz` — `g(v,v) · g(w,w) ≥ g(v,w)²`
  (standard Cauchy–Schwarz as a corollary).

## Design notes

The RLD Cauchy–Schwarz condition is axiomatised rather than derived,
because its proof requires the Gram matrix structure of the RLD —
which is quantum-mechanical content.  The bridge file
`QuantumMechanics.SchrodingerCR` will discharge it from Hilbert-space
Cauchy–Schwarz applied to the shifted observables `Ãψ` and `B̃ψ`.

The `sldBilin` definition duplicates the Fisher bilinear form in matrix
notation.  This is intentional: it keeps the RLD file self-contained
at the matrix level, without depending on the integral representation
in `FisherInformation.lean`.

## References

* D. Petz, "Monotone metrics on matrix spaces",
  *Linear Algebra Appl.* **244** (1996), 81–96.
* A. S. Holevo, *Probabilistic and Statistical Aspects of Quantum
  Theory*, North-Holland, 1982. — Introduces the RLD bound.
* S. L. Braunstein, C. M. Caves, "Statistical distance and the
  geometry of quantum states", *Phys. Rev. Lett.* **72** (1994),
  3439–3443. — Quantum Fisher information = max classical Fisher.
* E. Schrödinger, "Zum Heisenbergschen Unschärfeprinzip",
  *Sitzungsber. Preuss. Akad. Wiss.* (1930), 296–303.

## Tags

RLD Fisher information, symplectic form, Schrödinger inequality,
Cramér–Rao, Kähler, monotone metric
-/

noncomputable section

open MeasureTheory ENNReal Real Set Filter Finset

open scoped Topology

namespace InformationGeometry

open RegularStatisticalModel

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-! ### Bilinear sum evaluation on standard basis vectors -/

/-- Evaluating a bilinear sum `∑_{ij} eₐ(i) eᵦ(j) f(i,j)` on standard
basis vectors yields the matrix entry `f(a,b)`. -/
lemma bilinSum_single (f : Fin n → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin n, ∑ j : Fin n,
      (EuclideanSpace.single a (1 : ℝ) : ParamSpace n) i *
      (EuclideanSpace.single b (1 : ℝ) : ParamSpace n) j *
      f i j = f a b := by
  simp only [EuclideanSpace.single_apply]
  simp only [ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-! ### The RLD Fisher model -/

/-- An `RLDFisherModel` extends a `RegularStatisticalModel` with a
**symplectic form** `ω` on the parameter space and the **RLD Cauchy–Schwarz
condition** relating the SLD metric `g` and the symplectic form `ω`.

The symplectic form is the imaginary part of the RLD Fisher information:
`G^RLD_{ij} = g_{ij} + i · ω_{ij}`.

The RLD Cauchy–Schwarz condition states that for all real tangent
vectors `v` and `w`:

  `g(v,w)² + ω(v,w)² ≤ g(v,v) · g(w,w)`

This is equivalent to the complex Hermitian matrix `G^RLD` being
positive semidefinite.  In the quantum setting, this follows from the
Gram matrix structure of the RLD: `G^RLD_{ij} = Tr(ρ R_i† R_j)`. -/
structure RLDFisherModel (n : ℕ) (Ω : Type*)
    [MeasurableSpace Ω] extends
    RegularStatisticalModel n Ω where
  /-- The symplectic form at each parameter: `ω(θ, i, j)`. -/
  symplecticForm : ParamSpace n → Fin n → Fin n → ℝ
  /-- Antisymmetry: `ω_{ij} = -ω_{ji}`. -/
  symplectic_antisymm :
    ∀ θ ∈ paramDomain, ∀ i j : Fin n,
      symplecticForm θ i j = -symplecticForm θ j i
  /-- **RLD Cauchy–Schwarz condition.**

  For all real vectors `v`, `w` and all parameters `θ ∈ Θ`:

    `g(v,w)² + ω(v,w)² ≤ g(v,v) · g(w,w)`

  where `g(v,w) = ∑_{ij} vᵢ wⱼ g_{ij}` and `ω(v,w) = ∑_{ij} vᵢ wⱼ ω_{ij}`.

  This is Cauchy–Schwarz for the complex Hermitian form `G^RLD`
  restricted to real vectors.  It is equivalent to `G^RLD` being
  positive semidefinite (given that `g` is already positive definite). -/
  rld_cauchy_schwarz :
    ∀ θ ∈ paramDomain,
    ∀ v w : ParamSpace n,
      (∑ i : Fin n, ∑ j : Fin n,
        v i * w j * toRegularStatisticalModel.fisherMatrix θ i j) ^ 2 +
      (∑ i : Fin n, ∑ j : Fin n,
        v i * w j * symplecticForm θ i j) ^ 2 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        v i * v j * toRegularStatisticalModel.fisherMatrix θ i j) *
      (∑ i : Fin n, ∑ j : Fin n,
        w i * w j * toRegularStatisticalModel.fisherMatrix θ i j)

namespace RLDFisherModel

variable (R : RLDFisherModel n Ω)

/-! ### Bilinear form abbreviations -/

/-- The **SLD bilinear form** (matrix notation):
  `g(v, w) = ∑_{ij} vᵢ wⱼ g_{ij}(θ)`.

This is the Fisher inner product in coordinate form. -/
def sldBilin (θ : ParamSpace n) (v w : ParamSpace n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * w j * R.fisherMatrix θ i j

/-- The **symplectic bilinear form**:
  `ω(v, w) = ∑_{ij} vᵢ wⱼ ω_{ij}(θ)`. -/
def symplecticBilin (θ : ParamSpace n)
    (v w : ParamSpace n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    v i * w j * R.symplecticForm θ i j

/-! ### Properties of the symplectic form -/

/-- The symplectic bilinear form is antisymmetric:
  `ω(v, w) = -ω(w, v)`. -/
theorem symplecticBilin_antisymm {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v w : ParamSpace n) :
    R.symplecticBilin θ v w = -R.symplecticBilin θ w v := by
  simp only [symplecticBilin]
  -- Replace ω(i,j) → -ω(j,i) on the LHS only
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [R.symplectic_antisymm θ hθ i j, mul_neg]
  -- Pull out the negation: ∑ᵢ ∑ⱼ -(vᵢwⱼω(j,i)) = -(∑ᵢⱼ vᵢwⱼω(j,i))
  simp only [Finset.sum_neg_distrib]
  -- Cancel the outer negation on both sides
  congr 1
  -- Swap summation order and rename
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j; ring

/-- The symplectic form vanishes on the diagonal: `ω(v, v) = 0`.

This is an immediate consequence of antisymmetry. -/
theorem symplecticBilin_self {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v : ParamSpace n) :
    R.symplecticBilin θ v v = 0 := by
  have h := R.symplecticBilin_antisymm hθ v v
  linarith

/-- The diagonal entries of the symplectic form vanish:
  `ω(θ, i, i) = 0`. -/
theorem symplecticForm_diag {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i : Fin n) :
    R.symplecticForm θ i i = 0 := by
  have h := R.symplectic_antisymm θ hθ i i
  linarith

/-! ### The complex RLD Fisher matrix -/

/-- The complex **RLD Fisher matrix** at `θ`:

  `G^RLD_{ij}(θ) = g_{ij}(θ) + i · ω_{ij}(θ)`

where `g` is the (real, symmetric) SLD Fisher matrix and `ω` is the
(real, antisymmetric) symplectic form. -/
def rldMatrix (θ : ParamSpace n) (i j : Fin n) : ℂ :=
  ⟨R.fisherMatrix θ i j, R.symplecticForm θ i j⟩

/-- The RLD matrix is Hermitian: `G^RLD_{ji} = conj(G^RLD_{ij})`.

This follows from `g` being symmetric and `ω` being antisymmetric:
the real part is preserved and the imaginary part flips sign. -/
theorem rldMatrix_hermitian {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i j : Fin n)
    (h_symm : R.fisherMatrix θ i j = R.fisherMatrix θ j i) :
    R.rldMatrix θ j i = starRingEnd ℂ (R.rldMatrix θ i j) := by
  apply Complex.ext
  · -- Real part: g_{ji} = g_{ij}
    simp only [rldMatrix, Complex.conj_re]
    exact h_symm.symm
  · -- Imaginary part: ω_{ji} = -ω_{ij}
    simp only [rldMatrix, Complex.conj_im]
    exact R.symplectic_antisymm θ hθ j i

/-- The diagonal entries of the RLD matrix are real:
  `Im(G^RLD_{ii}) = 0`. -/
theorem rldMatrix_diag_real {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i : Fin n) :
    (R.rldMatrix θ i i).im = 0 := by
  exact R.symplecticForm_diag hθ i

/-! ### The complex RLD bilinear form -/

/-- The complex **RLD bilinear form**:

  `G^RLD(v, w) = g(v, w) + i · ω(v, w)`

Its real part is the SLD (Riemannian) inner product; its imaginary
part is the symplectic pairing. -/
def rldBilin (θ : ParamSpace n) (v w : ParamSpace n) : ℂ :=
  ⟨R.sldBilin θ v w, R.symplecticBilin θ v w⟩

/-- The RLD form on the diagonal is real (since `ω(v,v) = 0`):
  `G^RLD(v, v) = g(v, v)`. -/
theorem rldBilin_self_real {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v : ParamSpace n) :
    (R.rldBilin θ v v).im = 0 :=
  R.symplecticBilin_self hθ v

/-! ### Pythagorean decomposition -/

/-- **Pythagorean decomposition** of the RLD norm-squared:

  `|G^RLD(v, w)|² = g(v, w)² + ω(v, w)²`

The squared modulus of the complex RLD pairing splits into the
squared Riemannian (SLD) component and the squared symplectic
component.  This is the geometric reason the Schrödinger bound
has two additive terms — they are "orthogonal" in the complex
plane. -/
theorem rld_pythagorean (θ : ParamSpace n)
    (v w : ParamSpace n) :
    Complex.normSq (R.rldBilin θ v w) =
    R.sldBilin θ v w ^ 2 +
    R.symplecticBilin θ v w ^ 2 := by
  simp only [rldBilin, Complex.normSq_apply]
  ring

/-! ### The Schrödinger–Cramér–Rao bound -/

/-- **Schrödinger–Cramér–Rao bound (bilinear form version).**

For all tangent vectors `v`, `w` at `θ`:

  `g(v,v) · g(w,w) ≥ g(v,w)² + ω(v,w)²`

The first term on the RHS is the squared covariance (Riemannian/SLD
contribution).  The second is the squared commutator expectation
(symplectic contribution).  Together they give Schrödinger's
inequality.

Dropping the symplectic term `ω(v,w)²` recovers the ordinary
Cauchy–Schwarz / Robertson bound `g(v,v) · g(w,w) ≥ g(v,w)²`.
Dropping the Riemannian term `g(v,w)²` recovers Robertson's
inequality in the form `g(v,v) · g(w,w) ≥ ω(v,w)²`. -/
theorem schrodinger_bilin_bound {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v w : ParamSpace n) :
    R.sldBilin θ v v * R.sldBilin θ w w ≥
    R.sldBilin θ v w ^ 2 +
    R.symplecticBilin θ v w ^ 2 :=
  R.rld_cauchy_schwarz θ hθ v w

/-- **Schrödinger–Cramér–Rao bound (matrix entry version).**

For any pair of indices `(i, j)`:

  `g_{ii}(θ) · g_{jj}(θ) ≥ g_{ij}(θ)² + ω_{ij}(θ)²`

Under the quantum bridge axioms (`g_{kk} = 4 Var(O_k)`,
`g_{ij} = 4 Cov(A,B)`, `ω_{ij} = 2 Im⟨ψ,[A,B]ψ⟩`), this yields:

  `Var(A) · Var(B) ≥ Cov(A,B)² + ¼ |⟨[A,B]⟩|²`

which is the Schrödinger uncertainty relation. -/
theorem schrodinger_fisher_bound {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i j : Fin n) :
    R.fisherMatrix θ i i * R.fisherMatrix θ j j ≥
    R.fisherMatrix θ i j ^ 2 +
    R.symplecticForm θ i j ^ 2 := by
  have h := R.schrodinger_bilin_bound hθ
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [sldBilin, symplecticBilin] at h
  rwa [bilinSum_single _ i i, bilinSum_single _ j j,
       bilinSum_single _ i j, bilinSum_single _ i j] at h

/-! ### Corollaries: Robertson and standard Cauchy–Schwarz -/

/-- **Robertson bound from Schrödinger (matrix level).**

Dropping the covariance term from the Schrödinger bound:

  `g_{ii} · g_{jj} ≥ ω_{ij}²`

Under the quantum bridge, this gives `Var(A) Var(B) ≥ ¼|⟨[A,B]⟩|²`,
i.e. the Robertson uncertainty relation. -/
theorem robertson_fisher_bound {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i j : Fin n) :
    R.fisherMatrix θ i i * R.fisherMatrix θ j j ≥
    R.symplecticForm θ i j ^ 2 := by
  have h := R.schrodinger_fisher_bound hθ i j
  linarith [sq_nonneg (R.fisherMatrix θ i j)]

/-- **Robertson bound from Schrödinger (bilinear form level).**

  `g(v,v) · g(w,w) ≥ ω(v,w)²` -/
theorem robertson_bilin_bound {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v w : ParamSpace n) :
    R.sldBilin θ v v * R.sldBilin θ w w ≥
    R.symplecticBilin θ v w ^ 2 := by
  have h := R.schrodinger_bilin_bound hθ v w
  linarith [sq_nonneg (R.sldBilin θ v w)]

/-- **Standard Cauchy–Schwarz for the SLD metric** as a corollary of
the Schrödinger bound.

  `g(v,v) · g(w,w) ≥ g(v,w)²`

This is the ordinary Cauchy–Schwarz inequality for the Fisher inner
product, obtained by dropping the symplectic term `ω(v,w)²` from the
Schrödinger bound. -/
theorem sld_cauchy_schwarz {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v w : ParamSpace n) :
    R.sldBilin θ v v * R.sldBilin θ w w ≥
    R.sldBilin θ v w ^ 2 := by
  have h := R.schrodinger_bilin_bound hθ v w
  linarith [sq_nonneg (R.symplecticBilin θ v w)]

/-- **Standard Cauchy–Schwarz (matrix level).**

  `g_{ii} · g_{jj} ≥ g_{ij}²` -/
theorem sld_cauchy_schwarz_matrix {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i j : Fin n) :
    R.fisherMatrix θ i i * R.fisherMatrix θ j j ≥
    R.fisherMatrix θ i j ^ 2 := by
  have h := R.schrodinger_fisher_bound hθ i j
  linarith [sq_nonneg (R.symplecticForm θ i j)]

/-! ### Norm-level bounds -/

/-- The norm of the RLD pairing is bounded by the geometric mean of
the SLD diagonal entries:

  `‖G^RLD(v, w)‖² ≤ g(v,v) · g(w,w)`

This is the Schrödinger bound rewritten using the Pythagorean
decomposition. -/
theorem rldBilin_normSq_le {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (v w : ParamSpace n) :
    Complex.normSq (R.rldBilin θ v w) ≤
    R.sldBilin θ v v * R.sldBilin θ w w := by
  rw [R.rld_pythagorean]
  exact R.schrodinger_bilin_bound hθ v w

/-! ### Relationship between sldBilin and fisherBilin

The `sldBilin` is defined as a matrix-level sum for self-containedness.
It agrees with the Fisher bilinear form from `FisherInformation.lean`
when the latter is expanded via `fisherBilin_eq_sum_fisherMatrix`. -/

/-- `sldBilin` on a standard basis vector pair yields the Fisher
matrix entry. -/
@[simp]
theorem sldBilin_single (θ : ParamSpace n) (i j : Fin n) :
    R.sldBilin θ (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) =
    R.fisherMatrix θ i j := by
  simp only [sldBilin]
  exact bilinSum_single _ i j

/-- `symplecticBilin` on a standard basis vector pair yields the
symplectic form entry. -/
@[simp]
theorem symplecticBilin_single (θ : ParamSpace n) (i j : Fin n) :
    R.symplecticBilin θ (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) =
    R.symplecticForm θ i j := by
  simp only [symplecticBilin]
  exact bilinSum_single _ i j

/-! ### Determinant form of the Schrödinger bound

For a 2×2 principal submatrix, the Schrödinger bound is equivalent
to the determinant of the RLD submatrix being nonnegative.  This
gives a clean characterisation of when the bound is tight. -/

/-- The Schrödinger bound is equivalent to the `2 × 2` RLD principal
minor being nonneg:

  `g_{ii} g_{jj} - g_{ij}² - ω_{ij}² ≥ 0`

This is `det(G^RLD|_{ij})` for the 2×2 Hermitian submatrix, and
equals zero iff the bound is saturated. -/
theorem schrodinger_det_form {θ : ParamSpace n}
    (hθ : θ ∈ R.paramDomain) (i j : Fin n) :
    0 ≤ R.fisherMatrix θ i i * R.fisherMatrix θ j j -
      R.fisherMatrix θ i j ^ 2 -
      R.symplecticForm θ i j ^ 2 := by
  linarith [R.schrodinger_fisher_bound hθ i j]

/-! ### Where the physics lives

In the quantum setting, the bridge axioms connect the abstract
quantities to observables:

| IG quantity | Quantum meaning | Scale factor |
|-------------|----------------|--------------|
| `g_{ii}` | `4 · Var_ψ(Oᵢ)` | 4 |
| `g_{ij}` | `4 · Cov_ψ(Oᵢ, Oⱼ)` | 4 |
| `ω_{ij}` | `2 · Im⟨ψ, [Oᵢ, Oⱼ]ψ⟩` | 2 |

Substituting into `g_{ii} g_{jj} ≥ g_{ij}² + ω_{ij}²`:

  `16 Var(A) Var(B) ≥ 16 Cov(A,B)² + 4 Im⟨[A,B]⟩²`

i.e., `Var(A) Var(B) ≥ Cov(A,B)² + ¼ |⟨[A,B]⟩|²`,

which is the Schrödinger uncertainty relation.

The `rld_cauchy_schwarz` axiom is discharged from the Hilbert space
Cauchy–Schwarz inequality:

  `|⟨Ãψ, B̃ψ⟩|² ≤ ‖Ãψ‖² · ‖B̃ψ‖²`

via the decomposition `⟨Ãψ, B̃ψ⟩ = Cov(A,B) + ½ i · Im⟨[A,B]⟩`
(Schrödinger's key identity, proved in `Schrodinger.lean`).
-/

end RLDFisherModel

end InformationGeometry
