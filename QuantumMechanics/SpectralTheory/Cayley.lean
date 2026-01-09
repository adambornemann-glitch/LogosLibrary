/-
Author: Adam Bornemann
Created: 12-27-2025
Updated: 1-6-2026

================================================================================
THE CAYLEY TRANSFORM
Von Neumann's Bridge from Unbounded to Bounded Spectral Theory (1929-1932)
================================================================================

Historical Context
------------------
In 1925-1927, quantum mechanics existed in two seemingly distinct formulations:
Heisenberg's matrix mechanics (infinite matrices) and Schrödinger's wave mechanics
(differential operators on L²). Dirac's "transformation theory" unified them
formally, but relied on mathematically ill-defined objects—the notorious
δ-functions and their derivatives.

The core problem: the physically essential operators of quantum mechanics
(position, momentum, energy) are *unbounded*. Hilbert's spectral theory,
developed 1906-1912, applied only to bounded operators. The mathematical
foundations of quantum mechanics were, in 1927, parsing correct physical
predictions from formally meaningless expressions.

Von Neumann's Insight
---------------------
The Cayley transform provides a bijective correspondence:

    { Self-adjoint operators A }  ←→  { Unitary operators U with -1 ∉ σₚ(U) }

Given self-adjoint A, define:

    U = (A - iI)(A + iI)⁻¹

This is well-defined because ±i lie in the resolvent set of any self-adjoint
operator (eigenvalues of self-adjoint operators are real). The resulting U is:
  • Bounded (in fact, ‖U‖ = 1)
  • Unitary (U*U = UU* = I)
  • Defined on all of H

The inverse transform recovers A:

    A = i(I + U)(I - U)⁻¹

with domain D(A) = Range(I - U).

Why This Works: The Key Identity
--------------------------------
For ψ ∈ D(A), self-adjointness implies ⟨Aψ, ψ⟩ ∈ ℝ. Therefore:

    ‖(A ± iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

The cross-term ±2i⟨Aψ, ψ⟩ vanishes in the real part because ⟨Aψ, ψ⟩ is real!

This single identity implies:
  1. (A + iI) is injective (‖(A+iI)ψ‖ ≥ ‖ψ‖)
  2. The Cayley transform is an isometry (‖Uφ‖ = ‖φ‖)
  3. Combined with self-adjointness conditions, U is unitary

Spectral Correspondence
-----------------------
The Cayley transform maps the spectrum bijectively:

    ℝ ∋ μ  ↦  (μ - i)/(μ + i) ∈ S¹ \ {-1}

This is the Möbius transformation that maps the real line to the unit circle
(minus the point -1). Eigenvalues map to eigenvalues. Approximate eigenvalues
map to approximate eigenvalues. The spectral theorem for unbounded self-adjoint
operators follows from the spectral theorem for unitary operators.

Mathematical Significance
-------------------------
This transform reduced the unbounded spectral theory problem—which had blocked
progress since Hilbert's 1906 work—to the bounded case in one stroke. It enabled
von Neumann's 1932 "Mathematische Grundlagen der Quantenmechanik," the first
rigorous foundation for quantum mechanics, and remains the standard approach
in functional analysis texts today.

Structure of This File
----------------------
  § Cayley Transform Definition     — U = I - 2i·R_{-i}
  § Isometry Property               — ‖Uφ‖ = ‖φ‖ via the key identity
  § Surjectivity                    — Range(U) = H via self-adjointness
  § Unitarity                       — Isometry + surjective ⟹ unitary
  § Eigenvalue -1                   — Uφ = -φ ⟺ Aψ = 0 correspondence
  § Inverse Cayley Transform        — A = i(I+U)(I-U)⁻¹
  § Spectral Correspondence         — Full σ(A) ↔ σ(U) bijection
  § Domain Characterization         — D(A) = Range(I - U)

References
----------
  • Von Neumann, J. "Allgemeine Eigenwerttheorie Hermitescher
    Funktionaloperatoren" Math. Ann. 102 (1929), 49-131.
  • Von Neumann, J. "Mathematische Grundlagen der Quantenmechanik"
    Springer, Berlin (1932). English trans. Princeton (1955).
  • Reed, M. & Simon, B. "Methods of Modern Mathematical Physics"
    Vol. I, Section VIII.3; Vol. II, Section X.1.
  • Rudin, W. "Functional Analysis" 2nd ed., Section 13.30-13.32.
-/

import LogosLibrary.QuantumMechanics.Evolution.Resolvent
open InnerProductSpace MeasureTheory Complex Filter Topology  StonesTheorem.Bochner Stone.Generators
open scoped BigOperators Topology

namespace StonesTheorem.Cayley
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-!
## Unitary Operators: Preliminaries

Before constructing the Cayley transform, we establish the basic theory of
unitary operators on Hilbert space. These results are classical, but we
develop them here to maintain self-containment and to establish the logical
chain that will be essential later:

    U*U = I  ⟹  inner product preservation  ⟹  isometry  ⟹  injectivity
    UU* = I  ⟹  surjectivity (directly: y = U(U*y))

Together: unitary ⟹ bijective isometry ⟹ invertible.

The Cayley transform will produce a unitary operator from any self-adjoint
generator. These lemmas then immediately give us the structural properties
we need for the inverse construction.
-/

/--
A continuous linear map U : H →L[ℂ] H is **unitary** if it satisfies
both U*U = I and UU* = I.

**Equivalent characterizations** (which we prove below):
- U is a surjective isometry
- U preserves the inner product and is surjective
- U is invertible with U⁻¹ = U*

**Physical interpretation:** Unitary operators represent symmetries and
time evolution in quantum mechanics. The condition U*U = UU* = I ensures
that probabilities (computed from inner products) are preserved.

**Note:** In finite dimensions, U*U = I implies UU* = I automatically.
In infinite dimensions, this fails: there exist isometries that are not
surjective (e.g., the unilateral shift). We require both conditions.
-/
def Unitary (U : H →L[ℂ] H) : Prop :=
  U.adjoint * U = 1 ∧ U * U.adjoint = 1

/--
Unitary operators preserve inner products: ⟪Ux, Uy⟫ = ⟪x, y⟫.

**Proof:** The adjoint satisfies ⟪U*z, w⟫ = ⟪z, Uw⟫ by definition.
Therefore ⟪Ux, Uy⟫ = ⟪U*Ux, y⟫ = ⟪x, y⟫ since U*U = I.

**This is the fundamental property.** All other consequences of unitarity
(norm preservation, injectivity, angle preservation) flow from this single
identity. Geometrically, U is a rigid motion of Hilbert space.
-/
lemma Unitary.inner_map_map {U : H →L[ℂ] H} (hU : Unitary U) (x y : H) :
    ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  calc ⟪U x, U y⟫_ℂ
      = ⟪U.adjoint (U x), y⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪(U.adjoint * U) x, y⟫_ℂ := rfl
    _ = ⟪x, y⟫_ℂ := by rw [hU.1]; simp

/--
Unitary operators are isometries: ‖Ux‖ = ‖x‖.

**Proof:** Set y = x in inner product preservation:
  ‖Ux‖² = ⟪Ux, Ux⟫ = ⟪x, x⟫ = ‖x‖²

**Remark:** The converse is false in infinite dimensions! The unilateral
shift S on ℓ² satisfies ‖Sx‖ = ‖x‖ but is not unitary (not surjective).
Isometry means S*S = I; unitarity additionally requires SS* = I.
-/
lemma Unitary.norm_map {U : H →L[ℂ] H} (hU : Unitary U) (x : H) : ‖U x‖ = ‖x‖ := by
  have h := hU.inner_map_map x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h_sq : ‖U x‖^2 = ‖x‖^2 := by exact_mod_cast h
  nlinarith [norm_nonneg (U x), norm_nonneg x, sq_nonneg (‖U x‖ - ‖x‖)]

/--
Unitary operators are injective.

**Proof:** If Ux = Uy, then ‖U(x - y)‖ = ‖x - y‖ = 0 by isometry,
hence x = y.

**Note:** This follows from U*U = I alone (any isometry is injective).
We do not need the full unitarity hypothesis here.
-/
lemma Unitary.injective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Injective U := by
  intro x y hxy
  have : ‖U x - U y‖ = 0 := by simp [hxy]
  rw [← map_sub, hU.norm_map] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/--
Unitary operators are surjective.

**Proof:** For any y ∈ H, set x = U*y. Then Ux = U(U*y) = (UU*)y = y
since UU* = I.

**This is where we use the second condition.** The hypothesis UU* = I
provides an explicit right inverse, which is surjectivity. Combined
with injectivity (from U*U = I), we get bijectivity.
-/
lemma Unitary.surjective {U : H →L[ℂ] H} (hU : Unitary U) : Function.Surjective U := by
  intro y
  use U.adjoint y
  have := congr_arg (· y) hU.2
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
  exact this

/--
Unitary operators are invertible (IsUnit in the ring of bounded operators).

**Proof:** The adjoint U* serves as a two-sided inverse:
- U* · U = I  (given: first unitarity condition)
- U · U* = I  (given: second unitarity condition)

**Corollary:** For unitary U, we have U⁻¹ = U*. This is the operator-theoretic
manifestation of the fact that unitary matrices satisfy Ū^T = U⁻¹.
-/
lemma Unitary.isUnit {U : H →L[ℂ] H} (hU : Unitary U) : IsUnit U :=
  ⟨⟨U, U.adjoint, hU.2, hU.1⟩, rfl⟩


/-!
## The Cayley Transform

We now construct the central object of this development: the Cayley transform
of a self-adjoint operator.

### Historical Note

The transform is named after Arthur Cayley, who in 1846 studied the map
X ↦ (X - I)(X + I)⁻¹ for matrices. However, Cayley worked only with finite
matrices and bounded operators. The extension to unbounded self-adjoint
operators—the case that matters for quantum mechanics—is due to von Neumann
(1929), building on earlier work with Hilbert and Nordheim (1927).

### The Key Idea

Given a self-adjoint operator A (potentially unbounded), we want to construct
a unitary operator U (necessarily bounded). The naive approach would be to
exponentiate: U = e^{iA}. But defining the exponential of an unbounded operator
requires... the spectral theorem we're trying to prove!

Von Neumann's insight: use the resolvent instead. Since A is self-adjoint,
its eigenvalues are real, so ±i are in the resolvent set. The operator
(A + iI)⁻¹ exists and is bounded. We can then form:

    U = (A - iI)(A + iI)⁻¹ = I - 2i(A + iI)⁻¹

The second form shows U is a bounded perturbation of the identity.

### Algebraic Derivation

Starting from U = (A - iI)(A + iI)⁻¹:

    U = (A + iI - 2iI)(A + iI)⁻¹
      = (A + iI)(A + iI)⁻¹ - 2iI(A + iI)⁻¹
      = I - 2i·R_{-i}

where R_{-i} = (A + iI)⁻¹ is the resolvent at -i.

This form is computationally convenient: it expresses U directly in terms
of the resolvent, which we have already constructed in the Resolvent module.
-/

/--
The **Cayley transform** of a self-adjoint generator A.

### Definition

    U = I - 2i · R_{-i}

where R_{-i} = (A + iI)⁻¹ is the resolvent at the spectral parameter -i.

### Equivalent Forms

1. **Resolvent form:** U = I - 2i·(A + iI)⁻¹
2. **Quotient form:** U = (A - iI)(A + iI)⁻¹
3. **Action form:** For φ ∈ H with ψ = R_{-i}(φ), we have Uφ = (A - iI)ψ

### Why This Definition?

We use the resolvent form because:
- `Resolvent.resolvent_at_neg_i` is already constructed and proven bounded
- The expression I - 2i·R_{-i} is manifestly a bounded operator on all of H
- The algebraic manipulations required for proofs are simpler

### Type Signature

The transform takes:
- A one-parameter unitary group U_grp (the time evolution)
- Its generator gen (the Hamiltonian / self-adjoint operator A)
- A proof hsa that the generator is self-adjoint

It returns a continuous linear map H →L[ℂ] H, which we will prove is unitary.

### Physical Interpretation

If A is the Hamiltonian of a quantum system (with ℏ = 1), then:
- R_{-i} = (A + iI)⁻¹ is related to the Laplace transform of time evolution
- U maps the "A + i" spectral data to the "A - i" spectral data
- The unit circle (range of U's spectrum) represents phase factors e^{iθ}
-/
noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa

/--
**Action of the Cayley transform:** Uφ = (A - iI)ψ where (A + iI)ψ = φ.

### Statement

For any φ ∈ H, let ψ = R_{-i}(φ) be the unique element of D(A) satisfying
(A + iI)ψ = φ. Then the Cayley transform acts as:

    U(φ) = Aψ - iψ = (A - iI)ψ

### Derivation

Starting from U = I - 2i·R_{-i} and using (A + iI)ψ = φ (i.e., Aψ + iψ = φ):

    Uφ = φ - 2i·ψ
       = (Aψ + iψ) - 2iψ
       = Aψ - iψ
       = (A - iI)ψ

### Significance

This lemma is the **fundamental computational tool** for working with the
Cayley transform. It translates between:

- The bounded operator U acting on arbitrary φ ∈ H
- The unbounded operator A acting on ψ ∈ D(A)

Every major theorem about the Cayley transform (isometry, surjectivity,
unitarity, spectral correspondence) ultimately reduces to algebraic
manipulations using this identity.

### Warning on Domains

Note that ψ ∈ D(A) but φ ∈ H may not be in D(A). The Cayley transform
"lifts" the action of A to all of H via the resolvent.
-/
lemma cayleyTransform_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    let hψ := Resolvent.resolvent_solution_mem_plus gen hsa φ
    cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform]
  -- ψ = R_{-i}(φ) satisfies (A + iI)ψ = φ, i.e., Aψ + iψ = φ
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ

  -- Uφ = φ - 2i·ψ = (Aψ + iψ) - 2iψ = Aψ - iψ = (A - iI)ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]
  calc φ - (2 * I) • ψ
      = (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) - (2 * I) • ψ := by rw [← hψ_eq]
    _ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ - (2 * I) • ψ := rfl
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by
      rw [mul_smul, two_smul ℂ (I • ψ)]
      abel
    _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := rfl

/-!
## Isometry Property

This section establishes that the Cayley transform preserves norms: ‖Uφ‖ = ‖φ‖.

### The Heart of the Matter

The entire proof rests on a single identity. For self-adjoint A and ψ ∈ D(A):

    ‖(A ± iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

Both signs give the same result! This is not a coincidence—it is the geometric
content of self-adjointness.

### Why the Cross-Term Vanishes

Expanding ‖(A + iI)ψ‖² = ⟨(A + iI)ψ, (A + iI)ψ⟩:

    ‖Aψ + iψ‖² = ‖Aψ‖² + ‖iψ‖² + 2·Re⟨Aψ, iψ⟩
               = ‖Aψ‖² + ‖ψ‖² + 2·Re(i⟨Aψ, ψ⟩)

The cross-term is Re(i⟨Aψ, ψ⟩) = Re(i · r) where r = ⟨Aψ, ψ⟩.

**Key observation:** For self-adjoint A, the expectation value ⟨Aψ, ψ⟩ is real.

Proof: By symmetry, ⟨Aψ, ψ⟩ = ⟨ψ, Aψ⟩ = conj⟨Aψ, ψ⟩, so ⟨Aψ, ψ⟩ ∈ ℝ.

Therefore Re(i · r) = r · Re(i) = r · 0 = 0.

The same calculation works for (A - iI), giving Re(-i · r) = 0.

### Geometric Interpretation

In the complex plane, multiplying a real number r by i rotates it to the
imaginary axis. Taking the real part then gives zero. Self-adjointness
ensures ⟨Aψ, ψ⟩ lies on the real axis, and multiplication by ±i rotates
it to the imaginary axis, where it contributes nothing to the norm.

### The Isometry Proof

Given φ ∈ H, let ψ = R_{-i}(φ), so:
- (A + iI)ψ = φ   (definition of resolvent)
- (A - iI)ψ = Uφ  (by cayleyTransform_apply)

Then:
    ‖Uφ‖² = ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² = ‖(A + iI)ψ‖² = ‖φ‖²

The middle equality is where both ± cases coincide.
-/

/--
**The Cayley transform is an isometry:** ‖Uφ‖ = ‖φ‖ for all φ ∈ H.

### Theorem Statement

For any φ in the Hilbert space H, the Cayley transform preserves its norm.

### Proof Strategy

1. Write φ = (A + iI)ψ for unique ψ ∈ D(A) (via resolvent)
2. Then Uφ = (A - iI)ψ (by `cayleyTransform_apply`)
3. Show ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² (cross-term vanishes)
4. Show ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² (same identity)
5. Conclude ‖Uφ‖² = ‖φ‖²

### Why This Matters

Isometry is half of unitarity. Combined with surjectivity (next section),
we obtain that U is unitary. The isometry property alone gives:
- U is injective (isometries are always injective)
- U has closed range (isometries into complete spaces have closed range)
- ‖U‖ = 1 as an operator (assuming H ≠ {0})

### Physical Interpretation

Norm preservation means probability preservation. If ψ represents a quantum
state with ‖ψ‖ = 1, then ‖Uψ‖ = 1 as well. The Cayley transform respects
the probabilistic interpretation of quantum mechanics.
-/
theorem cayleyTransform_isometry {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ φ : H, ‖cayleyTransform gen hsa φ‖ = ‖φ‖ := by
  intro φ

  /-
  Step 1: Set up the resolvent decomposition.

  For any φ ∈ H, there exists unique ψ ∈ D(A) such that (A + iI)ψ = φ.
  This ψ is precisely R_{-i}(φ), the resolvent applied to φ.
  -/
  let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
  have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ

  /-
  Step 2: Express Uφ in terms of ψ.

  By cayleyTransform_apply: Uφ = (A - iI)ψ = Aψ - iψ
  -/
  have h_Uφ : cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ :=
    cayleyTransform_apply gen hsa φ

  /-
  Step 3: The fundamental identity for (A - iI).

  We prove: ‖Aψ - iψ‖² = ‖Aψ‖² + ‖ψ‖²

  The key is that the cross-term 2·Re⟨Aψ, iψ⟩ vanishes because ⟨Aψ, ψ⟩ ∈ ℝ.
  -/
  have h_minus : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 =
                 ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := by

    -- Preliminary: ‖iψ‖ = ‖ψ‖ since |i| = 1
    have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp

    /-
    The crux: Re⟨Aψ, iψ⟩ = 0.

    We have ⟨Aψ, iψ⟩ = i · ⟨Aψ, ψ⟩.
    Since A is symmetric, ⟨Aψ, ψ⟩ = ⟨ψ, Aψ⟩ = conj⟨Aψ, ψ⟩, hence ⟨Aψ, ψ⟩ ∈ ℝ.
    Thus ⟨Aψ, iψ⟩ = i · (real number), which has zero real part.
    -/
    have cross_zero : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re = 0 := by
      rw [inner_smul_right]
      -- Show ⟨Aψ, ψ⟩ is real by proving its imaginary part is zero
      have h_real : (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).im = 0 := by
        -- Use symmetry: ⟨Aψ, ψ⟩ = ⟨ψ, Aψ⟩
        have h_sym := gen.symmetric ⟨ψ, hψ_mem⟩ ⟨ψ, hψ_mem⟩
        -- Combined with ⟨ψ, Aψ⟩ = conj⟨Aψ, ψ⟩, we get ⟨Aψ, ψ⟩ = conj⟨Aψ, ψ⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                      (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
        -- z = conj(z) implies Im(z) = 0
        have := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at this
        linarith [this.2]
      -- Now: i · ⟨Aψ, ψ⟩ = i · Re⟨Aψ, ψ⟩ (since Im = 0), which is purely imaginary
      have h1 : I * ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                I * (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).re := by
        conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ, h_real]
        simp
      rw [h1, mul_comm]; simp  -- Re(r · i) = 0 for real r

    /-
    Expand ‖x - y‖² using the parallelogram-type identity:
    ‖x - y‖² = ‖x‖² + ‖y‖² - 2·Re⟨x, y⟩

    With cross_zero, this becomes ‖x‖² + ‖y‖².
    -/
    have h_expand : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 =
        ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖I • ψ‖^2 -
        2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖ ^ 2 =
                (⟪gen.op ⟨ψ, hψ_mem⟩ - I • ψ, gen.op ⟨ψ, hψ_mem⟩ - I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩ - I • ψ)
        rw [this]; norm_cast
      have h2 : ‖gen.op ⟨ψ, hψ_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, hψ_mem⟩, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩)
        rw [this]; norm_cast
      have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
        rw [this]; norm_cast
      have h_cross : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re =
                    2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
        have h_eq : (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
          calc (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [h_eq]; ring
      rw [h1, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      rw [h2, h3, ← h_cross]
      ring

    -- Combine: ‖Aψ - iψ‖² = ‖Aψ‖² + ‖ψ‖² - 2·0 = ‖Aψ‖² + ‖ψ‖²
    rw [h_expand, norm_I_smul, cross_zero]
    ring

  /-
  Step 4: The same identity for (A + iI).

  We prove: ‖Aψ + iψ‖² = ‖Aψ‖² + ‖ψ‖²

  The proof is identical—the cross-term 2·Re⟨Aψ, iψ⟩ = 0 regardless of sign.
  -/
  have h_plus : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 =
              ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := by
    have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp

    have cross_zero : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re = 0 := by
      rw [inner_smul_right]
      have h_real : (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ⟨ψ, hψ_mem⟩ ⟨ψ, hψ_mem⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                      (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
        have := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at this
        linarith [this.2]
      have h1 : I * ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ =
                I * (⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ).re := by
        conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ_mem⟩, ψ⟫_ℂ, h_real]
        simp
      rw [h1, mul_comm]; simp

    -- For addition: ‖x + y‖² = ‖x‖² + ‖y‖² + 2·Re⟨x, y⟩
    have h_expand : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 =
        ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖I • ψ‖^2 +
        2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖ ^ 2 =
                (⟪gen.op ⟨ψ, hψ_mem⟩ + I • ψ, gen.op ⟨ψ, hψ_mem⟩ + I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩ + I • ψ)
        rw [this]; norm_cast
      have h2 : ‖gen.op ⟨ψ, hψ_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, hψ_mem⟩, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, hψ_mem⟩)
        rw [this]; norm_cast
      have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
        rw [this]; norm_cast
      have h_cross : (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re =
                    2 * (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
        have h_eq : (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by
          calc (⟪I • ψ, gen.op ⟨ψ, hψ_mem⟩⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪gen.op ⟨ψ, hψ_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [h_eq]; ring
      rw [h1, inner_add_left, inner_add_right, inner_add_right]
      simp only [Complex.add_re]
      rw [h2, h3, ← h_cross]
      ring

    -- Combine: ‖Aψ + iψ‖² = ‖Aψ‖² + ‖ψ‖² + 2·0 = ‖Aψ‖² + ‖ψ‖²
    rw [h_expand, norm_I_smul, cross_zero]
    ring

  /-
  Step 5: Chain the identities together.

      ‖Uφ‖² = ‖(A - iI)ψ‖²     (by Step 2: Uφ = (A - iI)ψ)
            = ‖Aψ‖² + ‖ψ‖²     (by Step 3: cross-term vanishes)
            = ‖(A + iI)ψ‖²     (by Step 4: same identity)
            = ‖φ‖²             (by Step 1: φ = (A + iI)ψ)
  -/
  have h_sq : ‖cayleyTransform gen hsa φ‖^2 = ‖φ‖^2 := by
    calc ‖cayleyTransform gen hsa φ‖^2
        = ‖gen.op ⟨ψ, hψ_mem⟩ - I • ψ‖^2 := by rw [h_Uφ]
      _ = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_minus
      _ = ‖gen.op ⟨ψ, hψ_mem⟩ + I • ψ‖^2 := h_plus.symm
      _ = ‖φ‖^2 := by rw [hψ_eq]

  -- Extract ‖Uφ‖ = ‖φ‖ from ‖Uφ‖² = ‖φ‖² (both norms are non-negative)
  rw [← Real.sqrt_sq (norm_nonneg (cayleyTransform gen hsa φ)),
      ← Real.sqrt_sq (norm_nonneg φ), h_sq]

/-!
## Surjectivity

We prove that the Cayley transform is surjective: every element of H is
in the range of U.

### The Role of Self-Adjointness

Recall that `Generator.IsSelfAdjoint gen` packages two conditions:

1. **Symmetry:** ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for all ψ, φ ∈ D(A)
2. **Maximality:** Range(A - iI) = H and Range(A + iI) = H

We used symmetry in the isometry proof (to show ⟨Aψ, ψ⟩ ∈ ℝ).
Now we use maximality.

### Why Maximality Matters

A symmetric operator need not be self-adjoint. The difference is subtle
but crucial:

- **Symmetric:** ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ on D(A)
- **Self-adjoint:** Symmetric AND D(A) = D(A*)

The condition Range(A ± iI) = H is equivalent to self-adjointness (this is
a theorem of von Neumann). It ensures that:

- (A + iI)⁻¹ is defined on ALL of H (not just a dense subspace)
- (A - iI)⁻¹ is defined on ALL of H
- The Cayley transform maps H onto H (surjectivity)

### The Surjectivity Proof

Given χ ∈ H, we must find φ ∈ H with Uφ = χ.

**Step 1:** By hsa.2, there exists ψ ∈ D(A) with (A - iI)ψ = χ.

**Step 2:** Set φ = (A + iI)ψ.

**Step 3:** Then Uφ = (A - iI)ψ = χ. ∎

The key insight is that Range(U) = Range(A - iI). Since Range(A - iI) = H
by self-adjointness, we have Range(U) = H.

### Contrast with Merely Symmetric Operators

If A were only symmetric (not self-adjoint), then Range(A - iI) might be
a proper dense subspace of H. The Cayley transform would still be an
isometry, but NOT surjective—it would be like the unilateral shift.

This is why the distinction between "symmetric" and "self-adjoint" is not
pedantry but physics: only self-adjoint operators generate unitary time
evolution, and only they have the full spectral theorem.
-/

/--
**The Cayley transform is surjective:** Range(U) = H.

### Theorem Statement

For any χ ∈ H, there exists φ ∈ H such that U(φ) = χ.

### Proof Outline

1. Use self-adjointness (hsa.2): Range(A - iI) = H
2. For given χ, find ψ ∈ D(A) with (A - iI)ψ = χ
3. Set φ = (A + iI)ψ
4. Then U(φ) = (A - iI)ψ = χ

### Key Observation

The proof constructs an explicit preimage:

    φ = (A + iI)ψ  where  (A - iI)ψ = χ

This shows that Range(U) = Range(A - iI), and self-adjointness gives
Range(A - iI) = H.

### Why This Completes Half the Story

Combined with isometry (previous section), we now have:

- U is an isometry (‖Uφ‖ = ‖φ‖)
- U is surjective (Range(U) = H)

Together: **U is a surjective isometry, hence unitary.**

This is the fundamental theorem of the Cayley transform.
-/
theorem cayleyTransform_surjective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Function.Surjective (cayleyTransform gen hsa) := by
  intro χ

  /-
  Step 1: Use the second self-adjointness condition.

  The hypothesis hsa.2 states: Range(A - iI) = H.
  Concretely: for any χ ∈ H, there exists ψ ∈ D(A) with (A - iI)ψ = χ.

  This is the ONLY place in the unitarity proof where we use hsa.2.
  The isometry proof used only symmetry (hsa.1 implicitly through gen.symmetric).
  -/
  obtain ⟨ψ, hψ_dom, hψ_eq⟩ := hsa.2 χ

  /-
  Step 2: Construct the preimage.

  We claim that φ := (A + iI)ψ satisfies U(φ) = χ.

  Intuition: The Cayley transform sends (A + iI)ψ ↦ (A - iI)ψ.
  If we want output χ = (A - iI)ψ, we input (A + iI)ψ.
  -/
  let φ := gen.op ⟨ψ, hψ_dom⟩ + I • ψ
  use φ

  /-
  Step 3: Verify that U(φ) = χ.

  The resolvent R_{-i}(φ) solves (A + iI)x = φ.
  But ψ also solves this equation (by definition of φ).
  By uniqueness of the resolvent solution, R_{-i}(φ) = ψ.

  Then: U(φ) = (A - iI) · R_{-i}(φ) = (A - iI)ψ = χ.
  -/
  have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
    -- Both ψ and R_{-i}(φ) solve (A + iI)x = φ
    have h_sol : gen.op ⟨ψ, hψ_dom⟩ + I • ψ = φ := rfl
    let ψ' := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ'_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ'_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ
    -- By uniqueness of solutions to (A + iI)x = φ, we have ψ' = ψ
    exact Resolvent.resolvent_at_neg_i_unique gen hsa φ ψ' ψ hψ'_mem hψ_dom hψ'_eq h_sol

  -- Chain: U(φ) = (A - iI) · R_{-i}(φ) = (A - iI)ψ = χ
  have h_Uφ := cayleyTransform_apply gen hsa φ
  simp only at h_Uφ
  calc cayleyTransform gen hsa φ
      = gen.op ⟨Resolvent.resolvent_at_neg_i gen hsa φ,
               Resolvent.resolvent_solution_mem_plus gen hsa φ⟩ -
        I • Resolvent.resolvent_at_neg_i gen hsa φ := h_Uφ
    _ = gen.op ⟨ψ, hψ_dom⟩ - I • ψ := by
        subst hψ_eq
        simp_all only [map_add, map_smul, φ]
    _ = χ := hψ_eq

/-!
## Unitarity

This section establishes the main theorem: the Cayley transform is unitary.

### The Structure of the Proof

We have established:
- **Isometry:** ‖Uφ‖ = ‖φ‖ for all φ ∈ H (from self-adjointness via cross-term)
- **Surjectivity:** Range(U) = H (from Range(A - iI) = H)

We now show these imply unitarity: U*U = UU* = I.

### From Isometry to U*U = I

An isometry preserves norms: ‖Uφ‖ = ‖φ‖. But unitarity requires U*U = I,
which is equivalent to inner product preservation: ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫.

The bridge is the **polarization identity**. In a complex Hilbert space:

    4⟪φ, ψ⟫ = ‖φ + ψ‖² - ‖φ - ψ‖² + i‖φ + iψ‖² - i‖φ - iψ‖²

If U preserves all four norms on the right, it preserves the inner product
on the left. Since U is an isometry, it preserves all norms, hence all
inner products.

### From Surjectivity to UU* = I

Once we have U*U = I, surjectivity gives UU* = I:

For any φ ∈ H, surjectivity provides ψ with Uψ = φ. Then:

    UU*φ = UU*(Uψ) = U(U*U)ψ = Uψ = φ

So UU* = I on all of H.

### Why Both Conditions Are Necessary

- Isometry alone does NOT imply unitarity. The unilateral shift S on ℓ²
  satisfies S*S = I but SS* ≠ I (it projects onto the orthogonal
  complement of the first basis vector).

- Surjectivity alone does NOT imply unitarity. A surjective non-isometry
  would have U*U ≠ I.

Self-adjointness of A provides both conditions simultaneously:
- Symmetry → isometry (via the cross-term vanishing)
- Maximality → surjectivity (via Range(A - iI) = H)

### The Polarization Calculation

The proof below extracts both real and imaginary parts of ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫
from the isometry property. The key steps:

1. From ‖U(φ + ψ)‖² = ‖φ + ψ‖², extract Re⟪Uφ, Uψ⟫ = Re⟪φ, ψ⟫
2. From ‖U(φ + iψ)‖² = ‖φ + iψ‖², extract Im⟪Uφ, Uψ⟫ = Im⟪φ, ψ⟫
3. Combine to get ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫
4. This is equivalent to U*U = I
5. Surjectivity then gives UU* = I
-/

/--
**The Cayley transform is unitary:** U*U = UU* = I.

### Theorem Statement

The Cayley transform satisfies both unitarity conditions:
- U*U = I (equivalently: U preserves inner products)
- UU* = I (equivalently: U* is a right inverse)

### Proof Structure

**Part 1: U*U = I (from isometry)**

We show ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫ for all φ, ψ using polarization:

Step 1a: From ‖Ux‖ = ‖x‖, deduce ⟪Ux, Ux⟫ = ⟪x, x⟫
Step 1b: Apply to x = φ + ψ, expand, use Step 1a for φ and ψ separately
         → Extract: Re⟪Uφ, Uψ⟫ = Re⟪φ, ψ⟫
Step 1c: Apply to x = φ + iψ, same expansion
         → Extract: Im⟪Uφ, Uψ⟫ = Im⟪φ, ψ⟫
Step 1d: Combine real and imaginary parts
         → ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫, i.e., U*U = I

**Part 2: UU* = I (from surjectivity)**

For any φ, choose ψ with Uψ = φ (surjectivity). Then:
    UU*φ = UU*(Uψ) = U(U*Uψ) = Uψ = φ

### Historical Note

This polarization argument is classical—it appears in essentially this
form in von Neumann's original work. The key insight is that complex
inner products are determined by norms via polarization, so isometries
(norm-preserving maps) automatically preserve inner products.

### Significance

This theorem completes the forward direction of the Cayley correspondence:

    Self-adjoint A  →  Unitary U = (A - iI)(A + iI)⁻¹

The converse (unitary U with -1 ∉ σₚ(U) → self-adjoint A) is established
in the inverse Cayley transform section.
-/
theorem cayleyTransform_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) := by

  /-
  ═══════════════════════════════════════════════════════════════════════════
  PART 1: Prove U*U = I using the polarization identity
  ═══════════════════════════════════════════════════════════════════════════

  Strategy: Show ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫ for all φ, ψ.
  This is equivalent to U*U = I because:
      ⟪U*Uφ, ψ⟩ = ⟪Uφ, Uψ⟩ = ⟪φ, ψ⟩  for all ψ
  implies U*Uφ = φ by non-degeneracy of the inner product.
  -/
  have h_isometry := cayleyTransform_isometry gen hsa

  have h_star_self : (cayleyTransform gen hsa).adjoint * cayleyTransform gen hsa = 1 := by
    -- Prove equality of operators by showing they agree on all vectors
    ext φ
    -- Use non-degeneracy: two vectors are equal iff their inner products
    -- with all other vectors are equal
    apply ext_inner_left ℂ
    intro ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    -- Goal: ⟪U*Uφ, ψ⟫ = ⟪φ, ψ⟫
    -- By definition of adjoint: ⟪U*Uφ, ψ⟫ = ⟪Uφ, Uψ⟫
    rw [ContinuousLinearMap.adjoint_inner_right]
    -- So we must show: ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫

    /-
    ─────────────────────────────────────────────────────────────────────────
    The Polarization Argument
    ─────────────────────────────────────────────────────────────────────────

    We extract ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫ from norm preservation using polarization.

    Key insight: In a complex Hilbert space, the inner product is determined
    by the norm via the polarization identity. So norm-preserving maps
    (isometries) automatically preserve inner products.
    -/
    have h_polar : ⟪cayleyTransform gen hsa φ, cayleyTransform gen hsa ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
      set U := cayleyTransform gen hsa with hU

      /-
      Step 1a: From isometry (‖Ux‖ = ‖x‖), derive ⟪Ux, Ux⟫ = ⟪x, x⟫.

      This is immediate since ‖x‖² = ⟪x, x⟫ for vectors in a Hilbert space.
      -/
      have h_inner_self : ∀ x, ⟪U x, U x⟫_ℂ = ⟪x, x⟫_ℂ := by
        intro x
        -- ⟪Ux, Ux⟫ and ⟪x, x⟫ are both real (equal to ‖·‖²)
        have h1 : (⟪U x, U x⟫_ℂ).re = ‖U x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h2 : (⟪x, x⟫_ℂ).re = ‖x‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        have h3 : (⟪U x, U x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
        have h4 : (⟪x, x⟫_ℂ).im = 0 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
        -- Both have same real part (by isometry) and zero imaginary part
        apply Complex.ext <;> simp only [h1, h2, h3, h4, h_isometry]

      /-
      Step 1b: Extract the real part of ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫.

      Expand ⟪U(φ+ψ), U(φ+ψ)⟫ = ⟪φ+ψ, φ+ψ⟫ using bilinearity:

        ⟪Uφ,Uφ⟫ + ⟪Uφ,Uψ⟫ + ⟪Uψ,Uφ⟫ + ⟪Uψ,Uψ⟫ = ⟪φ,φ⟫ + ⟪φ,ψ⟫ + ⟪ψ,φ⟫ + ⟪ψ,ψ⟫

      Using h_inner_self for φ, ψ, and φ+ψ, we get:
        ⟪Uφ,Uψ⟫ + ⟪Uψ,Uφ⟫ = ⟪φ,ψ⟫ + ⟪ψ,φ⟫

      Since ⟪a,b⟫ + ⟪b,a⟫ = ⟪a,b⟫ + conj⟪a,b⟫ = 2·Re⟪a,b⟫, this gives:
        Re⟪Uφ, Uψ⟫ = Re⟪φ, ψ⟫
      -/
      have h_re_part : ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by
        have h_sum := h_inner_self (φ + ψ)
        rw [U.map_add] at h_sum
        have lhs : ⟪U φ + U ψ, U φ + U ψ⟫_ℂ =
                  ⟪U φ, U φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪U ψ, U ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have rhs : ⟪φ + ψ, φ + ψ⟫_ℂ =
                  ⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        -- Substitute into h_sum and use h_inner_self to cancel diagonal terms
        have hφ := h_inner_self φ
        have hψ := h_inner_self ψ
        rw [lhs, rhs, hφ, hψ] at h_sum
        -- Now h_sum says: ⟪φ,φ⟫ + ⟪Uφ,Uψ⟫ + ⟪Uψ,Uφ⟫ + ⟪ψ,ψ⟫ = ⟪φ,φ⟫ + ⟪φ,ψ⟫ + ⟪ψ,φ⟫ + ⟪ψ,ψ⟫
        calc ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ
            = (⟪φ, φ⟫_ℂ + ⟪U φ, U ψ⟫_ℂ + ⟪U ψ, U φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ + ⟪ψ, ψ⟫_ℂ) - ⟪φ, φ⟫_ℂ - ⟪ψ, ψ⟫_ℂ := by rw [h_sum]
          _ = ⟪φ, ψ⟫_ℂ + ⟪ψ, φ⟫_ℂ := by ring

      /-
      Step 1c: Extract the imaginary part of ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫.

      Same technique, but expand ⟪U(φ + iψ), U(φ + iψ)⟫ = ⟪φ + iψ, φ + iψ⟫:

        ⟪Uφ,Uφ⟫ + ⟪Uφ,iUψ⟫ + ⟪iUψ,Uφ⟫ + ⟪iUψ,iUψ⟫ = ⟪φ,φ⟫ + ⟪φ,iψ⟫ + ⟪iψ,φ⟫ + ⟪iψ,iψ⟫

      After cancellation:
        ⟪Uφ, iUψ⟫ + ⟪iUψ, Uφ⟫ = ⟪φ, iψ⟫ + ⟪iψ, φ⟫

      Now ⟪a, ib⟫ + ⟪ib, a⟫ = i⟪a,b⟫ - i·conj⟪a,b⟫ = i(⟪a,b⟫ - conj⟪a,b⟫) = -2·Im⟪a,b⟫

      This gives: Im⟪Uφ, Uψ⟫ = Im⟪φ, ψ⟫
      -/
      have h_im_part : ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ = ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ := by
        have h_sum_i := h_inner_self (φ + I • ψ)
        rw [U.map_add, U.map_smul] at h_sum_i
        have lhs : ⟪U φ + I • U ψ, U φ + I • U ψ⟫_ℂ =
                  ⟪U φ, U φ⟫_ℂ + ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ + ⟪I • U ψ, I • U ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        have rhs : ⟪φ + I • ψ, φ + I • ψ⟫_ℂ =
                  ⟪φ, φ⟫_ℂ + ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right]; ring
        -- Show ⟪iUψ, iUψ⟫ = ⟪iψ, iψ⟫ using h_inner_self
        have hIψ : ⟪I • U ψ, I • U ψ⟫_ℂ = ⟪I • ψ, I • ψ⟫_ℂ := by
          rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
          simp only [Complex.conj_I]
          have hψ' := h_inner_self ψ
          ring_nf
          rw [hψ']
        have hφ := h_inner_self φ
        rw [lhs, rhs, hφ, hIψ] at h_sum_i
        calc ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ
            = (⟪φ, φ⟫_ℂ + ⟪U φ, I • U ψ⟫_ℂ + ⟪I • U ψ, U φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) -
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by ring
          _ = (⟪φ, φ⟫_ℂ + ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ + ⟪I • ψ, I • ψ⟫_ℂ) -
              ⟪φ, φ⟫_ℂ - ⟪I • ψ, I • ψ⟫_ℂ := by rw [h_sum_i]
          _ = ⟪φ, I • ψ⟫_ℂ + ⟪I • ψ, φ⟫_ℂ := by ring

      /-
      Step 1d: Combine real and imaginary parts.

      From h_re_part: ⟪Uφ,Uψ⟫ + conj⟪Uφ,Uψ⟫ = ⟪φ,ψ⟫ + conj⟪φ,ψ⟫
                      → Re⟪Uφ,Uψ⟫ = Re⟪φ,ψ⟫

      From h_im_part: i⟪Uφ,Uψ⟫ - i·conj⟪Uφ,Uψ⟫ = i⟪φ,ψ⟫ - i·conj⟪φ,ψ⟫
                      → Im⟪Uφ,Uψ⟫ = Im⟪φ,ψ⟫

      Therefore ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫.
      -/
      apply Complex.ext
      · -- Real parts equal
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        -- z + conj(z) = 2·Re(z)
        have h3 : (⟪U φ, U ψ⟫_ℂ + (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ).re = 2 * (⟪U φ, U ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]; ring
        have h4 : (⟪φ, ψ⟫_ℂ + (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ).re = 2 * (⟪φ, ψ⟫_ℂ).re := by
          simp only [Complex.add_re, Complex.conj_re]; ring
        rw [h1, h2] at h_re_part
        have := congrArg Complex.re h_re_part
        rw [h3, h4] at this
        linarith

      · -- Imaginary parts equal
        rw [inner_smul_right, inner_smul_left, inner_smul_right, inner_smul_left] at h_im_part
        simp only [Complex.conj_I] at h_im_part
        have h1 : ⟪U ψ, U φ⟫_ℂ = (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ := (inner_conj_symm _ _).symm
        have h2 : ⟪ψ, φ⟫_ℂ = (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ := (inner_conj_symm _ _).symm
        -- i·z - i·conj(z) = i(z - conj(z)) = i·(2i·Im(z)) = -2·Im(z)
        have h3 : (I * ⟪U φ, U ψ⟫_ℂ + (-I) * (starRingEnd ℂ) ⟪U φ, U ψ⟫_ℂ).re =
                  -2 * (⟪U φ, U ψ⟫_ℂ).im := by
          simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
                    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
          ring
        have h4 : (I * ⟪φ, ψ⟫_ℂ + (-I) * (starRingEnd ℂ) ⟪φ, ψ⟫_ℂ).re =
                  -2 * (⟪φ, ψ⟫_ℂ).im := by
          simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
                    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
          ring
        rw [h1, h2] at h_im_part
        have := congrArg Complex.re h_im_part
        rw [h3, h4] at this
        linarith

    -- We've shown ⟪Uφ, Uψ⟫ = ⟪φ, ψ⟫. Now apply with swapped arguments.
    have h_polar' : ⟪cayleyTransform gen hsa ψ, cayleyTransform gen hsa φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
      have := congrArg (starRingEnd ℂ) h_polar
      simp only [inner_conj_symm] at this
      exact this
    exact h_polar'

  /-
  ═══════════════════════════════════════════════════════════════════════════
  PART 2: Prove UU* = I using surjectivity
  ═══════════════════════════════════════════════════════════════════════════

  Strategy: For any φ ∈ H, find ψ with Uψ = φ (surjectivity), then:
      UU*φ = UU*(Uψ) = U(U*Uψ) = Uψ = φ
                          ↑
                     uses U*U = I from Part 1
  -/
  have h_surj := cayleyTransform_surjective gen hsa

  have h_self_star : cayleyTransform gen hsa * (cayleyTransform gen hsa).adjoint = 1 := by
    set U := cayleyTransform gen hsa with hU
    ext φ
    -- Use surjectivity: φ = Uψ for some ψ
    obtain ⟨ψ, hψ⟩ := cayleyTransform_surjective gen hsa φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← hψ]
    -- Goal: UU*(Uψ) = Uψ
    -- Use U*U = I: U*(Uψ) = ψ
    have : U.adjoint (U ψ) = ψ := by
      have h := congrFun (congrArg DFunLike.coe h_star_self) ψ
      simp at h
      exact h
    -- Then UU*(Uψ) = U(U*Uψ) = Uψ
    rw [this, hψ]

  /-
  ═══════════════════════════════════════════════════════════════════════════
  CONCLUSION: U is unitary
  ═══════════════════════════════════════════════════════════════════════════
  -/
  exact ⟨h_star_self, h_self_star⟩

/-!
## The Eigenvalue -1 Correspondence

This section establishes the precise relationship between the kernel of A
and the -1 eigenspace of U.

### Why -1 Is Special

The Cayley transform U = (A - iI)(A + iI)⁻¹ corresponds to the Möbius map:

    w(μ) = (μ - i)/(μ + i)

This maps:
- The real line ℝ → the unit circle S¹
- The point μ = 0 → w = -i/i = -1
- The point μ = ∞ → w = 1

So -1 is special: it's the image of 0 under the Möbius map. This suggests
that -1 as an eigenvalue of U should correspond to 0 as an eigenvalue of A.

### The Correspondence

We prove: **-1 ∈ σₚ(U) if and only if 0 ∈ σₚ(A)**

More precisely:
- If Uφ = -φ with φ ≠ 0, then φ = iψ where Aψ = 0 and ψ ≠ 0
- If Aψ = 0 with ψ ≠ 0, then U(iψ) = -iψ

The eigenvectors are related by a factor of i.

### Proof Sketch

**Forward (Uφ = -φ ⟹ Aψ = 0):**

Let ψ = R_{-i}(φ), so (A + iI)ψ = φ. Then:
- Uφ = (A - iI)ψ = -φ = -(A + iI)ψ

Adding: 2Aψ = 0, so Aψ = 0.

Since φ = Aψ + iψ = 0 + iψ = iψ, and φ ≠ 0, we have ψ ≠ 0.

**Backward (Aψ = 0 ⟹ Uφ = -φ):**

Set φ = (A + iI)ψ = 0 + iψ = iψ. Then:
- Uφ = (A - iI)ψ = 0 - iψ = -iψ = -φ ✓

### Significance for the Inverse Cayley Transform

The inverse Cayley transform A = i(I + U)(I - U)⁻¹ requires (I - U) to be
invertible, which fails precisely when -1 is an eigenvalue of U.

The correspondence shows:
- If ker(A) = {0}, then -1 ∉ σₚ(U), so (I - U) is injective
- The inverse Cayley is well-defined on Range(I - U) = D(A)

This is why the Cayley transform establishes a bijection between:
- Self-adjoint operators (possibly with kernel)
- Unitary operators with -1 possibly an eigenvalue

To get a bijection with "unitary operators where -1 is NOT an eigenvalue,"
we must restrict to self-adjoint operators with trivial kernel.
-/

/--
**Eigenvalue correspondence at -1:** The point -1 is an eigenvalue of the
Cayley transform U if and only if 0 is an eigenvalue of the generator A.

### Precise Statement

    (∃ φ ≠ 0, Uφ = -φ)  ↔  (∃ ψ ≠ 0 in D(A), Aψ = 0)

### Eigenvector Relationship

The eigenvectors are related by:
- If Uφ = -φ, then φ = iψ where Aψ = 0
- If Aψ = 0, then U(iψ) = -(iψ)

### Algebraic Content

At μ = 0, the Möbius map gives w = (0 - i)/(0 + i) = -1.
The eigenvalue correspondence is the "infinitesimal" version of the
spectral correspondence at this special point.

### Physical Interpretation

For the Hamiltonian H of a quantum system:
- ker(H) = {ground states with zero energy}
- -1 ∈ σₚ(U) means the Cayley transform has a -1 eigenvector

The correspondence says: zero-energy states exist iff U has -1 eigenvectors.
-/
theorem cayley_neg_one_eigenvalue_iff {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = -φ) ↔
    (∃ ψ : gen.domain, (ψ : H) ≠ 0 ∧ gen.op ψ = 0) := by
  constructor

  /-
  ═══════════════════════════════════════════════════════════════════════════
  FORWARD DIRECTION: Uφ = -φ implies Aψ = 0
  ═══════════════════════════════════════════════════════════════════════════

  Given: φ ≠ 0 with Uφ = -φ
  Goal: Find ψ ≠ 0 in D(A) with Aψ = 0

  Strategy:
  1. Write φ = (A + iI)ψ via the resolvent
  2. Then Uφ = (A - iI)ψ
  3. From Uφ = -φ, derive (A - iI)ψ = -(A + iI)ψ
  4. Add the equations: 2Aψ = 0, so Aψ = 0
  5. Show ψ ≠ 0 (otherwise φ = 0)
  -/
  · intro ⟨φ, hφ_ne, hUφ⟩

    -- Step 1: Decompose φ via the resolvent
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    have hψ_mem := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hψ_eq := Resolvent.resolvent_solution_eq_plus gen hsa φ  -- (A + iI)ψ = φ

    -- Step 2: Express Uφ in terms of ψ
    have h_Uφ := cayleyTransform_apply gen hsa φ

    /-
    Step 3: Derive the key equation.

    We have:
      - Uφ = (A - iI)ψ     (by cayleyTransform_apply)
      - Uφ = -φ            (given)
      - φ = (A + iI)ψ      (by resolvent)

    Therefore: (A - iI)ψ = -(A + iI)ψ

    Equivalently: Aψ - iψ = -Aψ - iψ
    -/
    have h1 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by
      calc gen.op ⟨ψ, hψ_mem⟩ - I • ψ
          = cayleyTransform gen hsa φ := h_Uφ.symm
        _ = -φ := hUφ
        _ = -(gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by rw [← hψ_eq]; exact rfl

    /-
    Step 4: Solve for Aψ.

    From (A - iI)ψ = -(A + iI)ψ:
      Aψ - iψ = -Aψ - iψ
      Aψ + Aψ = 0
      2Aψ = 0
      Aψ = 0  (since 2 ≠ 0 in ℂ)
    -/
    have h_Aψ_zero : gen.op ⟨ψ, hψ_mem⟩ = 0 := by
      -- Add the two sides: (A - iI)ψ + (A + iI)ψ = 0
      have h2 : gen.op ⟨ψ, hψ_mem⟩ - I • ψ + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) = 0 := by
        rw [h1]; abel
      -- This simplifies to 2Aψ = 0
      have h3 : (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩ = 0 := by
        calc (2 : ℂ) • gen.op ⟨ψ, hψ_mem⟩
            = gen.op ⟨ψ, hψ_mem⟩ + gen.op ⟨ψ, hψ_mem⟩ := two_smul ℂ _
          _ = (gen.op ⟨ψ, hψ_mem⟩ - I • ψ) + (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by abel
          _ = 0 := h2
      -- 2 ≠ 0 in ℂ, so Aψ = 0
      exact (smul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

    /-
    Step 5: Show ψ ≠ 0.

    If ψ = 0, then φ = (A + iI)ψ = Aψ + iψ = 0 + 0 = 0.
    But φ ≠ 0 by hypothesis. Contradiction.

    Note: This also shows φ = iψ (since Aψ = 0 implies φ = 0 + iψ = iψ).
    -/
    have hψ_ne : ψ ≠ 0 := by
      intro hψ_eq_zero
      have : φ = 0 := by
        calc φ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ := hψ_eq.symm
          _ = 0 + I • ψ := by rw [h_Aψ_zero]
          _ = 0 + I • 0 := by rw [hψ_eq_zero]
          _ = 0 := by simp
      exact hφ_ne this

    exact ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ_zero⟩

  /-
  ═══════════════════════════════════════════════════════════════════════════
  BACKWARD DIRECTION: Aψ = 0 implies Uφ = -φ
  ═══════════════════════════════════════════════════════════════════════════

  Given: ψ ≠ 0 in D(A) with Aψ = 0
  Goal: Find φ ≠ 0 with Uφ = -φ

  Strategy:
  1. Set φ = (A + iI)ψ = iψ (since Aψ = 0)
  2. Show φ ≠ 0 (since ψ ≠ 0 and i ≠ 0)
  3. Compute Uφ = (A - iI)ψ = -iψ = -φ
  -/
  · intro ⟨⟨ψ, hψ_mem⟩, hψ_ne, h_Aψ⟩

    /-
    Step 1: Construct the eigenvector φ = iψ.

    Since Aψ = 0, we have:
      (A + iI)ψ = Aψ + iψ = 0 + iψ = iψ

    So we set φ = iψ.
    -/
    let φ := I • ψ
    have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := by simp [φ, h_Aψ]

    use φ
    constructor

    /-
    Step 2: Show φ ≠ 0.

    If iψ = 0 and i ≠ 0, then ψ = 0. But ψ ≠ 0 by hypothesis.
    -/
    · intro hφ_zero
      have : ψ = 0 := by
        have h := hφ_zero
        simp only [φ] at h
        exact (smul_eq_zero.mp h).resolve_left I_ne_zero
      exact hψ_ne this

    /-
    Step 3: Verify Uφ = -φ.

    Since Aψ = 0:
      Uφ = U(iψ) = (A - iI)ψ = Aψ - iψ = 0 - iψ = -iψ = -φ ✓

    The calculation uses:
    - R_{-i}(φ) = ψ (by uniqueness: (A + iI)ψ = φ)
    - Uφ = (A - iI) · R_{-i}(φ) = (A - iI)ψ
    -/
    · -- First establish that R_{-i}(φ) = ψ
      have h_Rφ : Resolvent.resolvent_at_neg_i gen hsa φ = ψ := by
        exact Resolvent.resolvent_at_neg_i_unique gen hsa φ
          (Resolvent.resolvent_at_neg_i gen hsa φ) ψ
          (Resolvent.resolvent_solution_mem_plus gen hsa φ) hψ_mem
          (Resolvent.resolvent_solution_eq_plus gen hsa φ) hφ_eq

      -- Now compute Uφ
      calc cayleyTransform gen hsa φ
          = gen.op ⟨Resolvent.resolvent_at_neg_i gen hsa φ,
                   Resolvent.resolvent_solution_mem_plus gen hsa φ⟩ -
            I • Resolvent.resolvent_at_neg_i gen hsa φ := cayleyTransform_apply gen hsa φ
        _ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by simp_all only [ne_eq, zero_add, map_smul, zero_sub, φ]
        _ = 0 - I • ψ := by rw [h_Aψ]        -- Aψ = 0
        _ = -φ := by simp [φ]                -- -iψ = -(iψ) = -φ




/-!
## The Inverse Cayley Transform

Having constructed the forward Cayley transform A ↦ U and proven it produces
a unitary operator, we now develop the inverse: U ↦ A.

### The Inverse Formula

For a unitary U with -1 not an eigenvalue, the inverse Cayley transform is:

    A = i(I + U)(I - U)⁻¹

The domain of A is precisely Range(I - U).

### Why This Works: Algebraic Motivation

Starting from U = (A - iI)(A + iI)⁻¹, we solve for A.

Let φ = (A + iI)ψ for ψ ∈ D(A). Then Uφ = (A - iI)ψ.

Compute:
- (I - U)φ = φ - Uφ = (A + iI)ψ - (A - iI)ψ = 2iψ
- (I + U)φ = φ + Uφ = (A + iI)ψ + (A - iI)ψ = 2Aψ

From the first equation: ψ = (2i)⁻¹(I - U)φ = (-i/2)(I - U)φ
Substituting into the second: 2Aψ = (I + U)φ

Therefore: Aψ = (1/2)(I + U)φ = (1/2)(I + U) · (I - U)⁻¹ · (2iψ)
                               = i(I + U)(I - U)⁻¹ ψ

This is the inverse Cayley formula, valid on D(A) = Range(I - U).

### Key Lemmas

We establish two fundamental identities:

1. **one_minus_cayley_apply:** (I - U)φ = 2i·ψ  where φ = (A + iI)ψ
2. **one_plus_cayley_apply:**  (I + U)φ = 2·Aψ  where φ = (A + iI)ψ

These directly encode the relationship between:
- The domain element ψ ∈ D(A)
- The "transformed" element φ = (A + iI)ψ ∈ H
- The operators (I ± U)

### Significance

The inverse Cayley transform completes the bijection:

    { Self-adjoint A } ←――――→ { Unitary U with -1 ∉ σₚ(U) }
                        Cayley
                       ←――――→
                    Inverse Cayley

This is the foundation for:
- Transferring spectral theory from U to A
- Proving Stone's theorem (one-parameter unitary groups ↔ self-adjoint generators)
- The functional calculus for unbounded self-adjoint operators
-/

/--
**(I - U) extracts the domain element:** If φ = (A + iI)ψ, then (I - U)φ = 2i·ψ.

### Statement

For ψ ∈ D(A), let φ = (A + iI)ψ = Aψ + iψ. Then:

    (I - U)φ = 2i · ψ

### Derivation

    (I - U)φ = φ - Uφ
             = (A + iI)ψ - (A - iI)ψ      [since Uφ = (A - iI)ψ]
             = Aψ + iψ - Aψ + iψ
             = 2iψ

### Significance

This identity shows that (I - U) "undoes" the (A + iI) part of the Cayley
transform, leaving behind (a multiple of) the original domain element ψ.

Rearranging: **ψ = (2i)⁻¹(I - U)φ = (-i/2)(I - U)φ**

This is the key to recovering D(A) from U: the domain D(A) consists
precisely of elements of the form (-i/2)(I - U)φ for φ ∈ H.

### Role in Inverse Cayley

Combined with `one_plus_cayley_apply`, this gives:
- From (I - U)φ we recover ψ
- From (I + U)φ we recover Aψ
- Together: A = i(I + U)(I - U)⁻¹
-/
lemma one_minus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.smul_apply]

  /-
  Key step: Identify R_{-i}(φ) = ψ.

  The resolvent R_{-i} solves (A + iI)x = φ.
  But ψ satisfies (A + iI)ψ = Aψ + iψ = φ by definition.
  By uniqueness of the resolvent solution, R_{-i}(φ) = ψ.
  -/
  have h_R : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
    apply Resolvent.resolvent_at_neg_i_unique gen hsa _
      (Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ)) ψ
      (Resolvent.resolvent_solution_mem_plus gen hsa _) hψ
      (Resolvent.resolvent_solution_eq_plus gen hsa _)
    rfl

  /-
  Now compute (I - U)φ:

  Recall U = I - 2i·R_{-i}, so:
    (I - U)φ = φ - Uφ
             = φ - (φ - 2i·R_{-i}(φ))
             = 2i·R_{-i}(φ)
             = 2i·ψ
  -/
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) -
       ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) := by abel
    _ = (2 * I) • ψ := by rw [h_R]

/--
**(I + U) extracts the operator output:** If φ = (A + iI)ψ, then (I + U)φ = 2·Aψ.

### Statement

For ψ ∈ D(A), let φ = (A + iI)ψ = Aψ + iψ. Then:

    (I + U)φ = 2 · Aψ

### Derivation

    (I + U)φ = φ + Uφ
             = (A + iI)ψ + (A - iI)ψ      [since Uφ = (A - iI)ψ]
             = Aψ + iψ + Aψ - iψ
             = 2Aψ

### Significance

This identity shows that (I + U) "doubles" the A-component while canceling
the i-component. Combined with `one_minus_cayley_apply`:

    (I - U)φ = 2iψ   →   ψ = (-i/2)(I - U)φ
    (I + U)φ = 2Aψ   →   Aψ = (1/2)(I + U)φ

Combining: **Aψ = (1/2)(I + U)φ = (1/2)(I + U) · (2i) · ((-i/2)(I - U)φ)**
                                = i(I + U)(I - U)⁻¹ ψ

### The Inverse Cayley Formula

This derivation shows:

    A = i(I + U)(I - U)⁻¹

where the domain of the right side is Range(I - U) = D(A).
-/
lemma one_plus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  simp only [cayleyTransform, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]

  -- Same key step: R_{-i}(φ) = ψ
  have h_R : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
    apply Resolvent.resolvent_at_neg_i_unique gen hsa _
      (Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ)) ψ
      (Resolvent.resolvent_solution_mem_plus gen hsa _) hψ
      (Resolvent.resolvent_solution_eq_plus gen hsa _)
    rfl

  /-
  Compute (I + U)φ:

    (I + U)φ = φ + Uφ
             = φ + (φ - 2i·R_{-i}(φ))
             = 2φ - 2i·ψ
             = 2(Aψ + iψ) - 2iψ
             = 2Aψ + 2iψ - 2iψ
             = 2Aψ
  -/
  calc (gen.op ⟨ψ, hψ⟩ + I • ψ) +
       ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ))
      = (gen.op ⟨ψ, hψ⟩ + I • ψ) + ((gen.op ⟨ψ, hψ⟩ + I • ψ) - (2 * I) • ψ) := by rw [h_R]
    _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
      -- Algebraic simplification: 2φ - 2iψ = 2(Aψ + iψ) - 2iψ = 2Aψ
      have h1 : I • ψ + I • ψ = (2 * I) • ψ := by rw [← two_smul ℂ (I • ψ), smul_smul]
      calc gen.op ⟨ψ, hψ⟩ + I • ψ + (gen.op ⟨ψ, hψ⟩ + I • ψ - (2 * I) • ψ)
          = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (I • ψ + I • ψ) - (2 * I) • ψ := by abel
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ + (2 * I) • ψ - (2 * I) • ψ := by rw [h1]
        _ = gen.op ⟨ψ, hψ⟩ + gen.op ⟨ψ, hψ⟩ := by abel
        _ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by rw [two_smul]

/--
**The inverse Cayley relation:** Connecting (I ± U) to the generator A.

### Statement

For ψ ∈ D(A), with φ = (A + iI)ψ and U the Cayley transform:

    2i · Aψ = i · (I + U)φ

### Significance

This theorem packages the relationship between the two key lemmas:
- `one_minus_cayley_apply`: (I - U)φ = 2iψ
- `one_plus_cayley_apply`:  (I + U)φ = 2Aψ

Combining them:
    (I + U)φ = 2Aψ
    i · (I + U)φ = 2i · Aψ ✓

This is the algebraic content of the inverse Cayley formula A = i(I+U)(I-U)⁻¹,
expressed without explicitly inverting (I - U).

### Why Express It This Way?

In Lean, defining the inverse (I - U)⁻¹ requires showing (I - U) is invertible,
which requires -1 ∉ σₚ(U). By stating the relation without explicit inversion,
we separate the algebraic identity from the invertibility question.

The full inverse Cayley formula follows when we additionally prove:
1. (I - U) is injective (from -1 ∉ σₚ(U))
2. Range(I - U) = D(A)
-/
theorem inverse_cayley_relation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    -- The key relation: 2i·Aψ = i·(I+U)φ
    (2 * I) • gen.op ⟨ψ, hψ⟩ = I • ((ContinuousLinearMap.id ℂ H + U) φ) := by
  -- Use one_plus_cayley_apply: (I + U)φ = 2·Aψ
  have h_plus := one_plus_cayley_apply gen hsa ψ hψ
  -- Then i·(I + U)φ = i·(2·Aψ) = 2i·Aψ ✓
  simp only [h_plus, smul_smul]
  ring_nf


/-!
### The Inverse Cayley Structure

Having established the two fundamental identities:
- `one_minus_cayley_apply`: (I - U)φ = 2iψ
- `one_plus_cayley_apply`:  (I + U)φ = 2Aψ

We now assemble these into the full inverse Cayley structure:
1. Package both identities together (`inverse_cayley_formula`)
2. Characterize Range(I - U) (`range_one_minus_cayley`)
3. Express ψ in terms of (I - U)φ (`inverse_cayley_domain`)
4. State the complete bijection (`cayley_bijection`)

The key insight is that the map ψ ↦ φ = (A + iI)ψ from D(A) to H is
inverted by φ ↦ (-i/2)(I - U)φ, and simultaneously the operator A
is recovered by φ ↦ (1/2)(I + U)φ.
-/

/--
**The inverse Cayley formula (packaged):** Both fundamental identities together.

### Statement

For ψ ∈ D(A), let φ = (A + iI)ψ. Then:
1. (I - U)φ = 2i·ψ
2. (I + U)φ = 2·Aψ

### Why Package Them?

These two identities are the complete algebraic content of the inverse
Cayley transform. From them, one can derive:

    ψ = (-i/2)(I - U)φ     (inverting the first)
    Aψ = (1/2)(I + U)φ     (inverting the second)

And therefore:

    A = (1/2)(I + U) ∘ ((-i/2)(I - U))⁻¹ = i(I + U)(I - U)⁻¹

### Use Case

This theorem is useful when you need both identities simultaneously,
for instance when proving that the forward and inverse Cayley transforms
are mutual inverses.
-/
theorem inverse_cayley_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    -- The two fundamental relations that define the inverse Cayley
    (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ ∧
    (ContinuousLinearMap.id ℂ H + U) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩ := by
  exact ⟨one_minus_cayley_apply gen hsa ψ hψ, one_plus_cayley_apply gen hsa ψ hψ⟩

/--
**Range characterization:** D(A) embeds into Range(I - U) via scaling.

### Statement

For every ψ ∈ D(A), the element 2i·ψ lies in Range(I - U).

Concretely: there exists φ ∈ H with (I - U)φ = 2i·ψ, namely φ = (A + iI)ψ.

### Significance

This is the first step toward proving Range(I - U) = D(A) (up to scaling).

The full characterization is:
- **Forward:** ψ ∈ D(A) ⟹ 2i·ψ ∈ Range(I - U)  [this lemma]
- **Backward:** χ ∈ Range(I - U) ⟹ (-i/2)χ ∈ D(A)  [requires more work]

Together: **D(A) = (-i/2) · Range(I - U)**

### Why the Factor of 2i?

The factor 2i is an artifact of the symmetric form of the Cayley transform.
Some authors define U = (A - iI)(A + iI)⁻¹ and others use different
normalizations. Our choice makes the forward transform simple at the
cost of this factor in the inverse.

To work with D(A) directly (without the 2i), use `inverse_cayley_domain`.
-/
lemma range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ ψ : H, ψ ∈ gen.domain →
      ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ := by
  intro ψ hψ
  use gen.op ⟨ψ, hψ⟩ + I • ψ
  exact one_minus_cayley_apply gen hsa ψ hψ

/--
**Domain recovery formula:** Express ψ ∈ D(A) in terms of (I - U)φ.

### Statement

For ψ ∈ D(A), let φ = (A + iI)ψ. Then:

    ψ = (-i/2) · (I - U)φ

### Derivation

From `one_minus_cayley_apply`: (I - U)φ = 2i·ψ

Solving for ψ:
    ψ = (2i)⁻¹ · (I - U)φ
      = (1/2i) · (I - U)φ
      = (-i/2) · (I - U)φ    [since 1/i = -i]

### Significance

This formula shows how to recover the domain element ψ from any
element φ in the range of (A + iI). It is the "inverse map" for
the transformation ψ ↦ (A + iI)ψ.

**Key insight:** The domain D(A) is characterized as:

    D(A) = { (-i/2)(I - U)φ : φ ∈ H }
         = (-i/2) · Range(I - U)

Since (I - U) is injective when -1 ∉ σₚ(U), and surjectivity of (A + iI)
gives Range(I - U) = H in the dense sense, we get D(A) dense in H
(as required for self-adjoint operators).
-/
theorem inverse_cayley_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ψ = ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - U) φ) := by
  have h_minus := one_minus_cayley_apply gen hsa ψ hψ

  /-
  We have: (I - U)φ = 2i·ψ
  We want: ψ = (-i/2)·(I - U)φ

  This is just scalar arithmetic: (-i/2) · (2i) = (-i · 2i) / 2 = (2) / 2 = 1
  -/
  have h_inv : ((-I) / 2) • ((2 * I) • ψ) = ψ := by
    rw [smul_smul]
    have : (-I) / 2 * (2 * I) = 1 := by
      field_simp
      simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
                     Pi.sub_apply, id_eq, map_add, map_smul, I_sq, neg_neg]
    rw [this, one_smul]
  rw [← h_minus] at h_inv
  exact h_inv.symm

/--
**The complete bijection:** Both inversion formulas together.

### Statement

For ψ ∈ D(A), let φ = (A + iI)ψ. Then:

1. **Domain recovery:**   (-i/2) · (I - U)φ = ψ
2. **Operator recovery:** (1/2) · (I + U)φ = Aψ

### The Bijection Picture

This theorem establishes that the map

    Φ : D(A) → H,  ψ ↦ (A + iI)ψ

has explicit left inverses for recovering both ψ and Aψ:

    ψ  = Φ⁻¹_dom(φ) := (-i/2)(I - U)φ
    Aψ = Φ⁻¹_op(φ)  := (1/2)(I + U)φ

### Significance for the Cayley Correspondence

This is the algebraic heart of the bijection:

    { Self-adjoint A on D(A) } ←→ { Unitary U with -1 ∉ σₚ(U) }

**Forward (A ↦ U):**
- U = (A - iI)(A + iI)⁻¹ = I - 2i·R_{-i}

**Backward (U ↦ A):**
- D(A) = (-i/2) · Range(I - U)
- Aψ = (1/2)(I + U) · (2i/(−i)) · ψ = i(I + U)(I - U)⁻¹ ψ

### The Commutative Diagram
```
    D(A) ――――A――――→ H
     |              |
     | (A+iI)       | (A-iI)
     ↓              ↓
     H ――――U――――→ H
     |              |
     | (-i/2)(I-U)  | (1/2)(I+U)
     ↓              ↓
    D(A) ――――A――――→ H
```

Both vertical compositions are the identity (on appropriate domains).
-/
theorem cayley_bijection {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ) = ψ ∧
    ((1 : ℂ) / 2) • ((ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ) = gen.op ⟨ψ, hψ⟩ := by
  constructor
  /-
  Part 1: (-i/2)(I - U)φ = ψ

  This is exactly inverse_cayley_domain, just with equality flipped.
  -/
  · exact (inverse_cayley_domain gen hsa ψ hψ).symm

  /-
  Part 2: (1/2)(I + U)φ = Aψ

  From one_plus_cayley_apply: (I + U)φ = 2·Aψ
  Therefore: (1/2)(I + U)φ = (1/2)·2·Aψ = Aψ
  -/
  · have h := one_plus_cayley_apply gen hsa ψ hψ
    simp only [h, smul_smul]
    norm_num



/-!
## The Inverse Cayley Operator

We now construct the inverse Cayley transform as an actual linear operator.
Given a unitary U with ±1 not eigenvalues, we define:

    A = i(I + U)(I - U)⁻¹

as a linear map on the domain D(A) = Range(I - U).

### The Well-Definedness Problem

The formula A = i(I + U)(I - U)⁻¹ requires inverting (I - U). This raises
two questions:

1. **Is (I - U) injective?** Yes, if 1 ∉ σₚ(U).
   If (I - U)ψ = 0, then Uψ = ψ, so ψ is a 1-eigenvector.
   If 1 is not an eigenvalue, then ψ = 0.

2. **Is (I - U) surjective?** Generally no—Range(I - U) is a proper
   dense subspace of H. This is why A is unbounded: its domain is
   Range(I - U), not all of H.

### The Construction

For φ ∈ Range(I - U), there exists ψ ∈ H with (I - U)ψ = φ.
By injectivity (from 1 ∉ σₚ(U)), this ψ is unique.

We define: **A(φ) = i(I + U)ψ = i(Uψ + ψ)**

### Why We Need Both Eigenvalue Conditions

- **1 ∉ σₚ(U):** Ensures (I - U) is injective, so ψ is uniquely determined
  by φ. Without this, A would not be well-defined.

- **-1 ∉ σₚ(U):** Ensures Range(I - U) is dense in H (equivalently, that
  A is densely defined). This is needed for A to be self-adjoint, not
  merely symmetric.

### The Role of Unitarity

Unitarity (⟪Uψ, Uφ⟫ = ⟪ψ, φ⟫) is used in two ways:

1. **Linearity proofs:** The `map_add'` and `map_smul'` proofs use
   injectivity of (I - U), which comes from 1 ∉ σₚ(U).

2. **Symmetry proof:** The calculation ⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫ uses inner
   product preservation to cancel cross-terms.
-/

/--
**The inverse Cayley transform** as a linear operator.

### Definition

Given a unitary operator U : H →L[ℂ] H with 1 and -1 not eigenvalues,
we define the linear map:

    A : Range(I - U) →ₗ[ℂ] H
    A(φ) = i(I + U)ψ  where (I - U)ψ = φ

### Type Signature

- **Domain:** `LinearMap.range (ContinuousLinearMap.id ℂ H - U)`
  This is the submodule Range(I - U) ⊆ H.

- **Codomain:** H

- **Hypotheses:**
  - `hU`: U preserves inner products (unitarity: ⟪Uψ, Uφ⟫ = ⟪ψ, φ⟫)
  - `h_one`: 1 is not an eigenvalue (Uψ = ψ ⟹ ψ = 0)
  - `h_neg_one`: -1 is not an eigenvalue (Uψ = -ψ ⟹ ψ = 0)

### Implementation Notes

The definition uses `Classical.choose` to select the witness ψ for
each φ ∈ Range(I - U). The proof obligations are:

1. **`map_add'`:** A(φ₁ + φ₂) = A(φ₁) + A(φ₂)
   - Key step: If (I-U)ψ₁ = φ₁ and (I-U)ψ₂ = φ₂, then (I-U)(ψ₁+ψ₂) = φ₁+φ₂
   - The chosen witness for φ₁+φ₂ equals ψ₁+ψ₂ by injectivity

2. **`map_smul'`:** A(c·φ) = c·A(φ)
   - Similar: the witness for c·φ equals c·ψ by injectivity

### Algebraic Verification

For φ = (I - U)ψ, we have:
    A(φ) = i(Uψ + ψ) = i(I + U)ψ

If φ came from the forward Cayley transform of some self-adjoint operator B,
say φ = (B + iI)χ, then the inverse Cayley should give A = B.

Indeed, by `cayley_bijection`:
- χ = (-i/2)(I - U)φ
- Bχ = (1/2)(I + U)φ

The inverse Cayley formula recovers B correctly (up to domain identification).

### Relation to the Forward Cayley

If A is defined via `inverseCayleyOp` from U, and we then apply the
forward Cayley transform to A, we should recover U. This "round-trip"
property is what makes the Cayley transform a bijection.
-/
noncomputable def inverseCayleyOp (U : H →L[ℂ] H)
    (_ /-hU-/ : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)       -- unitary
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)                     -- 1 not eigenvalue (injectivity)
    (_ /-h_neg_one-/ : ∀ ψ, U ψ = -ψ → ψ = 0) :       -- -1 not eigenvalue (density)
    LinearMap.range (ContinuousLinearMap.id ℂ H - U) →ₗ[ℂ] H where

  /-
  The underlying function: φ ↦ i(Uψ + ψ) where (I - U)ψ = φ.

  We use Classical.choose to extract the witness ψ from the existence
  proof hφ : φ ∈ Range(I - U).
  -/
  toFun := fun ⟨φ, hφ⟩ =>
    let ψ := Classical.choose hφ
    I • (U ψ + ψ)

  /-
  ═══════════════════════════════════════════════════════════════════════════
  ADDITIVITY: A(φ₁ + φ₂) = A(φ₁) + A(φ₂)
  ═══════════════════════════════════════════════════════════════════════════

  Strategy:
  1. Get witnesses ψ₁, ψ₂ for φ₁, φ₂
  2. Show ψ₁ + ψ₂ witnesses φ₁ + φ₂
  3. By injectivity of (I - U), the chosen witness for φ₁ + φ₂ equals ψ₁ + ψ₂
  4. Then A(φ₁ + φ₂) = i(U(ψ₁+ψ₂) + (ψ₁+ψ₂)) = i(Uψ₁+ψ₁) + i(Uψ₂+ψ₂)
  -/
  map_add' := by
    intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    simp only [smul_add]

    -- Step 1: Extract witnesses for φ₁ and φ₂
    set ψ₁ := Classical.choose hφ₁ with hψ₁_def
    set ψ₂ := Classical.choose hφ₂ with hψ₂_def
    have hψ₁ : (ContinuousLinearMap.id ℂ H - U) ψ₁ = φ₁ := Classical.choose_spec hφ₁
    have hψ₂ : (ContinuousLinearMap.id ℂ H - U) ψ₂ = φ₂ := Classical.choose_spec hφ₂

    -- Step 2: Construct a witness for φ₁ + φ₂ (namely ψ₁ + ψ₂)
    have hφ₁₂ : ∃ ψ, (ContinuousLinearMap.id ℂ H - U) ψ = φ₁ + φ₂ := ⟨ψ₁ + ψ₂, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
      rw [← hψ₁, ← hψ₂]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ₁₂ := Classical.choose hφ₁₂ with hψ₁₂_def
    have hψ₁₂ : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ = φ₁ + φ₂ := Classical.choose_spec hφ₁₂

    /-
    Step 3: Prove ψ₁₂ = ψ₁ + ψ₂ using injectivity of (I - U).

    We have (I - U)ψ₁₂ = φ₁ + φ₂ = (I - U)(ψ₁ + ψ₂).
    So (I - U)(ψ₁₂ - ψ₁ - ψ₂) = 0.
    This means U(ψ₁₂ - ψ₁ - ψ₂) = ψ₁₂ - ψ₁ - ψ₂ (a fixed point).
    By h_one (1 ∉ σₚ(U)), we conclude ψ₁₂ - ψ₁ - ψ₂ = 0.
    -/
    have h_diff : ψ₁₂ = ψ₁ + ψ₂ := by
      have h_eq : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ =
                  (ContinuousLinearMap.id ℂ H - U) (ψ₁ + ψ₂) := by
        rw [hψ₁₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
        rw [← hψ₁, ← hψ₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                   map_sub, map_add]
        rw [sub_eq_zero]
        convert h_eq using 1
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        rw [map_add]
        abel
      -- (I - U)(ψ₁₂ - ψ₁ - ψ₂) = 0 means ψ₁₂ - ψ₁ - ψ₂ is a fixed point of U
      have h_fixed : U (ψ₁₂ - (ψ₁ + ψ₂)) = ψ₁₂ - (ψ₁ + ψ₂) := by
        have : ψ₁₂ - (ψ₁ + ψ₂) - U (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      -- By h_one: fixed points are zero
      exact eq_of_sub_eq_zero (h_one _ h_fixed)

    -- Step 4: Use h_diff to complete the proof
    rw [h_diff, map_add]
    simp only [smul_add]
    abel

  /-
  ═══════════════════════════════════════════════════════════════════════════
  SCALAR MULTIPLICATION: A(c·φ) = c·A(φ)
  ═══════════════════════════════════════════════════════════════════════════

  Same strategy: the witness for c·φ is c·ψ by injectivity.
  -/
  map_smul' := by
    intro c ⟨φ, hφ⟩
    simp only [RingHom.id_apply, smul_add]

    -- Get witness for φ
    set ψ := Classical.choose hφ with hψ_def
    have hψ : (ContinuousLinearMap.id ℂ H - U) ψ = φ := Classical.choose_spec hφ

    -- Construct witness for c·φ (namely c·ψ)
    have hcφ : ∃ ψ', (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := ⟨c • ψ, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_smul]
      rw [← hψ]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ' := Classical.choose hcφ with hψ'_def
    have hψ' : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := Classical.choose_spec hcφ

    -- Prove ψ' = c·ψ by injectivity
    have h_diff : ψ' = c • ψ := by
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ' - c • ψ) = 0 := by
        have eq1 : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := hψ'
        have eq2 : (ContinuousLinearMap.id ℂ H - U) ψ = φ := hψ
        simp only [map_sub, map_smul, eq1, eq2]
        abel
      have h_fixed : U (ψ' - c • ψ) = ψ' - c • ψ := by
        have : ψ' - c • ψ - U (ψ' - c • ψ) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      exact eq_of_sub_eq_zero (h_one _ h_fixed)

    -- Complete: A(c·φ) = i(Uψ' + ψ') = i(U(cψ) + cψ) = c·i(Uψ + ψ) = c·A(φ)
    rw [h_diff, map_smul, smul_comm c I (U ψ), smul_comm c I ψ]

/--
**The inverse Cayley transform produces a symmetric operator.**

### Statement

For all ψ, φ in the domain Range(I - U):

    ⟪A(ψ), φ⟫ = ⟪ψ, A(φ)⟫

where A = inverseCayleyOp U.

### Significance

Symmetry is the first step toward self-adjointness. To get full
self-adjointness, we would additionally need to show D(A) = D(A*),
which follows from the density of Range(I - U) (ensured by -1 ∉ σₚ(U)).

### Proof Idea

Let ψ = (I - U)χ₁ and φ = (I - U)χ₂ for unique χ₁, χ₂ (by injectivity).

Then:
- A(ψ) = i(Uχ₁ + χ₁)
- A(φ) = i(Uχ₂ + χ₂)

We must show:
    ⟪i(Uχ₁ + χ₁), χ₂ - Uχ₂⟫ = ⟪χ₁ - Uχ₁, i(Uχ₂ + χ₂)⟫

Expanding both sides and using unitarity (⟪Uχ₁, Uχ₂⟫ = ⟪χ₁, χ₂⟫), the
cross-terms cancel and we get equality.

### The Calculation in Detail

LHS = ⟪i(Uχ₁ + χ₁), χ₂ - Uχ₂⟫
    = i(⟪Uχ₁, χ₂⟫ - ⟪Uχ₁, Uχ₂⟫ + ⟪χ₁, χ₂⟫ - ⟪χ₁, Uχ₂⟫)
    = i(⟪Uχ₁, χ₂⟫ - ⟪χ₁, χ₂⟫ + ⟪χ₁, χ₂⟫ - ⟪χ₁, Uχ₂⟫)   [unitarity]
    = i(⟪Uχ₁, χ₂⟫ - ⟪χ₁, Uχ₂⟫)

RHS = ⟪χ₁ - Uχ₁, i(Uχ₂ + χ₂)⟫
    = conj(i)(⟪χ₁, Uχ₂⟫ + ⟪χ₁, χ₂⟫ - ⟪Uχ₁, Uχ₂⟫ - ⟪Uχ₁, χ₂⟫)
    = -i(⟪χ₁, Uχ₂⟫ + ⟪χ₁, χ₂⟫ - ⟪χ₁, χ₂⟫ - ⟪Uχ₁, χ₂⟫)   [unitarity]
    = -i(⟪χ₁, Uχ₂⟫ - ⟪Uχ₁, χ₂⟫)
    = i(⟪Uχ₁, χ₂⟫ - ⟪χ₁, Uχ₂⟫)

LHS = RHS ✓

### Physical Interpretation

Symmetry of A means ⟪Aψ, ψ⟫ ∈ ℝ for all ψ in the domain—the expectation
value of the observable A is always real. This is a necessary condition
for A to represent a physical observable in quantum mechanics.
-/
theorem inverseCayleyOp_symmetric (U : H →L[ℂ] H)
    (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) :
    ∀ ψ φ : LinearMap.range (ContinuousLinearMap.id ℂ H - U),
      ⟪inverseCayleyOp U hU h_one h_neg_one ψ, (φ : H)⟫_ℂ =
      ⟪(ψ : H), inverseCayleyOp U hU h_one h_neg_one φ⟫_ℂ := by
  intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩

  -- Step 1: Extract witnesses χ₁, χ₂ for φ₁, φ₂
  set χ₁ := Classical.choose hφ₁ with hχ₁_def
  set χ₂ := Classical.choose hφ₂ with hχ₂_def
  have hχ₁ : (ContinuousLinearMap.id ℂ H - U) χ₁ = φ₁ := Classical.choose_spec hφ₁
  have hχ₂ : (ContinuousLinearMap.id ℂ H - U) χ₂ = φ₂ := Classical.choose_spec hφ₂

  -- Step 2: Express φᵢ in expanded form
  have hφ₁_eq : φ₁ = χ₁ - U χ₁ := by
    rw [← hχ₁]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hφ₂_eq : φ₂ = χ₂ - U χ₂ := by
    rw [← hχ₂]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]

  -- Coercion lemmas
  have hcoe₁ : (⟨φ₁, hφ₁⟩ : LinearMap.range (ContinuousLinearMap.id ℂ H - U)).val = φ₁ := rfl
  have hcoe₂ : (⟨φ₂, hφ₂⟩ : LinearMap.range (ContinuousLinearMap.id ℂ H - U)).val = φ₂ := rfl

  /-
  Step 3: Unfold the definitions.

  We need to show:
    ⟪A(φ₁), φ₂⟫ = ⟪φ₁, A(φ₂)⟫

  where A(φ₁) = i(Uχ₁ + χ₁) and A(φ₂) = i(Uχ₂ + χ₂).

  Substituting φ₁ = χ₁ - Uχ₁ and φ₂ = χ₂ - Uχ₂:
    ⟪i(Uχ₁ + χ₁), χ₂ - Uχ₂⟫ = ⟪χ₁ - Uχ₁, i(Uχ₂ + χ₂)⟫
  -/
  show ⟪I • (U χ₁ + χ₁), φ₂⟫_ℂ = ⟪φ₁, I • (U χ₂ + χ₂)⟫_ℂ

  rw [hφ₁_eq, hφ₂_eq]

  -- Pull out the scalar i (note: ⟨i·x, y⟩ = i·⟨x,y⟩ and ⟨x, i·y⟩ = conj(i)·⟨x,y⟩ = -i·⟨x,y⟩)
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]

  /-
  Step 4: Expand the inner products using bilinearity.

  LHS: i · ⟨Uχ₁ + χ₁, χ₂ - Uχ₂⟩
  RHS: (-i) · ⟨χ₁ - Uχ₁, Uχ₂ + χ₂⟩

  We need: i · ⟨Uχ₁ + χ₁, χ₂ - Uχ₂⟩ = (-i) · ⟨χ₁ - Uχ₁, Uχ₂ + χ₂⟩

  Equivalently: ⟨Uχ₁ + χ₁, χ₂ - Uχ₂⟩ = -⟨χ₁ - Uχ₁, Uχ₂ + χ₂⟩
  -/
  rw [inner_add_left, inner_sub_right, inner_sub_right]
  rw [inner_sub_left, inner_add_right, inner_add_right]

  /-
  Step 5: Apply unitarity to simplify.

  The key: ⟨Uχ₁, Uχ₂⟩ = ⟨χ₁, χ₂⟩

  This causes the ⟨χ₁, χ₂⟩ terms to cancel on both sides.
  -/
  rw [hU χ₁ χ₂]
  simp only [RCLike.star_def, conj_I, sub_add_sub_cancel, neg_mul]
  ring



/-!
## Consequences of Unitarity

Having established that the Cayley transform is unitary (U*U = UU* = I),
we now extract specific consequences that are useful for applications.

### What We Establish

1. **Composition identities:** U ∘ U* = I and U* ∘ U = I (as operator equations)
2. **Invertibility:** U is a unit in the ring of bounded operators
3. **Operator norm:** ‖U‖ = 1 (isometries on nontrivial spaces have norm 1)

These are standard facts about unitary operators, specialized to the
Cayley transform.

### Why Separate Lemmas?

The theorem `cayleyTransform_unitary` packages both conditions as a
conjunction. These lemmas extract them individually for convenience,
and derive further consequences (invertibility, norm).
-/

/--
**Right inverse property:** U ∘ U* = I.

### Statement

The Cayley transform composed with its adjoint (on the right) is the identity.

### Relation to Unitarity

This is the second component of the unitarity condition:
- `Unitary U` means `U* ∘ U = I ∧ U ∘ U* = I`
- This lemma extracts `U ∘ U* = I`

### Use Case

This form is convenient when you need to simplify expressions like
U(U*ψ) = ψ, or when working with the adjoint as a right inverse.
-/
lemma cayleyTransform_comp_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).comp (cayleyTransform gen hsa).adjoint =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.2

/--
**Left inverse property:** U* ∘ U = I.

### Statement

The adjoint of the Cayley transform composed with U (on the left) is the identity.

### Relation to Unitarity

This is the first component of the unitarity condition.
It is equivalent to inner product preservation: ⟪Uψ, Uφ⟫ = ⟪ψ, φ⟫.

### Use Case

This form is convenient when you need to simplify expressions like
U*(Uψ) = ψ, or when showing U is injective (since U*U = I implies
injectivity of U).
-/
lemma cayleyTransform_adjoint_comp {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  exact hU.1

/--
**Invertibility:** The Cayley transform is a unit in the operator ring.

### Statement

The Cayley transform is invertible (IsUnit) in the ring of bounded
linear operators H →L[ℂ] H.

### The Inverse

The inverse of U is its adjoint U*:
- U · U* = I  (right inverse)
- U* · U = I  (left inverse)

So U⁻¹ = U* in the group of units.

### Significance

This allows us to use general lemmas about units/invertible elements.
For instance, we can form U⁻¹ in expressions and use ring tactics.

### Connection to the Inverse Cayley

Note that `IsUnit U` concerns U as a bounded operator on all of H.
The inverse Cayley transform A = i(I+U)(I-U)⁻¹ is a different kind of
inverse—it inverts the *correspondence* between A and U, not U itself
as an operator.
-/
lemma cayleyTransform_isUnit {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    IsUnit (cayleyTransform gen hsa) := by
  refine ⟨⟨cayleyTransform gen hsa, (cayleyTransform gen hsa).adjoint, ?_, ?_⟩, rfl⟩
  · exact cayleyTransform_comp_adjoint gen hsa
  · exact cayleyTransform_adjoint_comp gen hsa

/--
**Left inverse (alternate proof):** U* ∘ U = I via inner products.

### Statement

Same as `cayleyTransform_adjoint_comp`, but with a proof that explicitly
uses inner product preservation.

### Proof Strategy

To show U*U = I, we prove ⟪(U*U)ψ, φ⟫ = ⟪ψ, φ⟫ for all ψ, φ.

By definition of adjoint: ⟪U*Uψ, φ⟫ = ⟪Uψ, Uφ⟫.
By unitarity: ⟪Uψ, Uφ⟫ = ⟪ψ, φ⟫.
By non-degeneracy of inner product: U*U = I.

### Why Keep Both Proofs?

The original `cayleyTransform_adjoint_comp` extracts from the packaged
unitarity theorem. This version shows the direct calculation, which
can be instructive and is sometimes needed when the inner product
form is more convenient.
-/
lemma cayleyTransform_adjoint_comp' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H := by
  have hU := cayleyTransform_unitary gen hsa
  ext ψ
  apply ext_inner_right ℂ
  intro φ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary hU ψ φ

/--
**Operator norm:** ‖U‖ = 1.

### Statement

The operator norm of the Cayley transform equals 1 (assuming H is nontrivial).

### Why Norm 1?

For any isometry U (satisfying ‖Uψ‖ = ‖ψ‖):

**Upper bound (‖U‖ ≤ 1):**
By definition, ‖U‖ = sup { ‖Uψ‖ : ‖ψ‖ ≤ 1 }.
Since ‖Uψ‖ = ‖ψ‖ ≤ 1 for ‖ψ‖ ≤ 1, we have ‖U‖ ≤ 1.

**Lower bound (1 ≤ ‖U‖):**
For any nonzero ψ, we have ‖Uψ‖/‖ψ‖ = 1.
Since ‖U‖ ≥ ‖Uψ‖/‖ψ‖ for all nonzero ψ, we have ‖U‖ ≥ 1.

### The Nontriviality Condition

We require `[Nontrivial H]` (i.e., H ≠ {0}) to ensure nonzero vectors exist.
On the trivial space H = {0}, the only operator is the zero operator,
which has norm 0, not 1.

### Significance

The fact that ‖U‖ = 1 is important for:
- Spectral radius considerations: ρ(U) ≤ ‖U‖ = 1
- Convergence of operator series involving U
- Stability of numerical algorithms using the Cayley transform
-/
theorem cayleyTransform_norm_one {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ‖cayleyTransform gen hsa‖ = 1 := by
  set U := cayleyTransform gen hsa
  apply le_antisymm

  /-
  Upper bound: ‖U‖ ≤ 1

  For an isometry, ‖Uψ‖ = ‖ψ‖, so ‖Uψ‖ ≤ 1·‖ψ‖.
  By the definition of operator norm, this gives ‖U‖ ≤ 1.
  -/
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ψ
    have hU := cayleyTransform_unitary gen hsa
    have h_inner := hU.1
    -- Derive ‖Uψ‖ = ‖ψ‖ from U*U = I
    have h_norm : ‖U ψ‖ = ‖ψ‖ := by
      have : U.adjoint.comp U = 1 := h_inner
      have h_eq : ⟪U ψ, U ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
        calc ⟪U ψ, U ψ⟫_ℂ
            = ⟪U.adjoint (U ψ), ψ⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪(U.adjoint.comp U) ψ, ψ⟫_ℂ := rfl
          _ = ⟪ψ, ψ⟫_ℂ := by rw [this]; simp
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_eq
      have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by exact_mod_cast h_eq
      nlinarith [norm_nonneg (U ψ), norm_nonneg ψ, sq_nonneg (‖U ψ‖ - ‖ψ‖)]
    simp only [one_mul, h_norm, le_refl]

  /-
  Lower bound: 1 ≤ ‖U‖

  For any nonzero ψ, the ratio ‖Uψ‖/‖ψ‖ = 1 (since U is an isometry).
  Since ‖U‖ ≥ ‖Uψ‖/‖ψ‖ for all nonzero ψ, we have ‖U‖ ≥ 1.

  Note: This is where we use [Nontrivial H] to get a nonzero vector.
  -/
  · obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have hU := cayleyTransform_unitary gen hsa
    have h_inner := hU.1
    -- Same isometry calculation
    have h_norm : ‖U ψ‖ = ‖ψ‖ := by
      have : U.adjoint.comp U = 1 := h_inner
      have h_eq : ⟪U ψ, U ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
        calc ⟪U ψ, U ψ⟫_ℂ
            = ⟪U.adjoint (U ψ), ψ⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪(U.adjoint.comp U) ψ, ψ⟫_ℂ := rfl
          _ = ⟪ψ, ψ⟫_ℂ := by rw [this]; simp
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_eq
      have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by exact_mod_cast h_eq
      nlinarith [norm_nonneg (U ψ), norm_nonneg ψ, sq_nonneg (‖U ψ‖ - ‖ψ‖)]
    calc 1 = ‖U ψ‖ / ‖ψ‖ := by rw [h_norm]; field_simp
      _ ≤ ‖U‖ := by exact ContinuousLinearMap.ratio_le_opNorm U ψ


/-!
## Spectral Correspondence

The Cayley transform induces a bijection between spectra:

    σ(A) ⊆ ℝ  ←――――→  σ(U) ⊆ S¹ \ {-1}

via the Möbius transformation w = (z - i)/(z + i).

### The Möbius Map

The map μ : ℂ → ℂ defined by

    μ(z) = (z - i)/(z + i)

has remarkable properties:

1. **Maps ℝ to S¹:** For real z, we have |μ(z)| = |z - i|/|z + i| = 1
   (since z - i and z + i are complex conjugates).

2. **Maps upper half-plane to unit disk:** If Im(z) > 0, then |μ(z)| < 1.

3. **Maps lower half-plane to exterior:** If Im(z) < 0, then |μ(z)| > 1.

4. **Special points:**
   - μ(0) = -1
   - μ(∞) = 1
   - μ(i) = 0
   - μ(-i) = ∞

### The Resolvent Correspondence

The key theorem: **If Im(z) ≠ 0, then w = μ(z) is in the resolvent set of U.**

Equivalently: σ(U) ⊆ S¹ (since |w| ≠ 1 implies w ∉ σ(U)).

This is the spectral manifestation of the Cayley transform:
- A self-adjoint ⟹ σ(A) ⊆ ℝ ⟹ Im(z) ≠ 0 for z ∈ ρ(A)
- U unitary ⟹ σ(U) ⊆ S¹ ⟹ |w| ≠ 1 for w ∈ ρ(U)
- The Möbius map μ : ρ(A) → ρ(U) is a bijection

### Proof Strategy

We show U - wI is invertible by case analysis on |w|:

**Case |w| < 1:** Factor U - wI = U ∘ (I - wU*).
- Since U is unitary, U is invertible
- Since |w| < 1 and ‖U*‖ = 1, we have ‖wU*‖ < 1
- By Neumann series, I - wU* is invertible
- Therefore U - wI is invertible

**Case |w| > 1:** Factor U - wI = -w(I - w⁻¹U).
- Since |w| > 1, we have |w⁻¹| < 1
- Since ‖U‖ = 1, we have ‖w⁻¹U‖ < 1
- By Neumann series, I - w⁻¹U is invertible
- Since w ≠ 0, the scalar -w is invertible
- Therefore U - wI is invertible

The case |w| = 1 cannot occur when Im(z) ≠ 0, as we prove first.
-/

/--
**Resolvent correspondence:** The Cayley transform maps resolvents bijectively.

### Statement

Let z ∈ ℂ with Im(z) ≠ 0, and set w = (z - i)/(z + i).
Then U - wI is invertible (i.e., w is in the resolvent set of U).

### The Contrapositive

Equivalently: if w ∈ σ(U), then w = μ(z) for some z ∈ ℝ.

Since σ(U) ⊆ S¹ for unitary U, and μ(ℝ) = S¹, this shows σ(U) ⊆ μ(ℝ).

### Key Lemma: |w| ≠ 1 When Im(z) ≠ 0

The proof begins by showing that Im(z) ≠ 0 implies |w| ≠ 1.

Calculation:
    |w|² = |z - i|²/|z + i|²
         = (x² + (y-1)²)/(x² + (y+1)²)    [where z = x + iy]
         = (|z|² - 2y + 1)/(|z|² + 2y + 1)

This equals 1 iff the numerator equals the denominator, i.e., iff y = 0.

Therefore: Im(z) ≠ 0 ⟹ |w| ≠ 1.

### The Two Cases

**Case |w| < 1 (upper half-plane, Im(z) > 0):**

We factor: U - wI = U ∘ (I - wU*)

Proof of factorization:
    U(I - wU*) = U - wUU* = U - wI    [since UU* = I]

Since ‖wU*‖ ≤ |w| · ‖U*‖ = |w| < 1, the Neumann series converges:
    (I - wU*)⁻¹ = Σₙ (wU*)ⁿ

Therefore I - wU* is invertible, and U - wI = U ∘ (I - wU*) is invertible
(as the composition of two invertible operators).

**Case |w| > 1 (lower half-plane, Im(z) < 0):**

We factor: U - wI = -w(I - w⁻¹U)

Since |w⁻¹| < 1 and ‖U‖ = 1, we have ‖w⁻¹U‖ < 1.
By Neumann series, I - w⁻¹U is invertible.
Since w ≠ 0, the scalar -w is invertible.
Therefore U - wI is invertible.

### Physical Interpretation

In quantum mechanics:
- Self-adjoint operators (observables) have real spectrum
- Unitary operators (symmetries, time evolution) have spectrum on S¹
- The Cayley transform preserves this structure

The resolvent (A - zI)⁻¹ for Im(z) ≠ 0 is the "propagator" in physics.
This theorem shows the propagator structure is preserved by the Cayley map.

### Connection to Functional Calculus

This theorem is a key step in transferring the functional calculus from U to A:
- Bounded functions on S¹ can be applied to U (continuous functional calculus)
- Via μ⁻¹, these become bounded functions on ℝ applied to A
- This allows us to define f(A) for bounded Borel functions f on ℝ
-/
theorem cayley_maps_resolvent {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) :
    let w := (z - I) * (z + I)⁻¹
    IsUnit (cayleyTransform gen hsa - w • ContinuousLinearMap.id ℂ H) := by
  intro w

  /-
  ═══════════════════════════════════════════════════════════════════════════
  STEP 1: Prove |w| ≠ 1 when Im(z) ≠ 0
  ═══════════════════════════════════════════════════════════════════════════

  This is the key geometric fact. The Möbius map μ(z) = (z-i)/(z+i) satisfies:
  - μ maps ℝ → S¹ (the unit circle)
  - μ maps the upper half-plane → the open unit disk
  - μ maps the lower half-plane → the exterior of the unit disk

  Therefore |w| = 1 iff z ∈ ℝ iff Im(z) = 0.
  -/
  have hw_norm_ne_one : ‖w‖ ≠ 1 := by
    simp only [w, norm_mul, norm_inv]
    intro h_eq
    -- From |w| = 1, derive |z - i| = |z + i|
    have h_abs_eq : ‖z - I‖ = ‖z + I‖ := by
      have h_ne : ‖z + I‖ ≠ 0 := by
        simp_all only [ne_eq, norm_eq_zero]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [norm_zero, inv_zero, mul_zero, zero_ne_one]
      calc ‖z - I‖ = ‖z - I‖ / ‖z + I‖ * ‖z + I‖ := by field_simp
        _ = 1 * ‖z + I‖ := by exact congrFun (congrArg HMul.hMul h_eq) ‖z + I‖
        _ = ‖z + I‖ := one_mul _
    /-
    From |z - i| = |z + i|, we derive Im(z) = 0.

    |z - i|² = x² + (y - 1)²
    |z + i|² = x² + (y + 1)²

    Setting these equal:
      x² + (y - 1)² = x² + (y + 1)²
      (y - 1)² = (y + 1)²
      y² - 2y + 1 = y² + 2y + 1
      -4y = 0
      y = 0
    -/
    have : z.im = 0 := by
      have h1 : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq, Complex.I_re, Complex.I_im]
        ring
      have h2 : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq, Complex.I_re, Complex.I_im]
        ring
      have h3 : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 := by rw [h_abs_eq]
      rw [h1, h2] at h3
      nlinarith
    -- But Im(z) = 0 contradicts hz
    exact hz this

  /-
  ═══════════════════════════════════════════════════════════════════════════
  STEP 2: Case split on |w| < 1 or |w| > 1
  ═══════════════════════════════════════════════════════════════════════════

  Since |w| ≠ 1, we have either |w| < 1 or |w| > 1.
  Each case uses a different factorization and Neumann series argument.
  -/
  have hU := cayleyTransform_unitary gen hsa
  set U := cayleyTransform gen hsa with hU_def
  rcases hw_norm_ne_one.lt_or_gt with hw_lt | hw_gt

  /-
  ─────────────────────────────────────────────────────────────────────────
  CASE 1: |w| < 1 (z in upper half-plane)
  ─────────────────────────────────────────────────────────────────────────

  Factorization: U - wI = U ∘ (I - wU*)

  Strategy:
  1. ‖wU*‖ ≤ |w| · ‖U*‖ = |w| < 1
  2. By Neumann series, I - wU* is invertible
  3. Since U is invertible (unitary), U - wI = U ∘ (I - wU*) is invertible
  -/
  · -- Bound on ‖wU*‖
    have h_adj_norm : ‖w • U.adjoint‖ < 1 := by
      calc ‖w • U.adjoint‖
          ≤ ‖w‖ * ‖U.adjoint‖ := by exact
            ContinuousLinearMap.opNorm_smul_le w (ContinuousLinearMap.adjoint U)
        _ = ‖w‖ * 1 := by
          congr 1
          simp only [LinearIsometryEquiv.norm_map]
          exact cayleyTransform_norm_one gen hsa
        _ = ‖w‖ := mul_one _
        _ < 1 := hw_lt

    -- Neumann series: I - wU* is invertible
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w • U.adjoint) :=
      Resolvent.isUnit_one_sub (w • U.adjoint) h_adj_norm

    /-
    Factorization: U - wI = U ∘ (I - wU*)

    Proof: U(I - wU*) = U - wUU* = U - wI  [since UU* = I by unitarity]
    -/
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        U.comp (ContinuousLinearMap.id ℂ H - w • U.adjoint) := by
      ext ψ
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
      have hUU : U.comp U.adjoint = ContinuousLinearMap.id ℂ H :=
        cayleyTransform_comp_adjoint gen hsa
      -- U(ψ - wU*ψ) = Uψ - wU(U*ψ) = Uψ - wψ  [since UU* = I]
      rw [map_sub, map_smul]
      congr 1
      have : U (U.adjoint ψ) = ψ := by
        calc U (U.adjoint ψ) = (U.comp U.adjoint) ψ := rfl
          _ = (ContinuousLinearMap.id ℂ H) ψ := by rw [hUU]
          _ = ψ := rfl
      exact congrArg (HSMul.hSMul w) (id (Eq.symm this))

    -- Conclusion: U - wI = U ∘ (I - wU*) is invertible
    rw [h_factor]
    exact (cayleyTransform_isUnit gen hsa).mul h_inv

  /-
  ─────────────────────────────────────────────────────────────────────────
  CASE 2: |w| > 1 (z in lower half-plane)
  ─────────────────────────────────────────────────────────────────────────

  Factorization: U - wI = -w(I - w⁻¹U)

  Strategy:
  1. Since |w| > 1, we have |w⁻¹| < 1
  2. ‖w⁻¹U‖ ≤ |w⁻¹| · ‖U‖ = |w⁻¹| < 1
  3. By Neumann series, I - w⁻¹U is invertible
  4. Since w ≠ 0, the scalar -w is invertible
  5. Therefore U - wI = -w(I - w⁻¹U) is invertible
  -/
  · -- First, w ≠ 0 (since |w| > 1 > 0)
    have hw_ne : w ≠ 0 := fun h => by
      simp only [h, norm_zero] at hw_gt
      exact not_lt.mpr zero_le_one hw_gt

    -- Bound on ‖w⁻¹U‖
    have h_inv_norm : ‖w⁻¹ • U‖ < 1 := by
      calc ‖w⁻¹ • U‖
          ≤ ‖w⁻¹‖ * ‖U‖ := by exact ContinuousLinearMap.opNorm_smul_le w⁻¹ U
        _ = ‖w‖⁻¹ * 1 := by rw [norm_inv, cayleyTransform_norm_one gen hsa]
        _ = ‖w‖⁻¹ := mul_one _
        _ < 1 := inv_lt_one_of_one_lt₀ hw_gt

    -- Neumann series: I - w⁻¹U is invertible
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w⁻¹ • U) :=
      Resolvent.isUnit_one_sub (w⁻¹ • U) h_inv_norm

    /-
    Factorization: U - wI = -w(I - w⁻¹U)

    Proof: -w(I - w⁻¹U) = -wI + ww⁻¹U = -wI + U = U - wI ✓
    -/
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        -w • (ContinuousLinearMap.id ℂ H - w⁻¹ • U) := by
      ext ψ
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, smul_sub, smul_smul]
      rw [neg_mul, mul_inv_cancel₀ hw_ne]
      simp_all only [ne_eq, Complex.norm_mul, norm_inv, mul_eq_zero, inv_eq_zero,
                     not_or, mul_inv_rev, inv_inv, neg_smul, one_smul, sub_neg_eq_add, w, U]
      obtain ⟨left, right⟩ := hU
      obtain ⟨left_1, right_1⟩ := hw_ne
      exact sub_eq_neg_add ((cayleyTransform gen hsa) ψ) (((z - I) * (z + I)⁻¹) • ψ)

    rw [h_factor]

    -- Show -w • (I - w⁻¹U) is invertible
    have hw_neg_unit : IsUnit (-w) := Ne.isUnit (neg_ne_zero.mpr hw_ne)
    have h_smul_eq : -w • (ContinuousLinearMap.id ℂ H - w⁻¹ • U) =
        (-w • ContinuousLinearMap.id ℂ H) * (ContinuousLinearMap.id ℂ H - w⁻¹ • U) := by
      ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply]
    rw [h_smul_eq]

    -- Product of invertible operators is invertible
    apply IsUnit.mul _ h_inv
    -- IsUnit (-w • id): scalar multiple of identity by invertible scalar
    refine ⟨⟨-w • ContinuousLinearMap.id ℂ H, (-w)⁻¹ • ContinuousLinearMap.id ℂ H, ?_, ?_⟩, rfl⟩
    · ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply,
                smul_smul, mul_inv_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul]
    · ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply,
                smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul]


/-!
## Technical Lemmas for Spectral Correspondence

Before establishing the full spectral correspondence, we need two
technical results from functional analysis:

1. **Dense range criterion:** If the orthogonal complement of Range(T)
   is trivial, then Range(T) is dense.

2. **Normality of U - wI:** When U is unitary, the operator U - wI is
   normal (commutes with its adjoint).

These lemmas are used in the approximate eigenvalue correspondence
and other spectral results.
-/

/--
**Dense range from trivial orthogonal complement.**

### Statement

If T : F →L[ℂ] F is a continuous linear map such that

    (∀ x, ⟪Tx, y⟫ = 0) ⟹ y = 0

then Range(T) is dense in F.

### Proof Idea

The condition says: the only vector orthogonal to all of Range(T) is zero.
In symbols: Range(T)^⊥ = {0}.

In a Hilbert space, we have the double orthogonal complement identity:
    M^⊥⊥ = closure(M)

Therefore:
    Range(T)^⊥ = {0}
    ⟹ Range(T)^⊥⊥ = {0}^⊥ = F
    ⟹ closure(Range(T)) = F
    ⟹ Range(T) is dense

### Use Case

This lemma is used to show that Range(I - U) is dense when -1 is not
an eigenvalue of U. The density of Range(I - U) ensures that the
inverse Cayley transform has dense domain (required for self-adjointness).

### Mathematical Context

This is a standard result in Hilbert space theory. The key ingredients are:
- Orthogonal complement of a subspace
- The identity M^⊥⊥ = closure(M) (double orthogonal = closure)
- {0}^⊥ = H (orthogonal complement of zero is everything)
-/
lemma dense_range_of_orthogonal_trivial {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : F →L[ℂ] F)
    (h : ∀ y, (∀ x, ⟪T x, y⟫_ℂ = 0) → y = 0) :
    Dense (Set.range T) := by
  /-
  Step 1: Show Range(T)^⊥ = {0}.

  The hypothesis h says: if y ⊥ Range(T), then y = 0.
  This is exactly Range(T)^⊥ ⊆ {0}, and the reverse inclusion is trivial.
  -/
  have h_orth : (LinearMap.range T.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply h y
    intro x
    rw [Submodule.mem_orthogonal'] at hy
    simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe,
                   forall_exists_index, forall_apply_eq_imp_iff]
    exact inner_eq_zero_symm.mp (hy x)

  /-
  Step 2: Apply double orthogonal complement.

  {0}^⊥ = ⊤ (everything is orthogonal to zero)
  So Range(T)^⊥⊥ = {0}^⊥ = ⊤
  -/
  have h_double_orth : (LinearMap.range T.toLinearMap)ᗮᗮ = ⊤ := by
    rw [h_orth]
    exact Submodule.bot_orthogonal_eq_top

  /-
  Step 3: Use M^⊥⊥ = closure(M).

  This is a fundamental theorem in Hilbert space theory.
  Therefore closure(Range(T)) = ⊤, i.e., Range(T) is dense.
  -/
  have h_closure_top : (LinearMap.range T.toLinearMap).topologicalClosure = ⊤ := by
    rw [h_double_orth.symm]
    rw [@Submodule.orthogonal_orthogonal_eq_closure]

  -- Convert submodule statements to topological density
  rw [dense_iff_closure_eq]
  have : closure (Set.range T) = ↑(LinearMap.range T.toLinearMap).topologicalClosure := by
    rw [Submodule.topologicalClosure_coe]
    rfl
  rw [this, h_closure_top]
  rfl

/--
**Unitary minus scalar is normal.**

### Statement

If U is unitary (U*U = UU* = I) and w ∈ ℂ, then U - wI is normal:

    (U - wI)*(U - wI) = (U - wI)(U - wI)*

### Why Normality Matters

Normal operators have nice spectral properties:
- The spectral theorem applies (even in infinite dimensions)
- Eigenspaces for distinct eigenvalues are orthogonal
- ‖Tx‖ = ‖T*x‖ for all x
- The spectrum equals the approximate point spectrum

For the Cayley transform, normality of U - wI is used in:
- Showing approximate eigenvalues correspond correctly
- Transferring spectral properties between A and U

### Proof

We compute both sides using (U - wI)* = U* - w̄I:

**LHS:** (U* - w̄I)(U - wI) = U*U - wU* - w̄U + |w|²I = I - wU* - w̄U + |w|²I

**RHS:** (U - wI)(U* - w̄I) = UU* - w̄U - wU* + |w|²I = I - wU* - w̄U + |w|²I

Both simplify to the same expression because U*U = UU* = I.

### General Fact

More generally: if T is normal (T*T = TT*), then T - wI is normal for any w.
This is because normality is preserved under translation by scalars.

For unitary U, normality is automatic since U*U = UU* = I implies U is normal.
-/
lemma unitary_sub_scalar_isNormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U.adjoint * U = 1 ∧ U * U.adjoint = 1) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint := by
  /-
  First, compute the adjoint of U - wI.

  The adjoint is conjugate-linear in the scalar:
    (U - wI)* = U* - w̄I
  -/
  have h_adj : (U - w • 1).adjoint = U.adjoint - (starRingEnd ℂ w) • 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
               inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]

  rw [h_adj]

  /-
  Now expand both sides.

  LHS: (U* - w̄I)(U - wI) = U*U - wU* - w̄U + ww̄·I
                         = I - wU* - w̄U + |w|²I    [using U*U = I]

  RHS: (U - wI)(U* - w̄I) = UU* - w̄U - wU* + ww̄·I
                         = I - wU* - w̄U + |w|²I    [using UU* = I]

  The two expressions are identical!
  -/
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]

  -- Use the unitarity conditions U*U = I and UU* = I
  have h1 : U.adjoint (U x) = x := by
    have := congr_arg (· x) hU.1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  have h2 : U (U.adjoint x) = x := by
    have := congr_arg (· x) hU.2
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  -- Substitute and simplify
  simp only [map_sub, map_smul, h1, h2]
  module  -- The module tactic handles the remaining algebra

/--
**Closed + Dense = Surjective.**

### Statement

If T : E →L[ℂ] F has closed range and dense range, then T is surjective.

### Proof

This is essentially a tautology in topology:
- Dense range means: closure(Range(T)) = F
- Closed range means: closure(Range(T)) = Range(T)
- Therefore: Range(T) = F, i.e., T is surjective

### Why This Lemma?

In many situations, we can prove:
1. Range(T) is closed (often via isometry or Banach space arguments)
2. Range(T) is dense (often via orthogonal complement being trivial)

This lemma combines them to get surjectivity.

### Application to Cayley Transform

For the operator I - U where U is unitary:
- **Closed range:** I - U has closed range because... [depends on context]
- **Dense range:** We prove Range(I - U)^⊥ = {0} when -1 ∉ σₚ(U)

Combining via this lemma: I - U is surjective (when -1 ∉ σₚ(U) and
additional conditions ensuring closed range are met).

### Topological Content

This is an instance of the general principle:
    A dense subset of a space that is also closed must be the whole space.

For subspaces: a dense closed subspace equals the ambient space.
-/
lemma surjective_of_isClosed_range_of_dense {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (hClosed : IsClosed (Set.range T))
    (hDense : Dense (Set.range T)) :
    Function.Surjective T := by
  intro y
  -- closure(Range(T)) = Range(T) by closedness
  have h_closure : closure (Set.range T) = Set.range T := hClosed.closure_eq
  -- closure(Range(T)) = F by density
  have h_univ : closure (Set.range T) = Set.univ := hDense.closure_eq
  -- Therefore Range(T) = F
  rw [h_closure] at h_univ
  -- So y ∈ Range(T)
  have hy : y ∈ Set.range T := by rw [h_univ]; trivial
  exact hy

/-!
## Point Spectrum Correspondence

The deepest result about the Cayley transform: eigenvalues correspond
precisely via the Möbius map.

### The Correspondence

For a self-adjoint operator A and its Cayley transform U:

    μ ∈ σₚ(A)  ⟺  w = (μ - i)/(μ + i) ∈ σₚ(U)

where σₚ denotes the point spectrum (set of eigenvalues).

### Eigenvector Relationship

The eigenvectors are related by:
- If Aψ = μψ, then U((μ + i)ψ) = w · (μ + i)ψ
- If Uφ = wφ, then A(R_{-i}φ) = μ · R_{-i}φ

The factor (μ + i) is exactly (A + iI) applied to ψ.

### Why This Works: Algebraic Derivation

**Forward direction (Aψ = μψ ⟹ Uφ = wφ):**

Set φ = (A + iI)ψ = (μ + i)ψ. Then:
    Uφ = (A - iI)ψ = (μ - i)ψ = [(μ - i)/(μ + i)] · (μ + i)ψ = wφ ✓

**Backward direction (Uφ = wφ ⟹ Aψ = μψ):**

Let ψ = R_{-i}(φ), so (A + iI)ψ = φ. Then:
- Uφ = (A - iI)ψ (by Cayley transform definition)
- Uφ = wφ = w(A + iI)ψ (given)

So (A - iI)ψ = w(A + iI)ψ.

Expanding: Aψ - iψ = wAψ + wiψ

Rearranging: (1 - w)Aψ = (i + wi)ψ = i(1 + w)ψ

Solving: Aψ = [i(1 + w)/(1 - w)]ψ

A calculation shows i(1 + w)/(1 - w) = μ when w = (μ - i)/(μ + i). ✓

### Key Subtlety: w ≠ 1

The backward direction requires dividing by (1 - w). This is valid because
w = 1 would require (μ - i)/(μ + i) = 1, i.e., μ - i = μ + i, i.e., -i = i.
Contradiction. So w ≠ 1 for any real μ.

(Note: w = 1 corresponds to μ = ∞, which is not in the real spectrum of A.)

### Connection to the -1 Eigenvalue Theorem

The special case μ = 0 gives w = (0 - i)/(0 + i) = -1.

So: 0 ∈ σₚ(A) ⟺ -1 ∈ σₚ(U)

This is exactly the `cayley_neg_one_eigenvalue_iff` theorem we proved earlier!
The current theorem generalizes it to all real eigenvalues.

### Physical Interpretation

In quantum mechanics:
- Eigenvalues of A (the Hamiltonian) are energy levels
- Eigenvalues of U are phase factors e^{iθ}

The Möbius map w = (μ - i)/(μ + i) parametrizes the unit circle by ℝ:
- μ = 0 ↦ w = -1 (phase π)
- μ → +∞ ↦ w → +1 (phase 0)
- μ → -∞ ↦ w → +1 (phase 0, from the other side)
- |w| = 1 always for real μ

The energy spectrum of A maps bijectively to the phase spectrum of U.
-/

/--
**Point spectrum correspondence:** Eigenvalues of A and U correspond via Möbius.

### Statement

For real μ:

    (∃ ψ ≠ 0 in D(A), Aψ = μψ)  ⟺  (∃ φ ≠ 0 in H, Uφ = wφ)

where w = (μ - i)/(μ + i).

### Significance

This is the **fundamental spectral correspondence** for the Cayley transform.
It shows that the point spectra of A and U are in bijection via the Möbius map.

Combined with similar results for the continuous and residual spectrum, this
establishes that the Cayley transform induces a complete spectral bijection:

    σ(A) ⊆ ℝ  ←―――→  σ(U) ⊆ S¹ \ {-1}  (when ker(A) = {0})
              Möbius

### Proof Structure

**Forward (⟹):** Given eigenvector ψ of A with eigenvalue μ:
1. Construct φ = (A + iI)ψ = (μ + i)ψ
2. Show φ ≠ 0 (since μ + i ≠ 0 and ψ ≠ 0)
3. Compute Uφ = (A - iI)ψ = (μ - i)ψ = wφ

**Backward (⟸):** Given eigenvector φ of U with eigenvalue w:
1. Set ψ = R_{-i}(φ), so (A + iI)ψ = φ
2. Show ψ ≠ 0 (since φ ≠ 0)
3. From Uφ = wφ and Uφ = (A - iI)ψ, derive (A - iI)ψ = w(A + iI)ψ
4. Algebraically solve for Aψ = μψ (requires w ≠ 1)
-/
theorem cayley_eigenvalue_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) (μ : ℝ) :
    (∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ) := by
  set U := cayleyTransform gen hsa
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def

  /-
  Preliminary: μ + i ≠ 0 for real μ.

  This is needed to ensure w is well-defined and to show φ ≠ 0 in the
  forward direction.
  -/
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := by
    intro h
    have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
    simp at this

  constructor

  /-
  ═══════════════════════════════════════════════════════════════════════════
  FORWARD DIRECTION: Aψ = μψ implies Uφ = wφ
  ═══════════════════════════════════════════════════════════════════════════

  Given: ψ ≠ 0 in D(A) with Aψ = μψ
  Construct: φ = (A + iI)ψ = (μ + i)ψ
  Show: Uφ = wφ
  -/
  · rintro ⟨ψ, hψ, hψ_ne, h_eig⟩

    /-
    Step 1: Construct the eigenvector φ = (A + iI)ψ.

    Since Aψ = μψ, we have:
      φ = (A + iI)ψ = Aψ + iψ = μψ + iψ = (μ + i)ψ
    -/
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ

    have hφ_eq : φ = (↑μ + I) • ψ := by
      simp only [φ, h_eig, add_smul]
      exact rfl

    /-
    Step 2: Show φ ≠ 0.

    We have φ = (μ + i)ψ. Since μ + i ≠ 0 (imaginary part is 1) and ψ ≠ 0,
    the product (μ + i)ψ ≠ 0.
    -/
    have hφ_ne : φ ≠ 0 := by
      rw [hφ_eq]
      intro h
      rw [smul_eq_zero] at h
      cases h with
      | inl h => exact hμ_ne h
      | inr h => exact hψ_ne h

    use φ, hφ_ne

    /-
    Step 3: Verify Uφ = wφ.

    Compute:
      Uφ = (A - iI)ψ        [by Cayley transform]
         = Aψ - iψ
         = μψ - iψ          [since Aψ = μψ]
         = (μ - i)ψ
         = [(μ - i)/(μ + i)] · (μ + i)ψ    [multiply and divide by (μ + i)]
         = w · φ             [since φ = (μ + i)ψ]
    -/
    have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
      rw [h_res]
      module

    calc U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := h_Uφ
      _ = (↑μ - I) • ψ := by rw [h_eig]; exact Eq.symm (sub_smul (↑μ) I ψ)
      _ = w • (↑μ + I) • ψ := by
        -- Key step: (μ - i) = w · (μ + i), i.e., w = (μ - i)/(μ + i)
        simp only [hw_def, smul_smul]
        congr 1
        exact Eq.symm (inv_mul_cancel_right₀ hμ_ne (↑μ - I))
      _ = w • φ := by rw [← hφ_eq]

  /-
  ═══════════════════════════════════════════════════════════════════════════
  BACKWARD DIRECTION: Uφ = wφ implies Aψ = μψ
  ═══════════════════════════════════════════════════════════════════════════

  Given: φ ≠ 0 with Uφ = wφ
  Construct: ψ = R_{-i}(φ), so (A + iI)ψ = φ
  Show: Aψ = μψ

  This direction is more involved because we must algebraically extract
  the eigenvalue equation from the Cayley transform relation.
  -/
  · rintro ⟨φ, hφ_ne, h_eig⟩

    /-
    Step 1: Extract ψ from φ via the resolvent.

    The resolvent R_{-i} = (A + iI)⁻¹ gives us ψ = R_{-i}(φ) satisfying
    (A + iI)ψ = φ.
    -/
    set ψ := Resolvent.resolvent_at_neg_i gen hsa φ with hψ_def
    have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
    have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ

    use ψ, hψ_mem

    /-
    Step 2: Show ψ ≠ 0.

    If ψ = 0, then φ = (A + iI)ψ = (A + iI)(0) = 0.
    But φ ≠ 0 by hypothesis. Contradiction.
    -/
    have hψ_ne : ψ ≠ 0 := by
      intro h
      have hφ_zero : φ = 0 := by
        have h0_mem : (0 : H) ∈ gen.domain := Submodule.zero_mem gen.domain
        have : gen.op ⟨0, h0_mem⟩ + I • (0 : H) = 0 := by
          rw [smul_zero, add_zero]
          exact map_zero gen.op
        rw [← hφ_eq]
        convert this using 2
        · simp_all only [ne_eq, smul_zero, add_zero, w, U, ψ]
        · exact congrArg (HSMul.hSMul I) h
      exact hφ_ne hφ_zero

    constructor
    · exact hψ_ne

    /-
    Step 3: Derive Aψ = μψ from (A - iI)ψ = w(A + iI)ψ.

    We have:
    - Uφ = (A - iI)ψ       [by Cayley transform, since (A + iI)ψ = φ]
    - Uφ = wφ = w(A + iI)ψ [given]

    Therefore: (A - iI)ψ = w(A + iI)ψ

    We now solve this algebraically for Aψ.
    -/
    · -- First express Uφ in terms of ψ
      have h_Uφ : U φ = gen.op ⟨ψ, hψ_mem⟩ - I • ψ := by
        rw [← hφ_eq]
        simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                   ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
        have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) = ψ :=
          Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ_mem
        rw [h_res]
        module

      /-
      The key equation: (A - iI)ψ = w(A + iI)ψ

      Expanding: Aψ - iψ = wAψ + wiψ
      -/
      have h_key : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = w • (gen.op ⟨ψ, hψ_mem⟩ + I • ψ) := by
        rw [← h_Uφ, h_eig, hφ_eq]

      /-
      Step 4: Show w ≠ 1.

      If w = 1, then (μ - i)/(μ + i) = 1, so μ - i = μ + i, so -i = i.
      Contradiction (imaginary parts -1 ≠ 1).

      This is essential: we need to divide by (1 - w) to solve for Aψ.
      -/
      have hw_ne_one : w ≠ 1 := by
        simp only [hw_def]
        intro h_eq
        have : (↑μ - I) * (↑μ + I)⁻¹ = 1 := h_eq
        field_simp [hμ_ne] at this
        have h_im : (↑μ - I : ℂ).im = (↑μ + I : ℂ).im := by rw [this]
        simp at h_im
        -- -1 ≠ 1, contradiction
        exact absurd h_im (by norm_num : (-1 : ℝ) ≠ 1)

      have h_one_sub_ne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne_one)

      /-
      Step 5: Algebraically solve for Aψ.

      From (A - iI)ψ = w(A + iI)ψ:
        Aψ - iψ = wAψ + wiψ
        Aψ - wAψ = iψ + wiψ
        (1 - w)Aψ = (i + wi)ψ = i(1 + w)ψ
        Aψ = [i(1 + w)/(1 - w)]ψ

      We must show i(1 + w)/(1 - w) = μ.
      -/
      have h_expand : gen.op ⟨ψ, hψ_mem⟩ - I • ψ = w • gen.op ⟨ψ, hψ_mem⟩ + w • I • ψ := by
        rw [h_key, smul_add]

      -- Collect terms: (1 - w)Aψ = (i + wi)ψ
      have h_collect : (1 - w) • gen.op ⟨ψ, hψ_mem⟩ = (I + w * I) • ψ := by
        calc (1 - w) • gen.op ⟨ψ, hψ_mem⟩
            = gen.op ⟨ψ, hψ_mem⟩ - w • gen.op ⟨ψ, hψ_mem⟩ := by rw [sub_smul, one_smul]
          _ = I • ψ + w • I • ψ := by
              -- Rearrange: Aψ - wAψ = iψ + wiψ
              have h1 : gen.op ⟨ψ, hψ_mem⟩ - w • gen.op ⟨ψ, hψ_mem⟩ =
                        (gen.op ⟨ψ, hψ_mem⟩ - I • ψ) - (w • gen.op ⟨ψ, hψ_mem⟩ - I • ψ) := by module
              rw [h1, h_expand]
              module
          _ = (I + w * I) • ψ := by rw [hw_def]; module

      /-
      Final calculation: Aψ = (1-w)⁻¹(i + wi)ψ = μψ

      We verify: (1-w)⁻¹(i + wi) = (1-w)⁻¹ · i(1+w) = i(1+w)/(1-w)

      With w = (μ-i)/(μ+i), a calculation shows i(1+w)/(1-w) = μ.
      -/
      calc gen.op ⟨ψ, hψ_mem⟩
          = (1 - w)⁻¹ • (1 - w) • gen.op ⟨ψ, hψ_mem⟩ := by
              rw [smul_smul]
              simp_all only [ne_eq, not_false_eq_true, inv_mul_cancel₀, one_smul, w, U, ψ]
        _ = (1 - w)⁻¹ • (I + w * I) • ψ := by rw [h_collect]
        _ = ((1 - w)⁻¹ * (I + w * I)) • ψ := by rw [smul_smul]
        _ = ↑μ • ψ := by
            -- The key algebraic verification: i(1+w)/(1-w) = μ when w = (μ-i)/(μ+i)
            congr 1
            simp only [hw_def]
            field_simp [hμ_ne, h_one_sub_ne]
            simp only [add_add_sub_cancel, add_sub_sub_cancel, RingHom.toMonoidHom_eq_coe,
              OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, coe_algebraMap,
              ZeroHom.coe_mk]
            ring
      exact rfl



/-!
## Möbius Map Algebra

The Möbius transformation w(μ) = (μ - i)/(μ + i) is the bridge between
the real spectrum of A and the circular spectrum of U. This section
collects the algebraic identities needed for spectral correspondence.

### The Möbius Map

For real μ, define:

    w(μ) = (μ - i)/(μ + i)

Key properties:
- |w(μ)| = 1 (lies on unit circle)
- w(0) = -1
- w(±∞) = 1
- w is a bijection ℝ → S¹ \ {1}

### Why These Identities?

The spectral correspondence proofs repeatedly need to manipulate
expressions involving w. Rather than re-derive these each time,
we collect them here:

1. **1 - w = 2i/(μ + i):** Used when solving (A - μI)ψ from (U - wI)φ
2. **1 + w = 2μ/(μ + i):** Appears in coefficient matching
3. **i(1 + w) = (1 - w)μ:** The fundamental intertwining identity
4. **1 - w ≠ 0:** Ensures we can divide by (1 - w)

### The Intertwining Identity

The most important result is `cayley_shift_identity`:

    (U - wI)(A + iI)ψ = (1 - w)(A - μI)ψ

This shows how the shifted Cayley transform (U - wI) relates to the
shifted generator (A - μI). It is the key to:
- Approximate eigenvalue correspondence
- Spectral mapping theorem
- Functional calculus transfer
-/

variable (μ : ℝ)

/--
**μ + i ≠ 0 for real μ.**

### Statement

For any real number μ, the complex number μ + i is nonzero.

### Proof

The imaginary part of μ + i is 1 ≠ 0, so μ + i ≠ 0.

### Use Case

This lemma is needed whenever we divide by (μ + i), which occurs
throughout the Möbius map calculations.
-/
lemma real_add_I_ne_zero : (↑μ : ℂ) + I ≠ 0 := by
  intro h
  have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
  simp at this

/--
**The Möbius map has unit modulus:** |w(μ)| = 1 for real μ.

### Statement

For real μ, the Möbius image w = (μ - i)/(μ + i) satisfies |w| = 1.

### Proof

We have |μ - i| = |μ + i| because μ - i and μ + i are complex conjugates
(both have real part μ and imaginary parts ±1).

Therefore |w| = |μ - i|/|μ + i| = 1.

### Geometric Interpretation

The Möbius map sends the real line to the unit circle. Every point on ℝ
maps to a point on S¹, and every point on S¹ \ {1} has a unique real preimage.

### Consequence

Since |w| = 1, the spectrum of U (which lies on S¹ for unitary U) is
exactly the Möbius image of the spectrum of A (which lies on ℝ for
self-adjoint A).
-/
lemma mobius_norm_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  simp only [norm_mul, norm_inv]
  -- Key: |μ - i| = |μ + i| because they are conjugates
  have h1 : ‖(↑μ : ℂ) - I‖ = ‖(↑μ : ℂ) + I‖ := by
    have h : starRingEnd ℂ ((↑μ : ℂ) + I) = (↑μ : ℂ) - I := by simp [Complex.ext_iff]
    rw [← h, RCLike.norm_conj]
  have h2 : ‖(↑μ : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr hμ_ne
  field_simp [h2, h1]
  exact h1

/--
**Möbius identity:** 1 - w = 2i/(μ + i).

### Statement

For w = (μ - i)/(μ + i):

    1 - w = 2i/(μ + i)

### Derivation

    1 - w = 1 - (μ - i)/(μ + i)
          = [(μ + i) - (μ - i)]/(μ + i)
          = 2i/(μ + i)

### Use Case

This identity appears when solving for (A - μI)ψ from the Cayley relation.
The factor (1 - w) multiplies the "A" term, and this formula shows it's
never zero (since 2i ≠ 0 and μ + i ≠ 0).
-/
lemma one_sub_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/--
**Möbius identity:** 1 + w = 2μ/(μ + i).

### Statement

For w = (μ - i)/(μ + i):

    1 + w = 2μ/(μ + i)

### Derivation

    1 + w = 1 + (μ - i)/(μ + i)
          = [(μ + i) + (μ - i)]/(μ + i)
          = 2μ/(μ + i)

### Use Case

This identity appears in the coefficient i(1 + w) which relates to
the "iψ" terms in the Cayley transform calculations.
-/
lemma one_add_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/--
**Key coefficient identity:** i(1 + w) = (1 - w)μ.

### Statement

For w = (μ - i)/(μ + i):

    i(1 + w) = (1 - w)μ

### Derivation

Using the previous identities:
- 1 + w = 2μ/(μ + i)
- 1 - w = 2i/(μ + i)

LHS = i · 2μ/(μ + i) = 2iμ/(μ + i)
RHS = 2i/(μ + i) · μ = 2iμ/(μ + i) ✓

### Significance

This is the **fundamental intertwining identity**. It shows that the
coefficients appearing in the Cayley transform relation are not independent:
knowing one determines the other via this relation.

Specifically, when we expand (U - wI)(A + iI)ψ, we get terms involving
(1 - w)Aψ and i(1 + w)ψ. This identity shows they collapse to (1 - w)(A - μI)ψ.
-/
lemma mobius_coeff_identity (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    let w := (↑μ - I) * (↑μ + I)⁻¹
    I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ := by
  simp only
  rw [one_sub_mobius μ hμ_ne, one_add_mobius μ hμ_ne]
  field_simp [hμ_ne]

/--
**1 - w ≠ 0 for real μ.**

### Statement

For w = (μ - i)/(μ + i), we have 1 - w ≠ 0.

### Proof

By `one_sub_mobius`: 1 - w = 2i/(μ + i).
Since 2i ≠ 0 and μ + i ≠ 0, the quotient is nonzero.

### Significance

This ensures we can always divide by (1 - w) in spectral calculations.
The condition 1 - w = 0 would correspond to w = 1, which would require
μ = ∞ (not a real number).

Geometrically: w = 1 is the point on S¹ that is NOT in the range of
the Möbius map restricted to ℝ.
-/
lemma one_sub_mobius_ne_zero (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := by
  rw [one_sub_mobius μ hμ_ne]
  simp [hμ_ne]

/--
**‖1 - w‖ > 0 for real μ.**

### Statement

For w = (μ - i)/(μ + i), we have ‖1 - w‖ > 0.

### Proof

Immediate from `one_sub_mobius_ne_zero` and the fact that norm is
positive for nonzero elements.

### Use Case

This is the "norm version" of `one_sub_mobius_ne_zero`, useful when
working with operator norm estimates.
-/
lemma one_sub_mobius_norm_pos (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0 :=
  norm_pos_iff.mpr (one_sub_mobius_ne_zero μ hμ_ne)

/-!
### Cayley Transform Identities

The following lemmas connect the Möbius algebra to the Cayley transform.
-/

/--
**Cayley transform on resolvent output:** U((A + iI)ψ) = (A - iI)ψ.

### Statement

For ψ ∈ D(A), the Cayley transform applied to (A + iI)ψ gives (A - iI)ψ.

### Proof

This is a direct calculation using the definition of the Cayley transform
and the resolvent inverse property.

### Significance

This is the **computational form** of the Cayley transform. It says:
- Input: φ = (A + iI)ψ (an element in the range of A + iI)
- Output: Uφ = (A - iI)ψ (the corresponding element with -i instead of +i)

The Cayley transform "flips the sign of i" in a controlled way.
-/
lemma cayleyTransform_apply_resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    cayleyTransform gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = gen.op ⟨ψ, hψ⟩ - I • ψ := by
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  have h_res := Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
  rw [h_res]
  module

/--
**The intertwining identity:** (U - wI)(A + iI)ψ = (1 - w)(A - μI)ψ.

### Statement

For ψ ∈ D(A), μ ∈ ℝ, and w = (μ - i)/(μ + i):

    (U - wI)((A + iI)ψ) = (1 - w)(A - μI)ψ

### Significance

This is the **master identity** for spectral correspondence. It shows
how the shifted Cayley transform (U - wI) intertwines with the shifted
generator (A - μI).

**Consequences:**

1. **Eigenvalue correspondence:** If (A - μI)ψ = 0, then (U - wI)φ = 0
   where φ = (A + iI)ψ. So eigenvalues of A at μ correspond to eigenvalues
   of U at w.

2. **Approximate eigenvalues:** If ‖(A - μI)ψ‖ is small, then ‖(U - wI)φ‖
   is small (scaled by |1 - w|). So approximate eigenvalues correspond.

3. **Resolvent correspondence:** (U - wI)⁻¹ and (A - μI)⁻¹ are related
   via this identity (when the inverses exist).

### Derivation

Let φ = (A + iI)ψ. Then Uφ = (A - iI)ψ by `cayleyTransform_apply_resolvent`.

    (U - wI)φ = Uφ - wφ
              = (A - iI)ψ - w(A + iI)ψ
              = Aψ - iψ - wAψ - wiψ
              = (1 - w)Aψ - i(1 + w)ψ
              = (1 - w)Aψ - (1 - w)μψ     [by mobius_coeff_identity]
              = (1 - w)(A - μI)ψ ✓
-/
lemma cayley_shift_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (U - w • ContinuousLinearMap.id ℂ H) φ = ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by
  intro U w φ

  have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := cayleyTransform_apply_resolvent gen hsa ψ hψ
  have h_coeff := mobius_coeff_identity μ hμ_ne

  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply, φ, h_Uφ]

  /-
  Expand both sides:

  LHS = (A - iI)ψ - w(A + iI)ψ
      = Aψ - iψ - wAψ - wiψ
      = (1 - w)Aψ - i(1 + w)ψ

  RHS = (1 - w)(Aψ - μψ)
      = (1 - w)Aψ - (1 - w)μψ

  These are equal by h_coeff: i(1 + w) = (1 - w)μ
  -/
  calc gen.op ⟨ψ, hψ⟩ - I • ψ - w • (gen.op ⟨ψ, hψ⟩ + I • ψ)
      = (1 - w) • gen.op ⟨ψ, hψ⟩ - (I * (1 + w)) • ψ := by rw [smul_add]; module
    _ = (1 - w) • gen.op ⟨ψ, hψ⟩ - ((1 - w) * ↑μ) • ψ := by rw [h_coeff]
    _ = (1 - w) • gen.op ⟨ψ, hψ⟩ - (1 - w) • (↑μ • ψ) := by rw [@mul_smul]; rfl
    _ = (1 - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by rw [smul_sub]
  simp only

/-!
## Bounded Below Correspondence

This section establishes how "bounded below" properties transfer between
the shifted generator (A - μI) and the shifted Cayley transform (U - wI).

### What "Bounded Below" Means

An operator T is **bounded below** if there exists C > 0 such that
‖Tx‖ ≥ C‖x‖ for all x in the domain. This is equivalent to:
- T is injective
- T has closed range
- T⁻¹ (on its range) is bounded

### The Transfer

The intertwining identity (U - wI)(A + iI)ψ = (1 - w)(A - μI)ψ allows us
to transfer bounded-below properties:

**Forward:** A - μI bounded below ⟹ U - wI injective
**Backward:** U - wI bounded below ⟹ A - μI bounded below

The backward direction is more subtle because it requires relating
‖φ‖ to ‖ψ‖ where φ = (A + iI)ψ. This is where the identity
‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² (from self-adjointness) is crucial.

### Why This Matters

These results connect the resolvent sets:
- μ ∈ ρ(A) ⟺ A - μI is invertible ⟺ A - μI bounded below + dense range
- w ∈ ρ(U) ⟺ U - wI is invertible ⟺ U - wI bounded below (automatic for normal)

The bounded-below correspondence is the "injectivity half" of the
resolvent correspondence.
-/

/--
**Forward injectivity transfer:** A - μI bounded below ⟹ U - wI injective.

### Statement

If there exists C > 0 such that ‖(A - μI)ψ‖ ≥ C‖ψ‖ for all ψ ∈ D(A),
then U - wI is injective (where w = (μ - i)/(μ + i)).

### Proof Strategy

Suppose (U - wI)φ₁ = (U - wI)φ₂. We show φ₁ = φ₂.

Set φ = φ₁ - φ₂. Then (U - wI)φ = 0, i.e., Uφ = wφ.

By the eigenvalue correspondence (`cayley_eigenvalue_correspondence`):
- Uφ = wφ with φ ≠ 0 implies there exists ψ ≠ 0 with Aψ = μψ

But Aψ = μψ means (A - μI)ψ = 0, so ‖(A - μI)ψ‖ = 0.
By bounded below: 0 = ‖(A - μI)ψ‖ ≥ C‖ψ‖, so ‖ψ‖ = 0, hence ψ = 0.

Contradiction! Therefore φ = 0, i.e., φ₁ = φ₂.

### Significance

This shows that if μ is not an eigenvalue of A (which is implied by
A - μI bounded below), then w is not an eigenvalue of U.

More strongly: bounded below is preserved in the forward direction.
-/
lemma cayley_shift_injective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (_ /-hμ_ne-/ : (↑μ : ℂ) + I ≠ 0)
    (hC : ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    Function.Injective (U - w • ContinuousLinearMap.id ℂ H) := by
  intro U w φ₁ φ₂ h_eq
  rw [← sub_eq_zero]
  set φ := φ₁ - φ₂

  -- (U - wI)φ = 0, i.e., Uφ = wφ
  have h_zero : (U - w • ContinuousLinearMap.id ℂ H) φ = 0 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, φ, map_sub]
    have := h_eq
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply] at this
    exact sub_eq_zero_of_eq h_eq

  -- Prove by contradiction: assume φ ≠ 0
  by_contra hφ_ne

  -- From h_zero: Uφ = wφ (φ is a w-eigenvector of U)
  have h_eig : U φ = w • φ := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, sub_eq_zero] at h_zero
    exact h_zero

  /-
  By eigenvalue correspondence: Uφ = wφ with φ ≠ 0 implies
  there exists ψ ≠ 0 in D(A) with Aψ = μψ.
  -/
  have h_exists : ∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ := by
    rw [cayley_eigenvalue_correspondence gen hsa μ]
    exact ⟨φ, hφ_ne, h_eig⟩

  obtain ⟨ψ, hψ_mem, hψ_ne, h_Aψ⟩ := h_exists
  obtain ⟨C, hC_pos, hC_bound⟩ := hC

  -- From bounded below: ‖(A - μI)ψ‖ ≥ C‖ψ‖
  have h_bound := hC_bound ψ hψ_mem

  -- But Aψ = μψ, so (A - μI)ψ = 0, hence ‖(A - μI)ψ‖ = 0
  rw [h_Aψ, sub_self, norm_zero] at h_bound

  -- 0 ≥ C‖ψ‖ with C > 0 implies ‖ψ‖ ≤ 0, hence ψ = 0
  have : ‖ψ‖ = 0 := by nlinarith [norm_nonneg ψ]
  exact hψ_ne (norm_eq_zero.mp this)

/--
**The fundamental norm identity for self-adjoint operators.**

### Statement

For ψ ∈ D(A) where A is self-adjoint:

    ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

### Proof

Expand ‖Aψ + iψ‖² = ⟨Aψ + iψ, Aψ + iψ⟩:

    = ‖Aψ‖² + ‖iψ‖² + 2·Re⟨Aψ, iψ⟩
    = ‖Aψ‖² + ‖ψ‖² + 2·Re(i⟨Aψ, ψ⟩)

The cross-term vanishes: Re(i⟨Aψ, ψ⟩) = 0 because ⟨Aψ, ψ⟩ is real
(by self-adjointness), and i times a real number is purely imaginary.

### Significance

This identity is used repeatedly:
1. In the isometry proof: ‖Uφ‖ = ‖φ‖
2. In bounded-below transfer: ‖φ‖ ≥ ‖ψ‖ where φ = (A + iI)ψ
3. In resolvent estimates

### Corollary

Since ‖Aψ‖² ≥ 0, we have ‖(A + iI)ψ‖² ≥ ‖ψ‖², hence **‖(A + iI)ψ‖ ≥ ‖ψ‖**.

This shows (A + iI) is bounded below with constant 1.
-/
lemma self_adjoint_norm_sq_add {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ /-hsa-/ : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := by
  have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp

  /-
  Key: Re⟨Aψ, iψ⟩ = 0 because ⟨Aψ, ψ⟩ is real for self-adjoint A.

  Proof that ⟨Aψ, ψ⟩ ∈ ℝ:
  By symmetry: ⟨Aψ, ψ⟩ = ⟨ψ, Aψ⟩ = conj⟨Aψ, ψ⟩
  A complex number equal to its conjugate is real.
  -/
  have cross_zero : (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re = 0 := by
    rw [inner_smul_right]
    have h_real : (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
      have h_sym := gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
      have h_conj : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
        calc ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
            = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := h_sym
          _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
      have := Complex.ext_iff.mp h_conj
      simp only [Complex.conj_im] at this
      linarith [this.2]
    -- i · (real number) has zero real part
    have h1 : I * ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = I * (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).re := by
      conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ, h_real]
      simp
    rw [h1, mul_comm]; simp

  -- ‖x + y‖² = ‖x‖² + ‖y‖² + 2Re⟨x,y⟩, and cross term is 0
  have h_expand : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 =
      ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖I • ψ‖^2 + 2 * (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
    have h1 : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 =
              (⟪gen.op ⟨ψ, hψ⟩ + I • ψ, gen.op ⟨ψ, hψ⟩ + I • ψ⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h2 : ‖gen.op ⟨ψ, hψ⟩‖^2 = (⟪gen.op ⟨ψ, hψ⟩, gen.op ⟨ψ, hψ⟩⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h3 : ‖I • ψ‖^2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; norm_cast
    have h_cross : (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ).re =
                   2 * (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
      have : (⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ).re := by
        have h : ⟪I • ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, I • ψ⟫_ℂ := by
          exact Eq.symm (conj_inner_symm (I • ψ) (gen.op ⟨ψ, hψ⟩))
        simp only [h, Complex.conj_re]
      linarith
    rw [h1, inner_add_left, inner_add_right, inner_add_right]
    simp only [Complex.add_re, h2, h3, ← h_cross]
    ring

  rw [h_expand, norm_I_smul, cross_zero]
  ring

/--
**Backward spectral correspondence:** U - wI invertible ⟹ A - μI bounded below.

### Statement

If U - wI is invertible (IsUnit), then A - μI is bounded below:
there exists C > 0 such that ‖(A - μI)ψ‖ ≥ C‖ψ‖ for all ψ ∈ D(A).

### Proof Strategy

Let T = U - wI and let T_inv be its inverse.

**Step 1:** T invertible implies T bounded below with constant ‖T_inv‖⁻¹.
(Standard result: ‖Tφ‖ ≥ ‖T_inv‖⁻¹ ‖φ‖)

**Step 2:** Use the intertwining identity:
    ‖Tφ‖ = ‖(1-w)(A-μI)ψ‖ = |1-w| · ‖(A-μI)ψ‖
where φ = (A + iI)ψ.

**Step 3:** Use ‖φ‖ ≥ ‖ψ‖ (from self_adjoint_norm_sq_add).

**Step 4:** Chain the inequalities:
    |1-w| · ‖(A-μI)ψ‖ = ‖Tφ‖ ≥ ‖T_inv‖⁻¹ ‖φ‖ ≥ ‖T_inv‖⁻¹ ‖ψ‖

Solving: ‖(A-μI)ψ‖ ≥ (‖T_inv‖⁻¹ / |1-w|) ‖ψ‖

### The Constant

C = ‖T_inv‖⁻¹ / |1 - w| = ‖(U - wI)⁻¹‖⁻¹ / |1 - w|

### Significance

This completes the "bounded below" direction of the spectral correspondence:
- U - wI invertible ⟹ A - μI bounded below
- Combined with range arguments: w ∈ ρ(U) ⟹ μ ∈ ρ(A)
-/
lemma cayley_spectrum_backward {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (h_unit : IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)) :
    ∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖ := by

  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def

  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ

  -- Step 1: Extract the inverse from IsUnit
  obtain ⟨⟨T, T_inv, hT_left, hT_right⟩, hT_eq⟩ := h_unit
  simp only at hT_eq

  -- T_inv ≠ 0 (otherwise T * T_inv = 0 ≠ 1)
  have hT_inv_ne : T_inv ≠ 0 := by
    intro h
    have : (1 : H →L[ℂ] H) = 0 := by
      calc (1 : H →L[ℂ] H) = T_inv * T := hT_right.symm
        _ = 0 * T := by rw [h]
        _ = 0 := zero_mul T
    exact one_ne_zero this

  have hT_inv_norm_pos : ‖T_inv‖ > 0 := norm_pos_iff.mpr hT_inv_ne

  -- Step 2: T has bounded below property
  have h_T_bounded_below : ∀ φ, ‖T φ‖ ≥ ‖T_inv‖⁻¹ * ‖φ‖ := by
    intro φ
    have h := ContinuousLinearMap.le_opNorm T_inv (T φ)
    have h' : T_inv (T φ) = φ := by
      have := congr_arg (· φ) hT_right
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
      exact this
    rw [h'] at h
    exact (inv_mul_le_iff₀ hT_inv_norm_pos).mpr h

  -- |1 - w| > 0
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne

  -- The constant C = ‖T_inv‖⁻¹ / |1 - w|
  use ‖T_inv‖⁻¹ / ‖(1 : ℂ) - w‖
  constructor
  · positivity

  intro ψ hψ

  -- φ = (A + iI)ψ
  let φ := gen.op ⟨ψ, hψ⟩ + I • ψ

  -- Key identity: Tφ = (1-w)(A - μI)ψ
  have h_key : T φ = ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ) := by
    rw [hT_eq]
    exact cayley_shift_identity gen hsa μ hμ_ne ψ hψ

  -- Step 3: ‖φ‖ ≥ ‖ψ‖ from ‖(A+iI)ψ‖² = ‖Aψ‖² + ‖ψ‖² ≥ ‖ψ‖²
  have h_phi_bound : ‖φ‖ ≥ ‖ψ‖ := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ
    have h_ge : ‖φ‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ 0 + ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ⟩‖]
        _ = ‖ψ‖^2 := by ring
    nlinarith [norm_nonneg φ, norm_nonneg ψ, sq_nonneg (‖φ‖ - ‖ψ‖)]

  -- Step 4: Chain the bounds
  have h_Tφ_eq : ‖T φ‖ = ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖ := by
    rw [h_key, norm_smul]

  have h_chain : ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖ ≥ ‖T_inv‖⁻¹ * ‖ψ‖ := by
    calc ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
        = ‖T φ‖ := h_Tφ_eq.symm
      _ ≥ ‖T_inv‖⁻¹ * ‖φ‖ := h_T_bounded_below φ
      _ ≥ ‖T_inv‖⁻¹ * ‖ψ‖ := by apply mul_le_mul_of_nonneg_left h_phi_bound; positivity

  -- Divide by |1 - w| to get the final bound
  calc ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
      = ‖(1 : ℂ) - w‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖) := by
          field_simp [ne_of_gt h_one_sub_w_norm_pos]
    _ ≥ ‖(1 : ℂ) - w‖⁻¹ * (‖T_inv‖⁻¹ * ‖ψ‖) := by
          apply mul_le_mul_of_nonneg_left h_chain; positivity
    _ = ‖T_inv‖⁻¹ / ‖(1 : ℂ) - w‖ * ‖ψ‖ := by ring

/--
**Backward bounded-below transfer (direct version).**

### Statement

If U - wI is bounded below with constant c > 0:
    ‖(U - wI)φ‖ ≥ c‖φ‖ for all φ

Then A - μI is bounded below with constant c / |1 - w|.

### Relation to cayley_spectrum_backward

This is a more direct version that takes the bounded-below hypothesis
explicitly, rather than deriving it from IsUnit.

### Use Case

When you have an explicit bound on (U - wI) (e.g., from distance to
spectrum), this lemma transfers it to A - μI without going through
invertibility.
-/
lemma cayley_shift_bounded_below_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0)
    (c : ℝ) (hc_pos : c > 0)
    (hc_bound : ∀ φ, ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ ≥ c * ‖φ‖) :
    ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖ := by
  set U := cayleyTransform gen hsa
  set w := (↑μ - I) * (↑μ + I)⁻¹

  have h_one_sub_w_norm_pos := one_sub_mobius_norm_pos μ hμ_ne

  -- The constant: C = c / |1 - w|
  use c / ‖(1 : ℂ) - w‖
  constructor
  · positivity
  · intro ψ hψ
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ

    -- Apply the key identity
    have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ

    -- Get the bound on (U - wI)φ
    have h_bound : ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ c * ‖φ‖ := hc_bound φ

    -- ‖φ‖ ≥ ‖ψ‖
    have h_phi_bound : ‖φ‖ ≥ ‖ψ‖ := by
      have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ
      have h1 : ‖φ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 := h_sq
      have h2 : ‖φ‖^2 ≥ ‖ψ‖^2 := by rw [h1]; linarith [sq_nonneg ‖gen.op ⟨ψ, hψ⟩‖]
      nlinarith [norm_nonneg φ, norm_nonneg ψ, sq_nonneg ‖φ‖, sq_nonneg ‖ψ‖]

    -- Chain: |1-w| · ‖(A-μI)ψ‖ = ‖(U-wI)φ‖ ≥ c · ‖φ‖ ≥ c · ‖ψ‖
    have h_chain : ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖ ≥ c * ‖ψ‖ := by
      have h_eq : ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ =
                  ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖ := by
        simp only [U, w, φ] at h_key ⊢
        rw [h_key, norm_smul]
      calc ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖
          = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ := h_eq.symm
        _ ≥ c * ‖φ‖ := h_bound
        _ ≥ c * ‖ψ‖ := mul_le_mul_of_nonneg_left h_phi_bound (le_of_lt hc_pos)

    -- Divide by |1-w|
    have h_ne := ne_of_gt h_one_sub_w_norm_pos
    calc ‖gen.op ⟨ψ, hψ⟩ - ↑μ • ψ‖
        = ‖(1 : ℂ) - w‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ⟩ - (↑μ • ψ)‖) := by
            field_simp [h_ne]
            exact Eq.symm (mul_div_cancel_right₀ ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ h_ne)
      _ ≥ ‖(1 : ℂ) - w‖⁻¹ * (c * ‖ψ‖) :=
            mul_le_mul_of_nonneg_left h_chain (inv_nonneg.mpr (norm_nonneg _))
      _ = c / ‖(1 : ℂ) - w‖ * ‖ψ‖ := by ring

/--
**Möbius norm (convenience duplicate).**

This is a duplicate of `mobius_norm_one` for convenience in proofs
that don't want to unfold the definition.
-/
lemma mobius_norm_eq_one (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  exact mobius_norm_one μ hμ_ne

/--
**Definition of normal operator.**

A continuous linear map T is **normal** if it commutes with its adjoint:
T* ∘ T = T ∘ T*

### Significance

Normal operators have the nicest spectral theory:
- The spectral theorem applies
- Eigenspaces for distinct eigenvalues are orthogonal
- ‖Tx‖ = ‖T*x‖ for all x
- The spectrum equals the approximate point spectrum

### Examples

- Self-adjoint operators (T* = T)
- Unitary operators (T*T = TT* = I)
- U - wI for unitary U (proved in `unitary_sub_scalar_isNormal'`)
-/
def ContinuousLinearMap.IsNormal (T : H →L[ℂ] H) : Prop :=
  T.adjoint.comp T = T.comp T.adjoint

/--
**Unitary minus scalar is normal (Unitary version).**

### Statement

If U is unitary and w ∈ ℂ, then U - wI is normal.

### Proof

This is a variant of `unitary_sub_scalar_isNormal` that takes the
`Unitary` predicate instead of the explicit conditions.

### Use Case

When working with the Cayley transform U (which satisfies `Unitary U`),
this gives normality of U - wI directly.
-/
lemma unitary_sub_scalar_isNormal' {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint := by
  -- (U - wI)* = U* - w̄I
  have h_adj : (U - w • 1).adjoint = U.adjoint - (starRingEnd ℂ w) • 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
               inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp_all only [RingHomCompTriple.comp_apply, RingHom.id_apply]

  rw [h_adj]
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]

  -- Use U*U = I and UU* = I from unitarity
  have h1 : U.adjoint (U x) = x := by
    have := congr_arg (· x) hU.1
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  have h2 : U (U.adjoint x) = x := by
    have := congr_arg (· x) hU.2
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this

  simp only [map_sub, map_smul, h1, h2]
  module


/-!
## Normal Operators: Bounded Below ⟺ Invertible

This section establishes a crucial fact for normal operators (including
unitary operators): being bounded below is equivalent to being invertible.

### Why Normal Operators Are Special

For a general operator T, "bounded below" (∃c > 0, ‖Tx‖ ≥ c‖x‖) only implies:
- T is injective
- T has closed range

But the range might not be all of H!

For **normal** operators (T*T = TT*), bounded below additionally implies:
- Range(T) is dense (because ker(T*) = ker(T) = {0} for normal T)
- Combined with closed range: Range(T) = H

Therefore: **normal + bounded below ⟹ bijective ⟹ invertible**

### The Key Lemma Chain

1. `isUnit_bounded_below`: Invertible ⟹ bounded below (general)
2. `normal_bounded_below_surjective`: Normal + bounded below ⟹ surjective
3. `normal_bounded_below_isUnit`: Normal + bounded below ⟹ invertible

### Application to Unitary Operators

Since U - wI is normal when U is unitary (by `unitary_sub_scalar_isNormal'`),
we can characterize the spectrum:

    w ∈ σ(U)  ⟺  U - wI not invertible  ⟺  U - wI not bounded below
              ⟺  w is an approximate eigenvalue

This gives the **approximate eigenvalue characterization** of the spectrum
for normal operators.
-/

/--
**Invertible implies bounded below.**

### Statement

If T is invertible (IsUnit), then there exists c > 0 such that
‖Tx‖ ≥ c‖x‖ for all x.

### Proof

Let T_inv be the inverse of T. Then:
- T_inv(Tx) = x for all x
- ‖x‖ = ‖T_inv(Tx)‖ ≤ ‖T_inv‖ · ‖Tx‖

Rearranging: ‖Tx‖ ≥ ‖T_inv‖⁻¹ · ‖x‖

So c = ‖T_inv‖⁻¹ = ‖T⁻¹‖⁻¹ works.

### The Constant

c = ‖T⁻¹‖⁻¹ is the optimal constant. In fact:
- c = inf { ‖Tx‖/‖x‖ : x ≠ 0 } (the "lower norm" of T)
- c = dist(0, σ(T)) for normal T

### Significance

This is the "easy direction" of the bounded-below/invertible equivalence.
It holds for all operators, not just normal ones.
-/
lemma isUnit_bounded_below [Nontrivial H] {T : H →L[ℂ] H} (hT : IsUnit T) :
    ∃ c > 0, ∀ φ, ‖T φ‖ ≥ c * ‖φ‖ := by
  obtain ⟨⟨T, T_inv, hT_left, hT_right⟩, rfl⟩ := hT

  -- T_inv ≠ 0 (otherwise T · T_inv = 0 ≠ 1)
  have hT_inv_ne : T_inv ≠ 0 := by
    intro h
    have h_one_eq : (1 : H →L[ℂ] H) = 0 := by
      calc (1 : H →L[ℂ] H) = T_inv * T := hT_right.symm
        _ = 0 * T := by rw [h]
        _ = 0 := zero_mul T
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have : x = 0 := by simpa using congr_arg (· x) h_one_eq
    exact hx this

  have hT_inv_norm_pos : ‖T_inv‖ > 0 := norm_pos_iff.mpr hT_inv_ne

  -- The constant c = ‖T_inv‖⁻¹
  use ‖T_inv‖⁻¹, inv_pos.mpr hT_inv_norm_pos

  intro φ
  -- Key: T_inv(Tφ) = φ, so ‖φ‖ ≤ ‖T_inv‖ · ‖Tφ‖
  have h_eq : T_inv (T φ) = φ := by
    have := congr_arg (· φ) hT_right
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
    exact this
  have h_bound : ‖φ‖ ≤ ‖T_inv‖ * ‖T φ‖ := by
    calc ‖φ‖ = ‖T_inv (T φ)‖ := by rw [h_eq]
      _ ≤ ‖T_inv‖ * ‖T φ‖ := ContinuousLinearMap.le_opNorm T_inv (T φ)
  exact (inv_mul_le_iff₀ hT_inv_norm_pos).mpr h_bound

/--
**Normal + bounded below ⟹ surjective.**

### Statement

If T is normal (T*T = TT*) and bounded below (‖Tx‖ ≥ c‖x‖ for some c > 0),
then T is surjective.

### Proof Structure

**Step 1: Range(T) is dense.**

We show Range(T)^⊥ = {0} using `dense_range_of_orthogonal_trivial`.

If y ⊥ Range(T), then ⟨Tx, y⟩ = 0 for all x.
This means ⟨x, T*y⟩ = 0 for all x, so T*y = 0.

For normal T: ‖T*y‖ = ‖Ty‖ (key property of normal operators!).
So T*y = 0 ⟹ ‖Ty‖ = 0 ⟹ Ty = 0.

By bounded below: ‖Ty‖ ≥ c‖y‖, so ‖y‖ = 0, hence y = 0.

**Step 2: Range(T) is closed.**

Bounded below implies closed range (standard functional analysis).

Proof: If Tx_n → z, then (x_n) is Cauchy (by bounded below), so x_n → x.
By continuity, Tx = z, so z ∈ Range(T).

**Step 3: Dense + closed = surjective.**

By `surjective_of_isClosed_range_of_dense`.

### The Key Property of Normal Operators

The crucial fact is: **for normal T, ker(T*) = ker(T)**.

Proof: T*T = TT* implies ⟨T*Tx, x⟩ = ⟨TT*x, x⟩, hence ‖Tx‖² = ‖T*x‖².

This is what makes normal operators special: the kernel of T* equals
the kernel of T, so Range(T)^⊥ = ker(T*) = ker(T) = {0} when T is injective.

### Non-Example

The unilateral shift S is bounded below (in fact, isometric) but not
surjective. This is because S is NOT normal: S*S = I but SS* ≠ I.
-/
lemma normal_bounded_below_surjective {T : H →L[ℂ] H}
    (hT : T.adjoint.comp T = T.comp T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    Function.Surjective T := by

  /-
  ═══════════════════════════════════════════════════════════════════════════
  STEP 1: Range(T) is dense
  ═══════════════════════════════════════════════════════════════════════════

  We show: if y ⊥ Range(T), then y = 0.
  -/
  have h_range_dense : Dense (Set.range T) := by
    apply dense_range_of_orthogonal_trivial
    intro y hy

    -- ∀ x, ⟨Tx, y⟩ = 0 means T*y = 0
    have hT_adj_y : T.adjoint y = 0 := by
      apply ext_inner_left ℂ
      intro x
      rw [inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
      exact hy x

    /-
    For normal T: ‖T*y‖ = ‖Ty‖

    Proof: T*T = TT* implies
      ⟨T*Ty, y⟩ = ⟨TT*y, y⟩
      ‖Ty‖² = ⟨T*Ty, y⟩ and ‖T*y‖² = ⟨TT*y, y⟩
    So ‖Ty‖² = ‖T*y‖², hence ‖Ty‖ = ‖T*y‖.
    -/
    have h_norm_eq : ‖T.adjoint y‖ = ‖T y‖ := by
      have h1 : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T (T.adjoint y), y⟫_ℂ := by
        calc ⟪T.adjoint (T y), y⟫_ℂ
            = ⟪(T.adjoint.comp T) y, y⟫_ℂ := rfl
          _ = ⟪(T.comp T.adjoint) y, y⟫_ℂ := by rw [hT]
          _ = ⟪T (T.adjoint y), y⟫_ℂ := rfl
      have h2 : ‖T.adjoint y‖^2 = (⟪T (T.adjoint y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_right T (T.adjoint y) y
        have h_inner : (⟪T.adjoint y, T.adjoint y⟫_ℂ).re = ‖T.adjoint y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        linarith [h_inner, congrArg Complex.re h]
      have h3 : ‖T y‖^2 = (⟪T.adjoint (T y), y⟫_ℂ).re := by
        have h := ContinuousLinearMap.adjoint_inner_left T (T y) y
        have h_inner : (⟪T y, T y⟫_ℂ).re = ‖T y‖^2 := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
          simp only [coe_algebraMap]
          rw [← ofReal_pow]
          exact Complex.ofReal_re _
        have h_adj : ⟪T.adjoint (T y), y⟫_ℂ = ⟪T y, T y⟫_ℂ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        rw [h_adj]
        exact h_inner.symm
      have h_sq : ‖T.adjoint y‖^2 = ‖T y‖^2 := by rw [h2, h3, h1]
      nlinarith [norm_nonneg (T.adjoint y), norm_nonneg (T y),
                 sq_nonneg (‖T.adjoint y‖ - ‖T y‖)]

    -- T*y = 0 implies ‖Ty‖ = 0
    rw [hT_adj_y, norm_zero] at h_norm_eq
    have h_Ty_zero : ‖T y‖ = 0 := by rw [← h_norm_eq]

    -- Bounded below: ‖Ty‖ ≥ c‖y‖, so y = 0
    have h := hc_bound y
    rw [h_Ty_zero] at h
    have hy_norm_zero : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
    exact norm_eq_zero.mp hy_norm_zero

  /-
  ═══════════════════════════════════════════════════════════════════════════
  STEP 2: Range(T) is closed
  ═══════════════════════════════════════════════════════════════════════════

  Bounded below implies closed range.

  Proof: If Tx_n → z, we show z ∈ Range(T).

  Key: (x_n) is Cauchy because ‖x_n - x_m‖ ≤ c⁻¹‖Tx_n - Tx_m‖.
  Since H is complete, x_n → x for some x.
  By continuity, Tx = z, so z ∈ Range(T).
  -/
  have h_range_closed : IsClosed (Set.range T) := by
    rw [← isSeqClosed_iff_isClosed]
    intro xseq x hxseq hx_lim
    -- xseq n ∈ Range(T) and xseq → x, need x ∈ Range(T)

    -- Get preimages: T(yseq n) = xseq n
    choose yseq hyseq using hxseq

    -- yseq is Cauchy because T is bounded below
    have h_cauchy : CauchySeq yseq := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      -- Since xseq converges, it's Cauchy
      have hx_cauchy := hx_lim.cauchySeq
      rw [Metric.cauchySeq_iff'] at hx_cauchy
      obtain ⟨N, hN⟩ := hx_cauchy (c * ε) (by positivity)
      use N
      intro n hn
      have h_bound := hc_bound (yseq n - yseq N)
      rw [map_sub] at h_bound
      have h_xdist : ‖xseq n - xseq N‖ < c * ε := by
        rw [← dist_eq_norm]
        exact hN n hn
      have h_ydist : c * ‖yseq n - yseq N‖ ≤ ‖T (yseq n) - T (yseq N)‖ := h_bound
      rw [hyseq n, hyseq N] at h_ydist
      calc dist (yseq n) (yseq N)
          = ‖yseq n - yseq N‖ := dist_eq_norm _ _
        _ ≤ ‖xseq n - xseq N‖ / c := by
            have : c * ‖yseq n - yseq N‖ ≤ ‖xseq n - xseq N‖ := h_ydist
            exact (le_div_iff₀' hc_pos).mpr h_ydist
        _ < (c * ε) / c := by apply div_lt_div_of_pos_right h_xdist hc_pos
        _ = ε := by field_simp

    -- yseq converges to some y' (completeness)
    obtain ⟨y', hy'_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy

    -- T y' = x (by continuity)
    have hTy' : T y' = x := by
      have hT_cont := T.continuous.tendsto y'
      have hTyseq_lim : Tendsto (fun n => T (yseq n)) atTop (𝓝 (T y')) := hT_cont.comp hy'_lim
      have hTyseq_eq : ∀ n, T (yseq n) = xseq n := hyseq
      simp_rw [hTyseq_eq] at hTyseq_lim
      exact tendsto_nhds_unique hTyseq_lim hx_lim

    exact ⟨y', hTy'⟩

  /-
  ═══════════════════════════════════════════════════════════════════════════
  STEP 3: Dense + closed = surjective
  ═══════════════════════════════════════════════════════════════════════════
  -/
  exact surjective_of_isClosed_range_of_dense T h_range_closed h_range_dense

/--
**Normal + bounded below ⟹ invertible.**

### Statement

If T is normal and bounded below, then T is invertible (IsUnit).

### Proof

Combine:
- Bounded below ⟹ injective (immediate from ‖Tx‖ ≥ c‖x‖)
- Normal + bounded below ⟹ surjective (by `normal_bounded_below_surjective`)
- Injective + surjective ⟹ bijective ⟹ invertible

### Significance

This completes the equivalence for normal operators:

    T normal ⟹ (T invertible ⟺ T bounded below)

Combined with `isUnit_bounded_below`, we have:
- Invertible ⟹ bounded below (always)
- Bounded below ⟹ invertible (for normal T)

### Application

For the Cayley transform U (which is unitary, hence normal):
- U - wI is normal (by `unitary_sub_scalar_isNormal'`)
- U - wI invertible ⟺ U - wI bounded below
- This characterizes the spectrum of U
-/
lemma normal_bounded_below_isUnit [Nontrivial H] {T : H →L[ℂ] H}
    (hT : T.adjoint * T = T * T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    IsUnit T := by
  -- Bounded below implies injective
  have h_inj : Function.Injective T := by
    intro x y hxy
    have : ‖T (x - y)‖ = 0 := by simp [hxy]
    have h := hc_bound (x - y)
    rw [this] at h
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

  -- Normal + bounded below implies surjective
  have h_surj := normal_bounded_below_surjective hT c hc_pos hc_bound

  -- Bijective implies invertible
  have h_ker : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr h_inj
  have h_range : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr h_surj
  let e := ContinuousLinearEquiv.ofBijective T h_ker h_range
  exact ⟨⟨T, e.symm.toContinuousLinearMap,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_apply_symm_apply T h_ker h_range x,
         by ext x;
            simp only [ContinuousLinearMap.coe_mul, ContinuousLinearEquiv.coe_coe,
              Function.comp_apply, ContinuousLinearMap.one_apply]
            exact ContinuousLinearEquiv.ofBijective_symm_apply_apply T h_ker h_range x⟩,
            rfl⟩

/-!
### Approximate Eigenvalue Characterization

For normal operators, the spectrum has a beautiful characterization in
terms of **approximate eigenvalues**.

**Definition:** w is an approximate eigenvalue of T if there exist
unit vectors φ_n with ‖(T - wI)φ_n‖ → 0.

**Theorem:** For normal T, w ∈ σ(T) ⟺ w is an approximate eigenvalue.

This is stronger than the general case, where we only have:
    eigenvalue ⟹ approximate eigenvalue ⟹ in spectrum

For normal operators, all three coincide (for points in the spectrum).
-/

/--
**Not invertible ⟹ approximate eigenvalue (for unitary operators).**

### Statement

If U is unitary and U - wI is not invertible, then w is an approximate
eigenvalue: for every ε > 0, there exists a unit vector φ with
‖(U - wI)φ‖ < ε.

### Proof (contrapositive)

Suppose w is NOT an approximate eigenvalue. Then there exists ε > 0
such that ‖(U - wI)φ‖ ≥ ε for all unit vectors φ.

This extends to: ‖(U - wI)φ‖ ≥ ε‖φ‖ for all φ (homogeneity).

So U - wI is bounded below with constant ε.

Since U - wI is normal (by `unitary_sub_scalar_isNormal'`), bounded
below implies invertible (by `normal_bounded_below_isUnit`).

Contradiction!

### Significance

This is half of the approximate eigenvalue characterization of the
spectrum for unitary operators:

    w ∈ σ(U) ⟹ w is an approximate eigenvalue

The converse is `unitary_not_approx_eigenvalue_isUnit`.
-/
lemma unitary_not_isUnit_approx_eigenvalue [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬IsUnit (U - w • ContinuousLinearMap.id ℂ H)) :
    ∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε := by
  -- Proof by contradiction
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∃ ε > 0, ∀ φ with ‖φ‖ = 1, ‖(U - wI)φ‖ ≥ ε
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_neg

  -- Extend from unit vectors to all vectors
  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      -- Apply the bound to the normalized vector φ/‖φ‖
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _

  -- U - wI is normal (since U is unitary)
  have h_normal := unitary_sub_scalar_isNormal' hU w

  -- Normal + bounded below ⟹ invertible
  have h_isUnit := normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below

  -- Contradiction!
  exact h_not h_isUnit

/--
**Not approximate eigenvalue ⟹ invertible (for unitary operators).**

### Statement

If U is unitary and w is NOT an approximate eigenvalue (i.e., there
exists ε > 0 such that ‖(U - wI)φ‖ ≥ ε for all unit vectors φ), then
U - wI is invertible.

### Proof

Direct application of `normal_bounded_below_isUnit`:
1. Extend the bound from unit vectors to all vectors
2. U - wI is normal (by `unitary_sub_scalar_isNormal'`)
3. Normal + bounded below ⟹ invertible

### Significance

This is the other half of the approximate eigenvalue characterization:

    w not an approximate eigenvalue ⟹ w ∉ σ(U)

Equivalently: w ∈ σ(U) ⟹ w is an approximate eigenvalue.

Combined with `unitary_not_isUnit_approx_eigenvalue`, we get:

    **w ∈ σ(U) ⟺ w is an approximate eigenvalue of U**

This is a fundamental characterization of the spectrum for normal operators.
-/
lemma unitary_not_approx_eigenvalue_isUnit [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε) :
    IsUnit (U - w • ContinuousLinearMap.id ℂ H) := by
  push_neg at h_not
  -- h_not : ∃ ε > 0, ∀ φ, ‖φ‖ = 1 → ‖(U - wI)φ‖ ≥ ε
  obtain ⟨ε, hε_pos, hε_bound⟩ := h_not

  -- Extend to bounded below on all vectors
  have h_bounded_below : ∀ φ, ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ ≥ ε * ‖φ‖ := by
    intro φ
    by_cases hφ : φ = 0
    · simp [hφ]
    · have hφ_norm_pos : ‖φ‖ > 0 := norm_pos_iff.mpr hφ
      have h_unit := hε_bound (‖φ‖⁻¹ • φ) (by rw [norm_smul, norm_inv, norm_norm]; field_simp)
      calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
          = ‖φ‖ * (‖φ‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖) := by field_simp
        _ = ‖φ‖ * ‖‖φ‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ‖ := by
            congr 1; rw [norm_smul, norm_inv, norm_norm]
        _ = ‖φ‖ * ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ‖⁻¹ • φ)‖ := by
            congr 1; simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
              ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq,
              ContinuousLinearMap.map_smul_of_tower]
        _ ≥ ‖φ‖ * ε := mul_le_mul_of_nonneg_left h_unit (norm_nonneg φ)
        _ = ε * ‖φ‖ := mul_comm _ _

  -- U - wI is normal
  have h_normal := unitary_sub_scalar_isNormal' hU w

  -- Normal + bounded below → IsUnit
  exact normal_bounded_below_isUnit h_normal ε hε_pos h_bounded_below



/--
**Lower bound on domain element norm from approximate eigenvalue condition.**

If ψ ∈ D(A) satisfies:
1. ‖(A + iI)ψ‖ = 1  (normalized in the graph norm sense)
2. ‖(A - μI)ψ‖ ≤ δ  (approximate μ-eigenvector)
3. δ² < 1 + μ²      (small enough approximation)

Then: ‖ψ‖ ≥ (√(1 + μ² - δ²) - |μ|δ) / (1 + μ²)

As δ → 0, this gives ‖ψ‖ ≥ 1/√(1 + μ²) - O(δ).
-/
lemma approx_eigenvalue_norm_lower_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (ψ : H) (hψ : ψ ∈ gen.domain) (hψ_ne : ψ ≠ 0)
    (h_norm : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖ = 1)
    (δ : ℝ) (hδ_pos : 0 ≤ δ) (hδ_small : δ^2 < 1 + μ^2)
    (h_approx : ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≤ δ) :
    ‖ψ‖ ≥ (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) := by
  
  /-
  Step 1: From self-adjointness, ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖².
  Combined with h_norm: ‖Aψ‖² + ‖ψ‖² = 1.
  -/
  have h_pythag := self_adjoint_norm_sq_add gen hsa ψ hψ
  have h_sum_one : ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2 = 1 := by
    have : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 = 1 := by rw [h_norm]; ring
    linarith [h_pythag]
  
  /-
  Step 2: From ‖(A - μI)ψ‖ ≤ δ, extract bounds on ‖Aψ‖.
  
  Triangle inequality: |‖Aψ‖ - |μ|‖ψ‖| ≤ ‖Aψ - μψ‖ ≤ δ
  
  Therefore: ‖Aψ‖ ≥ |μ|‖ψ‖ - δ  (if this is positive)
  -/
  have h_Aμψ_bound : ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≤ δ := h_approx
  
  -- Convert to real-valued norm comparison
  have h_triangle : |‖gen.op ⟨ψ, hψ⟩‖ - |μ| * ‖ψ‖| ≤ δ := by
    have h1 : ‖(↑μ : ℂ) • ψ‖ = |μ| * ‖ψ‖ := by
      rw [norm_smul]
      simp only [norm_real, Real.norm_eq_abs]
    calc |‖gen.op ⟨ψ, hψ⟩‖ - |μ| * ‖ψ‖|
        = |‖gen.op ⟨ψ, hψ⟩‖ - ‖(↑μ : ℂ) • ψ‖| := by rw [h1]
      _ ≤ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ := abs_norm_sub_norm_le _ _
      _ ≤ δ := h_approx
  
  -- Extract: ‖Aψ‖ ≥ |μ|‖ψ‖ - δ
  have h_Aψ_lower : ‖gen.op ⟨ψ, hψ⟩‖ ≥ |μ| * ‖ψ‖ - δ := by
    have ⟨h1, _⟩ := abs_le.mp h_triangle
    -- h1 : -δ ≤ ‖Aψ‖ - |μ|‖ψ‖
    -- Rearranging: ‖Aψ‖ ≥ |μ|‖ψ‖ - δ
    linarith
  
  /-
  Step 3: Substitute into ‖Aψ‖² + ‖ψ‖² = 1.
  
  If ‖Aψ‖ ≥ |μ|‖ψ‖ - δ, then ‖Aψ‖² ≥ (|μ|‖ψ‖ - δ)² (when the RHS is ≥ 0).
  
  Therefore: (|μ|‖ψ‖ - δ)² + ‖ψ‖² ≤ 1
  
  Expanding: μ²‖ψ‖² - 2|μ|δ‖ψ‖ + δ² + ‖ψ‖² ≤ 1
             (1 + μ²)‖ψ‖² - 2|μ|δ‖ψ‖ + (δ² - 1) ≤ 0
  -/
  set x := ‖ψ‖ with hx_def
  have hx_pos : x > 0 := norm_pos_iff.mpr hψ_ne
  
  /-
  Step 4: Solve the quadratic inequality.
  
  (1 + μ²)x² - 2|μ|δx + (δ² - 1) ≤ 0
  
  This is a downward-opening parabola (coefficient of x² is positive,
  but the inequality is ≤ 0). The roots are:
  
  x = [2|μ|δ ± √(4μ²δ² - 4(1+μ²)(δ² - 1))] / [2(1+μ²)]
    = [|μ|δ ± √(μ²δ² - (1+μ²)δ² + (1+μ²))] / (1+μ²)
    = [|μ|δ ± √(1 + μ² - δ²)] / (1+μ²)
  
  For the quadratic to be ≤ 0, x must be between the roots.
  The smaller root is x₋ = [|μ|δ - √(1+μ²-δ²)] / (1+μ²).
  
  But wait—we need x ≥ x₋, not x ≤ x₊!
  
  Actually, let me reconsider. We have ‖Aψ‖² ≥ (|μ|x - δ)² when |μ|x ≥ δ.
  So: (|μ|x - δ)² + x² ≤ ‖Aψ‖² + x² = 1
  
  This gives (|μ|x - δ)² ≤ 1 - x², i.e., |μ|x - δ ≤ √(1 - x²).
  
  Hmm, let me use the other direction. We have:
  ‖Aψ‖² = 1 - x²
  ‖Aψ‖ ≤ |μ|x + δ  (from triangle inequality, other direction)
  
  So: 1 - x² = ‖Aψ‖² ≤ (|μ|x + δ)²
      1 - x² ≤ μ²x² + 2|μ|δx + δ²
      1 - δ² ≤ x²(1 + μ²) + 2|μ|δx
      1 - δ² ≤ (1 + μ²)x² + 2|μ|δx
  
  Rearranging: (1 + μ²)x² + 2|μ|δx - (1 - δ²) ≥ 0
               (1 + μ²)x² + 2|μ|δx + (δ² - 1) ≥ 0
  -/
  
  have h_Aψ_upper : ‖gen.op ⟨ψ, hψ⟩‖ ≤ |μ| * x + δ := by
    have ⟨_, h2⟩ := abs_le.mp h_triangle
    -- h2 : ‖Aψ‖ - |μ|‖ψ‖ ≤ δ
    -- Rearranging: ‖Aψ‖ ≤ |μ|‖ψ‖ + δ
    linarith
  
  have h_Aψ_sq : ‖gen.op ⟨ψ, hψ⟩‖^2 = 1 - x^2 := by linarith [h_sum_one]
  
  have h_ineq : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) ≥ 0 := by
    have h1 : 1 - x^2 ≤ (|μ| * x + δ)^2 := by
      calc 1 - x^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 := h_Aψ_sq.symm
        _ ≤ (|μ| * x + δ)^2 := by
            apply sq_le_sq'
            · linarith [norm_nonneg (gen.op ⟨ψ, hψ⟩), hδ_pos, 
                        mul_nonneg (abs_nonneg μ) (le_of_lt hx_pos)]
            · exact h_Aψ_upper
    calc (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1)
        = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 + x^2 - 1 := by ring
      _ = (|μ| * x + δ)^2 - (1 - x^2) := by rw [← sq_abs μ]; ring
      _ ≥ 0 := by linarith [h1]
  
  /-
  Step 5: The quadratic (1+μ²)t² + 2|μ|δt + (δ² - 1) ≥ 0 
  
  has roots at t = [-|μ|δ ± √(μ²δ² - (1+μ²)(δ²-1))] / (1+μ²)
                 = [-|μ|δ ± √(1 + μ² - δ²)] / (1+μ²)
  
  (using discriminant: μ²δ² - (1+μ²)(δ²-1) = μ²δ² - δ² - μ²δ² + 1 + μ² = 1 + μ² - δ²)
  
  The parabola opens upward (coefficient 1+μ² > 0), so the inequality ≥ 0
  holds when t ≤ t₋ or t ≥ t₊, where:
  
  t₋ = [-|μ|δ - √(1+μ²-δ²)] / (1+μ²) < 0
  t₊ = [-|μ|δ + √(1+μ²-δ²)] / (1+μ²)
  
  Since x = ‖ψ‖ > 0 and t₋ < 0, we must have x ≥ t₊.
  -/
  
  have h_discriminant : 1 + μ^2 - δ^2 > 0 := by linarith [hδ_small]
  
  have h_sqrt_exists : Real.sqrt (1 + μ^2 - δ^2) > 0 := Real.sqrt_pos.mpr h_discriminant
  
  -- The larger root
  set t_plus := (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) with htplus_def -- unexpected token '₊'; expected ':='
  
  -- The smaller root  
  set t_minus := (-Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) with htminus_def
  
  have htminus_neg : t_minus < 0 := by
    rw [htminus_def]
    apply div_neg_of_neg_of_pos
    · linarith [h_sqrt_exists, mul_nonneg (abs_nonneg μ) hδ_pos]
    · linarith [sq_nonneg μ]
  
  have h_coeff_pos : 1 + μ^2 > 0 := by linarith [sq_nonneg μ]
  
  have h_at_root : (1 + μ^2) * t_plus^2 + 2 * |μ| * δ * t_plus + (δ^2 - 1) = 0 := by
    rw [htplus_def]
    field_simp
    -- First, unify μ^2 and |μ|^2 so ring_nf treats them consistently
    rw [← sq_abs μ]
    ring_nf
    -- Now the sqrt contains (1 + (|μ|^2 - δ^2))
    have h_sq : Real.sqrt (1 + (|μ|^2 - δ^2)) ^ 2 = 1 + (|μ|^2 - δ^2) := by
      apply Real.sq_sqrt
      have : |μ|^2 = μ^2 := sq_abs μ
      linarith [h_discriminant]
    rw [h_sq]
    ring
  
  -- For upward parabola: f(x) ≥ 0 and x > 0 and t₋ < 0 implies x ≥ t₊
  have h_x_ge_t_plus : x ≥ t_plus := by
    by_contra h_lt
    push_neg at h_lt
    -- If t₋ < x < t₊, then the quadratic is negative (contradiction)
    have h_neg : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) < 0 := by
      -- The quadratic is negative between roots for upward parabola
      have h_factored : ∀ t, (1 + μ^2) * t^2 + 2 * |μ| * δ * t + (δ^2 - 1) = 
                  (1 + μ^2) * (t - t_minus) * (t - t_plus) := by
        intro t
        rw [htplus_def, htminus_def]
        field_simp
        rw [← sq_abs μ]
        ring_nf
        have h_sq : Real.sqrt (1 + (|μ|^2 - δ^2)) ^ 2 = 1 + (|μ|^2 - δ^2) := by
          apply Real.sq_sqrt
          have : |μ|^2 = μ^2 := sq_abs μ
          linarith [h_discriminant]
        rw [h_sq]
        ring
      rw [h_factored]
      apply mul_neg_of_pos_of_neg
      · -- Need: (1 + μ^2) * (x - t_minus) > 0
        apply mul_pos h_coeff_pos
        linarith [htminus_neg]  -- x > 0 > t_minus, so x - t_minus > 0
      · -- Need: x - t_plus < 0
        linarith [h_lt]
    linarith [h_ineq, h_neg]

  -- Conclude
  calc ‖ψ‖ = x := rfl
    _ ≥ t_plus := h_x_ge_t_plus
    _ = (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2) := htplus_def

set_option maxHeartbeats 400000
/--
**Backward approximate eigenvalue correspondence:** U → A.

### Statement

If w = (μ - i)/(μ + i) is an approximate eigenvalue of U, then μ is an
approximate eigenvalue of A.

More precisely:

    (∀ε > 0, ∃ unit φ, ‖(U - wI)φ‖ < ε)
    ⟹
    (∀C > 0, ∃ ψ ∈ D(A) with ψ ≠ 0, ‖(A - μI)ψ‖ < C‖ψ‖)

### Proof Strategy

Given ε > 0, we need to find ψ with ‖(A - μI)ψ‖ < C‖ψ‖.

**Step 1:** Choose ε small enough.

Set ε' = C · |1-w| / (2√(1 + μ²)). Find unit φ with ‖(U - wI)φ‖ < ε'.

**Step 2:** Extract ψ from φ via resolvent.

Set ψ = R_{-i}(φ), so (A + iI)ψ = φ. Then ψ ∈ D(A) and ψ ≠ 0.

**Step 3:** Apply the intertwining identity.

By `cayley_shift_identity`:
    (U - wI)φ = (1 - w)(A - μI)ψ

So ‖(A - μI)ψ‖ = ‖(U - wI)φ‖ / |1 - w|.

**Step 4:** Use the norm lower bound.

Since ‖φ‖ = ‖(A + iI)ψ‖ = 1, by `approx_eigenvalue_norm_lower_bound`:
    ‖ψ‖ ≥ 1/(2√(1 + μ²))

**Step 5:** Chain the inequalities.

    ‖(A - μI)ψ‖ = ‖(U - wI)φ‖ / |1-w|
                < ε' / |1-w|
                = C / (2√(1 + μ²))
                ≤ C · ‖ψ‖ ✓

### Why the Formulation?

The "approximate eigenvalue of A" condition is stated as:
    ∀C > 0, ∃ψ ≠ 0, ‖(A - μI)ψ‖ < C‖ψ‖

This is equivalent to the unit-vector formulation but more convenient
when working with the unbounded operator A (where normalization may
take you outside D(A) for a dense domain).
-/
lemma cayley_approx_eigenvalue_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) →
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖) := by
  intro h_approx C hC

  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def

  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne

  set denom := Real.sqrt (1 + μ^2) with hdenom
  have hdenom_pos : denom > 0 := Real.sqrt_pos.mpr (by linarith [sq_nonneg μ])
  have hdenom_ge_one : denom ≥ 1 := by
    rw [hdenom]
    calc Real.sqrt (1 + μ^2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
      _ = 1 := Real.sqrt_one

  /-
  KEY CHANGE: Use min(C, 1/2) to ensure δ is small enough for the norm lower bound.
  -/
  set C' := min C (1/2) with hC'_def
  have hC'_pos : C' > 0 := lt_min hC (by norm_num : (0:ℝ) < 1/2)
  have hC'_le_half : C' ≤ 1/2 := min_le_right C (1/2)
  have hC'_le_C : C' ≤ C := min_le_left C (1/2)

  obtain ⟨φ, hφ_norm, hφ_bound⟩ := h_approx (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) (by positivity)

  set ψ := Resolvent.resolvent_at_neg_i gen hsa φ with hψ_def
  have hψ_mem : ψ ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa φ
  have hφ_eq : gen.op ⟨ψ, hψ_mem⟩ + I • ψ = φ := Resolvent.resolvent_solution_eq_plus gen hsa φ

  use ψ, hψ_mem

  have hφ_ne : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ_norm; exact one_ne_zero hφ_norm.symm
  have hψ_ne : ψ ≠ 0 := by
    intro h
    have hψ_eq_zero : (⟨ψ, hψ_mem⟩ : gen.domain) = 0 := by ext; exact h
    have : φ = 0 := by
      calc φ = gen.op ⟨ψ, hψ_mem⟩ + I • ψ := hφ_eq.symm
        _ = gen.op 0 + I • 0 := by rw [hψ_eq_zero, h]
        _ = 0 := by simp
    exact hφ_ne this

  constructor
  · exact norm_ne_zero_iff.mpr hψ_ne

  have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ_mem
  simp only at h_key
  rw [← hφ_eq.symm] at h_key

  have h_norm_eq : ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ =
      ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := by
    have : (U - w • ContinuousLinearMap.id ℂ H) φ =
           ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ) := h_key
    rw [this, norm_smul]
    field_simp [ne_of_gt h_one_sub_w_norm_pos]

  have h_norm_identity : ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 = 1 := by
    have h := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    rw [hφ_eq, hφ_norm] at h
    linarith [h, sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]

  /-
  Step 4: Derive the δ bound and prove ‖ψ‖ ≥ 1/(2*denom).
  -/
  
  -- First, establish the δ bound
  set δ := ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ with hδ_def
  
  have hδ_bound : δ < C' / (2 * denom) := by
    calc δ = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := h_norm_eq
      _ < (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) / ‖(1 : ℂ) - w‖ := by
          apply div_lt_div_of_pos_right hφ_bound h_one_sub_w_norm_pos
      _ = C' / (2 * denom) := by field_simp
  
  have hδ_nonneg : δ ≥ 0 := norm_nonneg _
  
  -- Key bound: δ < 1/(4*denom) since C' ≤ 1/2
  have hδ_small : δ < 1 / (4 * denom) := by
    calc δ < C' / (2 * denom) := hδ_bound
      _ ≤ (1/2) / (2 * denom) := by apply div_le_div_of_nonneg_right hC'_le_half (by positivity)
      _ = 1 / (4 * denom) := by ring
  
  -- Now prove the norm lower bound using quadratic analysis
  have hψ_norm_lower : ‖ψ‖ ≥ 1 / (2 * denom) := by
    -- From triangle inequality: ‖Aψ‖ ≤ |μ|‖ψ‖ + δ
    have h_Aψ_upper : ‖gen.op ⟨ψ, hψ_mem⟩‖ ≤ |μ| * ‖ψ‖ + δ := by
      have h1 : ‖(↑μ : ℂ) • ψ‖ = |μ| * ‖ψ‖ := by
        rw [norm_smul]
        simp only [norm_real, Real.norm_eq_abs]
      calc ‖gen.op ⟨ψ, hψ_mem⟩‖ 
        = ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ + (↑μ : ℂ) • ψ‖ := by rw [sub_add_cancel]
        _ ≤ ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ + ‖(↑μ : ℂ) • ψ‖ := norm_add_le _ _
        _ = δ + |μ| * ‖ψ‖ := by rw [← hδ_def, h1]
        _ = |μ| * ‖ψ‖ + δ := by ring

    -- Quadratic constraint: 1 - ‖ψ‖² = ‖Aψ‖² ≤ (|μ|‖ψ‖ + δ)²
    have h_quad : 1 - ‖ψ‖^2 ≤ (|μ| * ‖ψ‖ + δ)^2 := by
      have h1 : ‖gen.op ⟨ψ, hψ_mem⟩‖^2 = 1 - ‖ψ‖^2 := by linarith [h_norm_identity]
      calc 1 - ‖ψ‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 := h1.symm
        _ ≤ (|μ| * ‖ψ‖ + δ)^2 := by
            apply sq_le_sq'
            · linarith [norm_nonneg (gen.op ⟨ψ, hψ_mem⟩), 
                        mul_nonneg (abs_nonneg μ) (norm_nonneg ψ), hδ_nonneg]
            · exact h_Aψ_upper

    -- Expand: 1 - x² ≤ μ²x² + 2|μ|δx + δ²
    -- Rearrange: 1 - δ² ≤ (1 + μ²)x² + 2|μ|δx
    set x := ‖ψ‖ with hx_def
    have hx_nonneg : x ≥ 0 := norm_nonneg ψ
    
    have h_expanded : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) ≥ 0 := by
      have h1 : 1 - x^2 ≤ (|μ| * x + δ)^2 := h_quad
      have h2 : (|μ| * x + δ)^2 = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 := by
        rw [← sq_abs μ]; ring
      calc (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1)
          = μ^2 * x^2 + 2 * |μ| * δ * x + δ^2 + x^2 - 1 := by ring
        _ = (|μ| * x + δ)^2 - (1 - x^2) := by rw [h2]; ring
        _ ≥ 0 := by linarith [h1]
    
    -- The quadratic (1+μ²)t² + 2|μ|δt + (δ²-1) has positive root at
    -- t₊ = (√(1+μ²-δ²) - |μ|δ) / (1+μ²)
    -- and x ≥ t₊ since x > 0 and the parabola opens upward
    
    have h_denom_sq : denom^2 = 1 + μ^2 := by
      rw [hdenom]; exact Real.sq_sqrt (by linarith [sq_nonneg μ])
    
    -- Key: δ² < 1 + μ² (needed for discriminant)
    have hδ_sq_small : δ^2 < 1 + μ^2 := by
      have h1 : δ < 1 / (4 * denom) := hδ_small
      have h2 : δ^2 < 1 / (16 * denom^2) := by
        have h_lb : -(1 / (4 * denom)) < δ := by linarith
        have h1 : δ^2 < (1 / (4 * denom))^2 := sq_lt_sq' h_lb hδ_small
        calc δ^2 < (1 / (4 * denom))^2 := h1
          _ = 1 / (16 * denom^2) := by ring
      calc δ^2 < 1 / (16 * denom^2) := h2
        _ = 1 / (16 * (1 + μ^2)) := by rw [h_denom_sq]
        _ < 1 + μ^2 := by
            have : 1 + μ^2 ≥ 1 := by linarith [sq_nonneg μ]
            have : 16 * (1 + μ^2) ≥ 16 := by linarith
            have : 1 / (16 * (1 + μ^2)) ≤ 1/16 := by simp only [one_div, mul_inv_rev, inv_pos,
              Nat.ofNat_pos, mul_le_iff_le_one_left] ; (expose_names; exact inv_le_one_of_one_le₀ this_1)
            linarith
    
    -- Now we prove the lower bound via direct algebraic manipulation
    -- We show: if (1+μ²)x² + 2|μ|δx + (δ²-1) ≥ 0 and x ≥ 0, then x ≥ 1/(2*denom)
    
    by_contra h_neg
    push_neg at h_neg
    -- Assume x < 1/(2*denom)
    
    -- We'll show this leads to the quadratic being negative, contradiction
    -- The key estimate: for x < 1/(2*denom) and δ < 1/(4*denom), 
    -- the quadratic is negative
    
    have h_contra : (1 + μ^2) * x^2 + 2 * |μ| * δ * x + (δ^2 - 1) < 0 := by
      -- Upper bound each positive term, lower bound negative term
      have hx_upper : x < 1 / (2 * denom) := h_neg
      have hδ_upper : δ < 1 / (4 * denom) := hδ_small
      
      -- First term: (1+μ²)x² < (1+μ²)/(4*denom²) = (1+μ²)/(4*(1+μ²)) = 1/4
      have h_term1 : (1 + μ^2) * x^2 < 1/4 := by
        have h1 : x^2 < 1 / (4 * denom^2) := by
          have h_lb : -(1 / (2 * denom)) < x := by linarith
          have h1' : x^2 < (1 / (2 * denom))^2 := sq_lt_sq' h_lb hx_upper
          calc x^2 < (1 / (2 * denom))^2 := h1'
            _ = 1 / (4 * denom^2) := by ring
        calc (1 + μ^2) * x^2 < (1 + μ^2) * (1 / (4 * denom^2)) := by
              apply mul_lt_mul_of_pos_left h1 (by linarith [sq_nonneg μ])
          _ = (1 + μ^2) / (4 * (1 + μ^2)) := by rw [h_denom_sq]; ring
          _ = 1/4 := by field_simp
      
      -- Second term: 2|μ|δx < 2|μ| * 1/(4*denom) * 1/(2*denom) = |μ|/(4*denom²)
      have h_term2' : 2 * |μ| * δ * x < 1/4 := by
        by_cases hμ_zero : μ = 0
        · -- Case μ = 0: the term is 0 < 1/4
          simp [hμ_zero]
        · -- Case μ ≠ 0
          have hμ_pos : |μ| > 0 := abs_pos.mpr hμ_zero
          have h_mu_bound : |μ| ≤ denom := by
            rw [hdenom]
            calc |μ| = Real.sqrt (μ^2) := (Real.sqrt_sq_eq_abs μ).symm
              _ ≤ Real.sqrt (1 + μ^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
          have h1 : δ * x < 1/(4*denom) * (1/(2*denom)) := by
            apply mul_lt_mul hδ_upper (le_of_lt hx_upper) (by positivity) (by positivity)
          have h2 : 1/(4*denom) * (1/(2*denom)) = 1/(8*denom^2) := by field_simp; ring
          calc 2 * |μ| * δ * x = 2 * |μ| * (δ * x) := by ring
            _ < 2 * |μ| * (1/(8*denom^2)) := by
                rw [h2] at h1
                exact mul_lt_mul_of_pos_left h1 (by linarith : 2 * |μ| > 0)
            _ = |μ| / (4 * denom^2) := by ring
            _ = |μ| / (4 * (1 + μ^2)) := by rw [h_denom_sq]
            _ ≤ denom / (4 * (1 + μ^2)) := by
                apply div_le_div_of_nonneg_right h_mu_bound (by positivity)
            _ = Real.sqrt (1 + μ^2) / (4 * (1 + μ^2)) := by rw [hdenom]
            _ = 1 / (4 * Real.sqrt (1 + μ^2)) := by
                have h_sqrt_sq : Real.sqrt (1 + μ^2) * Real.sqrt (1 + μ^2) = 1 + μ^2 := 
                  Real.mul_self_sqrt (by linarith [sq_nonneg μ])
                rw [div_eq_div_iff (by positivity) (by positivity)]
                simp only [one_mul]
                calc Real.sqrt (1 + μ^2) * (4 * Real.sqrt (1 + μ^2)) 
                    = 4 * (Real.sqrt (1 + μ^2) * Real.sqrt (1 + μ^2)) := by ring
                  _ = 4 * (1 + μ^2) := by rw [h_sqrt_sq]
            _ ≤ 1/4 := by
                apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
                calc 4 * Real.sqrt (1 + μ^2) ≥ 4 * 1 := by
                      apply mul_le_mul_of_nonneg_left hdenom_ge_one (by norm_num)
                  _ = 4 := by ring
      
      -- Combined: first two terms < 1/4 + |μ|/(4*(1+μ²)) ≤ 1/4 + 1/4 = 1/2
      -- (using |μ| ≤ √(1+μ²) = denom, so |μ|/(1+μ²) ≤ denom/(1+μ²) = 1/denom ≤ 1)
      have h_mu_bound : |μ| ≤ denom := by
        rw [hdenom]
        calc |μ| = Real.sqrt (μ^2) := (Real.sqrt_sq_eq_abs μ).symm
          _ ≤ Real.sqrt (1 + μ^2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
      
      
      -- Third term: δ² - 1 < -1 + 1/16 < -1/2 (since δ² < 1/16 when δ < 1/4)
      have h_term3 : δ^2 - 1 < -1/2 := by
        have h1 : δ^2 < 1 / (16 * denom^2) := by 
          have h_lb : -(1 / (4 * denom)) < δ := by linarith
          have h1 : δ^2 < (1 / (4 * denom))^2 := sq_lt_sq' h_lb hδ_small
          calc δ^2 < (1 / (4 * denom))^2 := h1
            _ = 1 / (16 * denom^2) := by ring
        have h2 : 1 / (16 * denom^2) ≤ 1/16 := by
          apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
          calc 16 * denom^2 ≥ 16 * 1 := by nlinarith [hdenom_ge_one]
            _ = 16 := by ring
        linarith
      
      -- Total: < 1/4 + 1/4 + (-1/2) = 0
      linarith
    
    linarith [h_expanded, h_contra]

  /-
  Step 5: Chain the inequalities.
  -/
  calc ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖
      = δ := rfl
    _ < C' / (2 * denom) := hδ_bound
    _ ≤ C / (2 * denom) := by apply div_le_div_of_nonneg_right hC'_le_C (by positivity)
    _ ≤ C * ‖ψ‖ := by
        calc C / (2 * denom) = C * (1 / (2 * denom)) := by ring
          _ ≤ C * ‖ψ‖ := mul_le_mul_of_nonneg_left hψ_norm_lower (le_of_lt hC)


/--
**Forward approximate eigenvalue correspondence:** A → U.

### Statement

If μ is an approximate eigenvalue of A, then w = (μ - i)/(μ + i) is an
approximate eigenvalue of U.

More precisely:

    (∀C > 0, ∃ ψ ∈ D(A) with ψ ≠ 0, ‖(A - μI)ψ‖ < C‖ψ‖)
    ⟹
    (∀ε > 0, ∃ unit φ, ‖(U - wI)φ‖ < ε)

### Proof Strategy

This direction is more straightforward than the backward direction.

**Step 1:** Choose C strategically.

Given ε > 0, set C = ε / |1-w|. Find ψ with ‖(A - μI)ψ‖ < C‖ψ‖.

**Step 2:** Construct φ from ψ.

Set φ' = (A + iI)ψ. Then φ' ≠ 0 (since ‖φ'‖ ≥ ‖ψ‖ > 0).
Normalize: φ = φ'/‖φ'‖ (unit vector).

**Step 3:** Apply the intertwining identity.

By `cayley_shift_identity`:
    (U - wI)φ' = (1 - w)(A - μI)ψ

So ‖(U - wI)φ'‖ = |1-w| · ‖(A - μI)ψ‖.

**Step 4:** Normalize and bound.

    ‖(U - wI)φ‖ = ‖(U - wI)φ'‖ / ‖φ'‖
                = |1-w| · ‖(A - μI)ψ‖ / ‖φ'‖
                < |1-w| · C · ‖ψ‖ / ‖φ'‖
                ≤ |1-w| · C · ‖φ'‖ / ‖φ'‖    [since ‖φ'‖ ≥ ‖ψ‖]
                = |1-w| · C
                = ε ✓

### Why This Is Easier

The forward direction is simpler because:
- We can normalize φ' = (A + iI)ψ directly (it's in H, not D(A))
- The bound ‖φ'‖ ≥ ‖ψ‖ goes in the right direction
- No need for the lower bound axiom
-/
lemma cayley_approx_eigenvalue_forward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖) →
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) := by
  intro h_approx ε hε

  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def

  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne

  /-
  Step 1: Choose C = ε / |1-w|.
  -/
  obtain ⟨ψ, hψ_mem, hψ_norm_ne, h_Aμψ_bound⟩ := h_approx (ε / ‖(1 : ℂ) - w‖) (by positivity)

  have hψ_ne : ψ ≠ 0 := norm_ne_zero_iff.mp hψ_norm_ne
  have hψ_norm_pos : ‖ψ‖ > 0 := norm_pos_iff.mpr hψ_ne

  /-
  Step 2: Construct φ from ψ.

  φ' = (A + iI)ψ, then normalize to get unit φ.
  -/
  set φ' := gen.op ⟨ψ, hψ_mem⟩ + I • ψ with hφ'_def

  -- φ' ≠ 0 since ‖φ'‖² = ‖Aψ‖² + ‖ψ‖² ≥ ‖ψ‖² > 0
  have hφ'_norm_pos : ‖φ'‖ > 0 := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    have h_ge : ‖φ'‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ'‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ 0 + ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]
        _ = ‖ψ‖^2 := by ring
    nlinarith [norm_nonneg φ', sq_nonneg ‖φ'‖, sq_nonneg ‖ψ‖]

  have hφ'_ne : φ' ≠ 0 := norm_pos_iff.mp hφ'_norm_pos

  -- ‖φ'‖ ≥ ‖ψ‖ (key bound for the forward direction)
  have hφ'_norm_ge_ψ : ‖φ'‖ ≥ ‖ψ‖ := by
    have h_sq := self_adjoint_norm_sq_add gen hsa ψ hψ_mem
    have h_ge : ‖φ'‖^2 ≥ ‖ψ‖^2 := by
      calc ‖φ'‖^2 = ‖gen.op ⟨ψ, hψ_mem⟩‖^2 + ‖ψ‖^2 := h_sq
        _ ≥ ‖ψ‖^2 := by linarith [sq_nonneg ‖gen.op ⟨ψ, hψ_mem⟩‖]
    nlinarith [norm_nonneg φ', norm_nonneg ψ, sq_nonneg (‖φ'‖ - ‖ψ‖)]

  -- Normalize: φ = φ' / ‖φ'‖
  set φ := ‖φ'‖⁻¹ • φ' with hφ_def

  use φ
  constructor
  · -- ‖φ‖ = 1
    rw [hφ_def, norm_smul, norm_inv, norm_norm]
    field_simp [ne_of_gt hφ'_norm_pos]

  /-
  Step 3: Apply the intertwining identity.

  (U - wI)φ' = (1 - w)(A - μI)ψ
  -/
  have h_key := cayley_shift_identity gen hsa μ hμ_ne ψ hψ_mem
  simp only at h_key

  have h_Uwφ' : (U - w • ContinuousLinearMap.id ℂ H) φ' =
      ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ) := h_key

  -- ‖(U - wI)φ'‖ = |1-w| · ‖(A - μI)ψ‖
  have h_norm_Uwφ' : ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ =
      ‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖ := by
    rw [h_Uwφ', norm_smul]

  /-
  Step 4: Normalize and chain the bounds.

  ‖(U - wI)φ‖ = ‖(U - wI)φ'‖ / ‖φ'‖
              < |1-w| · C · ‖ψ‖ / ‖φ'‖
              ≤ |1-w| · C    [since ‖φ'‖ ≥ ‖ψ‖]
              = ε
  -/
  calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
      = ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ'‖⁻¹ • φ')‖ := by rw [hφ_def]
    _ = ‖‖φ'‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        simp only [ContinuousLinearMap.map_smul_of_tower,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
          ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq]
    _ = ‖φ'‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        rw [norm_smul, norm_inv, norm_norm]
    _ = ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖gen.op ⟨ψ, hψ_mem⟩ - (↑μ : ℂ) • ψ‖) := by rw [h_norm_Uwφ']
    _ < ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * (ε / ‖(1 : ℂ) - w‖ * ‖ψ‖)) := by
        apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hφ'_norm_pos)
        apply mul_lt_mul_of_pos_left h_Aμψ_bound h_one_sub_w_norm_pos
    _ = ‖φ'‖⁻¹ * (ε * ‖ψ‖) := by field_simp
    _ ≤ ‖φ'‖⁻¹ * (ε * ‖φ'‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        apply mul_le_mul_of_nonneg_left hφ'_norm_ge_ψ (le_of_lt hε)
    _ = ε := by field_simp [ne_of_gt hφ'_norm_pos]


/-!
## The Main Theorems

This section contains the culminating results of the Cayley transform theory:

1. **Spectral Correspondence:** The spectrum of A corresponds bijectively to
   the spectrum of U via the Möbius map.

2. **Domain Characterization:** The domain of A equals the range of (I - U).

These theorems complete von Neumann's program: the Cayley transform establishes
a perfect dictionary between unbounded self-adjoint operators and unitary
operators missing the eigenvalue 1.

### Historical Significance

Von Neumann proved these results in 1929-1932 to put quantum mechanics on
rigorous mathematical foundations. The spectral correspondence allows:
- Transfer of the spectral theorem from bounded to unbounded operators
- Rigorous treatment of the Schrödinger equation
- Mathematical foundation for quantum observables

### The Big Picture
```
    Self-adjoint A on D(A)          Unitary U on H
           ↓                              ↓
    σ(A) ⊆ ℝ          ←――Möbius――→      σ(U) ⊆ S¹
           ↓                              ↓
    A - μI bounded below    ⟺     U - wI invertible
```

where w = (μ - i)/(μ + i).
-/

/--
**The Spectral Correspondence Theorem.**

### Statement

For a self-adjoint operator A with Cayley transform U, and real μ with
corresponding w = (μ - i)/(μ + i):

    A - μI is bounded below  ⟺  U - wI is invertible

### Interpretation

**"Bounded below"** means: ∃C > 0, ∀ψ ∈ D(A), ‖(A - μI)ψ‖ ≥ C‖ψ‖

This is equivalent to:
- μ is not an approximate eigenvalue of A
- μ is in the resolvent set of A (when combined with range conditions)

**"Invertible"** means: U - wI has a bounded inverse (IsUnit)

This is equivalent to:
- w is not in the spectrum of U
- w is not an approximate eigenvalue of U (since U is normal)

### The Correspondence

Combining with the Möbius map w = (μ - i)/(μ + i):

    μ ∈ ρ(A)  ⟺  w ∈ ρ(U)    (resolvent sets)
    μ ∈ σ(A)  ⟺  w ∈ σ(U)    (spectra)

Since A is self-adjoint, σ(A) ⊆ ℝ.
Since U is unitary, σ(U) ⊆ S¹.
The Möbius map is a bijection ℝ → S¹ \ {1}.

Therefore: **σ(U) ⊆ S¹ \ {1}** (when ker(A) = {0}, so -1 ∉ σ(U)).

### Proof Structure

**Forward (⟹):** A - μI bounded below implies U - wI invertible.

Proof by contrapositive:
1. Suppose U - wI is NOT invertible
2. Since U is unitary (hence normal), U - wI not invertible implies
   w is an approximate eigenvalue of U (`unitary_not_isUnit_approx_eigenvalue`)
3. By `cayley_approx_eigenvalue_backward`, μ is an approximate eigenvalue of A
4. This contradicts A - μI bounded below

**Backward (⟸):** U - wI invertible implies A - μI bounded below.

1. U - wI invertible implies U - wI bounded below (`isUnit_bounded_below`)
2. By `cayley_shift_bounded_below_backward`, A - μI is bounded below

### Significance

This is the **fundamental theorem** connecting the spectral theory of
unbounded self-adjoint operators to bounded unitary operators. It allows:
- Transfer of spectral decomposition: E_A(B) ↔ E_U(μ(B))
- Definition of f(A) via f ∘ μ⁻¹ applied to U
- Proof that self-adjoint operators generate unitary groups
-/
theorem cayley_spectrum_correspondence {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ) :
    (∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) ↔
    IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) := by
  set U := cayleyTransform gen hsa with hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def

  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ

  constructor

  /-
  ═══════════════════════════════════════════════════════════════════════════
  FORWARD: A - μI bounded below ⟹ U - wI invertible
  ═══════════════════════════════════════════════════════════════════════════

  We prove the contrapositive: ¬IsUnit(U - wI) ⟹ ¬(A - μI bounded below)

  The chain of implications:
  1. U - wI not invertible
  2. ⟹ w is an approximate eigenvalue of U (by normality)
  3. ⟹ μ is an approximate eigenvalue of A (by spectral correspondence)
  4. ⟹ A - μI is NOT bounded below (definition of approx eigenvalue)
  -/
  · intro ⟨C, hC_pos, hC_bound⟩

    by_contra h_not_unit

    -- Step 1→2: U - wI not invertible ⟹ w is approx eigenvalue of U
    -- (This uses that U is unitary, hence normal)
    have h_approx_U := unitary_not_isUnit_approx_eigenvalue
                         (cayleyTransform_unitary gen hsa) w h_not_unit

    -- Step 2→3: w approx eigenvalue of U ⟹ μ approx eigenvalue of A
    have h_approx_A := cayley_approx_eigenvalue_backward gen hsa μ hμ_ne h_approx_U

    -- Step 3→4: Get contradiction with bounded below
    obtain ⟨ψ, hψ_mem, hψ_norm_ne, h_small⟩ := h_approx_A C hC_pos
    have hψ_ne : ψ ≠ 0 := norm_ne_zero_iff.mp hψ_norm_ne
    have hψ_norm_pos : ‖ψ‖ > 0 := norm_pos_iff.mpr hψ_ne

    have h_ge := hC_bound ψ hψ_mem
    -- h_ge : ‖(A - μI)ψ‖ ≥ C · ‖ψ‖
    -- h_small : ‖(A - μI)ψ‖ < C · ‖ψ‖
    -- Contradiction!
    linarith

  /-
  ═══════════════════════════════════════════════════════════════════════════
  BACKWARD: U - wI invertible ⟹ A - μI bounded below
  ═══════════════════════════════════════════════════════════════════════════

  This direction is more direct:
  1. U - wI invertible ⟹ U - wI bounded below (general fact)
  2. U - wI bounded below ⟹ A - μI bounded below (by intertwining)
  -/
  · intro hU
    -- Step 1: Invertible ⟹ bounded below
    obtain ⟨c, hc_pos, hc_bound⟩ := isUnit_bounded_below hU
    -- Step 2: Transfer the bound from U to A
    exact cayley_shift_bounded_below_backward gen hsa μ hμ_ne c hc_pos hc_bound

/--
**Domain Characterization:** D(A) = Range(I - U).

### Statement

The domain of the generator A equals the range of (I - U), where U is the
Cayley transform of A.

### Significance

This characterizes the (typically complicated) domain of an unbounded
self-adjoint operator in terms of a simple expression involving the
bounded unitary operator U.

**Consequences:**
- D(A) is a proper dense subspace of H (since I - U is not surjective
  unless -1 ∉ σ(U), which corresponds to 0 ∉ σ(A))
- The "size" of D(A) is controlled by how close U is to having -1 as
  an eigenvalue
- Provides a practical way to verify ψ ∈ D(A): check if ψ ∈ Range(I - U)

### Proof Structure

**Forward (D(A) ⊆ Range(I - U)):**

For ψ ∈ D(A), set φ = (A + iI)ψ. Then:
- Uφ = (A - iI)ψ (by Cayley transform)
- (I - U)φ = φ - Uφ = (A + iI)ψ - (A - iI)ψ = 2iψ
- Therefore ψ = (2i)⁻¹(I - U)φ ∈ Range(I - U)

**Backward (Range(I - U) ⊆ D(A)):**

For ψ = (I - U)χ, write χ = (A + iI)η via the resolvent (η ∈ D(A)). Then:
- Uχ = (A - iI)η (by Cayley transform)
- (I - U)χ = χ - Uχ = (A + iI)η - (A - iI)η = 2iη
- Therefore ψ = 2iη, and since η ∈ D(A) and D(A) is a subspace,
  ψ = 2iη ∈ D(A)

### The Formulas

The proof reveals explicit formulas:
- **From D(A) to Range(I - U):** ψ ↦ (2i)⁻¹(I - U)(A + iI)ψ
- **From Range(I - U) to D(A):** (I - U)χ ↦ (2i)⁻¹(I - U)χ = R_{-i}(χ)

These are consistent: (I - U) = 2i · R_{-i} on Range(A + iI) = H.

### Connection to Inverse Cayley

This theorem is closely related to the inverse Cayley transform:
    A = i(I + U)(I - U)⁻¹

The domain D(A) = Range(I - U) is exactly where (I - U)⁻¹ makes sense.
On this domain, A acts as i(I + U)(I - U)⁻¹.

### Physical Interpretation

In quantum mechanics:
- D(A) is the set of states where the observable A is "well-defined"
- States outside D(A) have "infinite uncertainty" in the observable A
- The characterization D(A) = Range(I - U) connects this to the
  unitary evolution generated by A
-/
theorem generator_domain_eq_range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (gen.domain : Set H) = LinearMap.range (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) := by
  set U := cayleyTransform gen hsa with hU_def
  ext ψ
  constructor

  /-
  ─────────────────────────────────────────────────────────────────────────
  Forward: D(A) ⊆ Range(I - U)
  ─────────────────────────────────────────────────────────────────────────

  For ψ ∈ D(A):
  1. Let φ = (A + iI)ψ
  2. Then Uφ = (A - iI)ψ
  3. So (I - U)φ = 2iψ
  4. Therefore ψ = (2i)⁻¹(I - U)φ ∈ Range(I - U)
  -/
  · intro hψ
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ

    -- Compute Uφ = (A - iI)ψ
    have h_Uφ : U φ = gen.op ⟨ψ, hψ⟩ - I • ψ := by
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa ψ hψ
      rw [h_res]
      module

    -- (I - U)φ = φ - Uφ = (A+iI)ψ - (A-iI)ψ = 2iψ
    have h_diff : (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, h_Uφ]
      simp only [φ]
      module

    -- So ψ = (2i)⁻¹(I - U)φ ∈ Range(I - U)
    rw [@LinearMap.coe_range]
    use (2 * I)⁻¹ • φ
    simp only [map_smul, h_diff, smul_smul]
    have h_ne : (2 : ℂ) * I ≠ 0 := by simp
    field_simp [h_ne]
    module

  /-
  ─────────────────────────────────────────────────────────────────────────
  Backward: Range(I - U) ⊆ D(A)
  ─────────────────────────────────────────────────────────────────────────

  For ψ = (I - U)χ:
  1. Write χ = (A + iI)η for some η ∈ D(A) (via resolvent)
  2. Then Uχ = (A - iI)η
  3. So (I - U)χ = 2iη
  4. Therefore ψ = 2iη ∈ D(A) (since D(A) is a subspace)
  -/
  · intro hψ
    rw [LinearMap.coe_range] at hψ
    obtain ⟨χ, hχ⟩ := hψ
    -- ψ = (I - U)χ

    -- Get η from resolvent: χ = (A + iI)η
    set η := Resolvent.resolvent_at_neg_i gen hsa χ with hη_def
    have hη_mem : η ∈ gen.domain := Resolvent.resolvent_solution_mem_plus gen hsa χ
    have hχ_eq : gen.op ⟨η, hη_mem⟩ + I • η = χ := Resolvent.resolvent_solution_eq_plus gen hsa χ

    -- Compute Uχ = (A - iI)η
    have h_Uχ : U χ = gen.op ⟨η, hη_mem⟩ - I • η := by
      rw [← hχ_eq]
      simp only [U, cayleyTransform, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      have h_res : Resolvent.resolvent_at_neg_i gen hsa (gen.op ⟨η, hη_mem⟩ + I • η) = η :=
        Resolvent.resolvent_at_neg_i_left_inverse gen hsa η hη_mem
      rw [h_res]
      module

    -- (I - U)χ = χ - Uχ = 2iη
    have h_diff : (ContinuousLinearMap.id ℂ H - U) χ = (2 * I) • η := by
      calc (ContinuousLinearMap.id ℂ H - U) χ
          = χ - U χ := by simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        _ = χ - (gen.op ⟨η, hη_mem⟩ - I • η) := by rw [h_Uχ]
        _ = (gen.op ⟨η, hη_mem⟩ + I • η) - (gen.op ⟨η, hη_mem⟩ - I • η) := by rw [← hχ_eq]
        _ = (2 * I) • η := by module

    -- ψ = (I - U)χ = 2iη ∈ D(A)
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
               Pi.sub_apply, id_eq] at hχ
    rw [← hχ]
    subst hχ
    simp_all only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
                   Pi.sub_apply, id_eq, SetLike.mem_coe, U, η]
    -- Need to show (2i) • η ∈ D(A)
    apply SMulMemClass.smul_mem
    exact hη_mem





/-!
================================================================================
SPECTRAL CONNECTION: Bridge to Functional Calculus
================================================================================

Having established the complete Cayley transform theory, we now connect it
to the spectral theorem and functional calculus.

## The Goal

The ultimate purpose of the Cayley transform is to **transfer** spectral theory:
```
    Spectral theorem for U          Spectral theorem for A
    (bounded, well-understood)  →   (unbounded, what we want)
```

## The Mechanism

The spectral theorem says every normal operator has a **spectral measure**:
- For unitary U: a projection-valued measure E_U on S¹
- For self-adjoint A: a projection-valued measure E_A on ℝ

The Cayley transform induces a correspondence between these measures
via the Möbius map μ ↦ w = (μ - i)/(μ + i).

## How It Works

For a Borel set B ⊆ ℝ, define its **Cayley image**:

    cayleyImage(B) = { (μ - i)/(μ + i) : μ ∈ B } ⊆ S¹

Then the spectral measures are related by:

    E_A(B) = E_U(cayleyImage(B))

This allows us to:
1. Start with the spectral measure E_U of the unitary U
2. Pull it back via the inverse Möbius map to get E_A
3. Define f(A) = ∫ f dE_A for bounded Borel functions f on ℝ

## What This Section Provides

- `cayleyImage`: The Möbius image of a Borel set
- `spectralMeasure_from_unitary`: Transfer E_U to E_A
- `SpectralMeasuresCompatible`: The compatibility condition
- `exists_compatible_spectral_measures`: Existence (axiom)
- `spectralMeasure_cayley_correspondence`: The main correspondence

## Connection to Functional Calculus

With compatible spectral measures, the functional calculus transfers:

    f(A) = ∫_ℝ f(μ) dE_A(μ) = ∫_{S¹} (f ∘ μ⁻¹)(w) dE_U(w)

This completes the program: **any bounded Borel function of A can be
computed via the unitary functional calculus of U**.
-/

/--
**Cayley image of a Borel set.**

### Definition

For a set B ⊆ ℝ, its Cayley image is the set of Möbius images:

    cayleyImage(B) = { w ∈ ℂ : w = (μ - i)/(μ + i) for some μ ∈ B }

### Properties

- cayleyImage(ℝ) = S¹ \ {1}
- cayleyImage({0}) = {-1}
- cayleyImage([a, b]) is an arc on S¹
- cayleyImage(∅) = ∅
- cayleyImage preserves countable unions and intersections

### Measure-Theoretic Role

If B is a Borel set in ℝ, then cayleyImage(B) is a Borel set in ℂ
(since the Möbius map is a homeomorphism ℝ → S¹ \ {1}).

This allows us to evaluate spectral measures: E_U(cayleyImage(B)).
-/
def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

/--
**Transfer spectral measure from U to A.**

### Definition

Given a spectral measure E_U for the unitary U, define the corresponding
measure for A by:

    E_A(B) := E_U(cayleyImage(B))

### Intuition

The spectral projection E_A(B) projects onto the eigenspaces of A with
eigenvalues in B. Under the Cayley correspondence:
- Eigenvalue μ of A ↔ Eigenvalue w = (μ-i)/(μ+i) of U
- Eigenspace for μ ↔ Eigenspace for w

So E_A(B) should equal E_U(cayleyImage(B)).

### Use Case

This provides a concrete construction of E_A from E_U, which is useful
because:
- E_U is easier to construct (U is bounded)
- E_U satisfies nice properties (projection-valued measure on S¹)
- E_A inherits these properties via pullback
-/
noncomputable def spectralMeasure_from_unitary
    (E_U : Set ℂ → (H →L[ℂ] H)) : Set ℝ → (H →L[ℂ] H) :=
  fun B => E_U (cayleyImage B)

/--
**Compatibility of spectral measures.**

### Definition

Spectral measures E_A (for A) and E_U (for U) are **compatible** if:

    E_A(B) = E_U(cayleyImage(B))  for all Borel sets B ⊆ ℝ

### Significance

This is the precise condition needed to transfer the functional calculus.
When E_A and E_U are compatible:

    f(A) = ∫_ℝ f dE_A = ∫_{S¹} (f ∘ μ⁻¹) dE_U = (f ∘ μ⁻¹)(U)

So computing f(A) reduces to computing g(U) where g = f ∘ μ⁻¹.

### What Compatibility Encodes

1. **Spectral correspondence:** Eigenspaces match under Möbius
2. **Measure correspondence:** E_A is the pullback of E_U
3. **Functional calculus correspondence:** f(A) = (f ∘ μ⁻¹)(U)

### Relation to Our Theorems

The compatibility follows from:
- `cayley_eigenvalue_correspondence`: Point spectrum matches
- `cayley_spectrum_correspondence`: Full spectrum matches
- Stone's theorem: Spectral measures exist and are unique
-/
def SpectralMeasuresCompatible {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ B : Set ℝ, E_A B = E_U (cayleyImage B)

/--
**Existence of compatible spectral measures.**

### Statement (Axiom)

For any self-adjoint generator A with Cayley transform U, there exist
spectral measures E_A and E_U that are compatible.

### Why an Axiom?

The full proof requires:
1. **Spectral theorem for unitary operators:** E_U exists
2. **Pullback construction:** E_A := E_U ∘ cayleyImage
3. **Verification:** E_A is a projection-valued measure
4. **Integration theory:** The functional calculus works

These are substantial results that would require significant additional
formalization (measure theory, integration, projection-valued measures).

### What Would a Full Proof Involve?

1. Define projection-valued measures (PVMs)
2. Prove the spectral theorem: every unitary has a PVM on S¹
3. Show cayleyImage preserves Borel structure
4. Prove E_U ∘ cayleyImage is a PVM on ℝ
5. Show this PVM corresponds to A via the spectral theorem for
   unbounded self-adjoint operators

### Justification

This axiom is mathematically sound—it's a well-known theorem in
functional analysis. The Cayley transform machinery we've built
provides all the spectral correspondence needed; what remains is
"just" measure theory.
-/
axiom exists_compatible_spectral_measures {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ∃ (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)),
      SpectralMeasuresCompatible gen hsa E_A E_U

/--
**The spectral measure correspondence theorem.**

### Statement

Given compatible spectral measures E_A and E_U, for any Borel set B ⊆ ℝ:

    E_A(B) = E_U(cayleyImage(B))

### Note

This is immediate from the definition of compatibility—it's provided as
a theorem for convenient application.

### Application

To compute E_A(B):
1. Compute cayleyImage(B) = { (μ-i)/(μ+i) : μ ∈ B }
2. Evaluate E_U(cayleyImage(B))

This transfers spectral computations from the unbounded A to the bounded U.

### Example

For B = [0, ∞) (positive spectrum):
- cayleyImage([0, ∞)) = lower semicircle of S¹ (from -1 to 1, going through -i)
- E_A([0, ∞)) = E_U(lower semicircle) = projection onto "positive energy" states
-/
theorem spectralMeasure_cayley_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H))
    (hcompat : SpectralMeasuresCompatible gen hsa E_A E_U)
    (B : Set ℝ) :
    E_A B = E_U (cayleyImage B) := hcompat B


/-
┌─────────────────────────────────────────────────────────┐
│                 THE COMPLETE PICTURE                    │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   Self-adjoint A ←──Cayley──→ Unitary U                 │
│         ↓                           ↓                   │
│   Spectrum σ(A) ⊆ ℝ ←─Möbius─→ Spectrum σ(U) ⊆ S¹       │
│         ↓                           ↓                   │
│   Spectral measure E_A ←─────→ Spectral measure E_U     │
│         ↓                           ↓                   │
│   f(A) = ∫ f dE_A    ←─────→    g(U) = ∫ g dE_U         │
│                                                         │
│   where g = f ∘ (inverse Möbius)                        │
│                                                         │
└─────────────────────────────────────────────────────────┘
-/

end StonesTheorem.Cayley
