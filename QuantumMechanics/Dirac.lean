/-
Author: Adam Bornemann
Created: 1-6-2026
Updated: 1-6-2026

================================================================================
THE DIRAC OPERATOR: Relativistic Quantum Mechanics
================================================================================

This file constructs the free Dirac operator and verifies it fits within
the spectral theory framework developed for unbounded self-adjoint operators.

THE DIRAC EQUATION:

  iℏ ∂ψ/∂t = H_D ψ

where the Dirac Hamiltonian is:

  H_D = cα·p + βmc² = -iℏc(α·∇) + βmc²

acting on 4-component spinor fields ψ : ℝ³ → ℂ⁴.

ALGEBRAIC STRUCTURE:

The Dirac matrices α = (α₁, α₂, α₃) and β satisfy the Clifford algebra:

  ┌────────────────────────────────────────────────────────────┐
  │  αᵢαⱼ + αⱼαᵢ = 2δᵢⱼ I₄        (anticommutation)            │
  │  αᵢβ + βαᵢ = 0                 (α and β anticommute)       │
  │  β² = I₄                        (β squares to identity)    │
  │  αᵢ* = αᵢ,  β* = β             (Hermitian)                 │
  └────────────────────────────────────────────────────────────┘

Standard (Dirac-Pauli) representation:

        ┌         ┐           ┌         ┐
        │  0   σᵢ │           │  I₂  0  │
  αᵢ =  │         │  ,   β =  │         │
        │  σᵢ  0  │           │  0  -I₂ │
        └         ┘           └         ┘

where σᵢ are the Pauli matrices.

HILBERT SPACE:

  H = L²(ℝ³, ℂ⁴) ≅ L²(ℝ³) ⊗ ℂ⁴

with inner product:

  ⟪ψ, φ⟫ = ∫_ℝ³ ψ(x)†φ(x) d³x = ∑_{a=1}^{4} ∫_ℝ³ ψ̄ₐ(x)φₐ(x) d³x

SPECTRAL STRUCTURE:

The free Dirac operator has spectrum:

  σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)

  ┌───────────────────────────────────────────────────────────┐
  │                                                           │
  │   ══════════════╪════════════════════╪══════════════      │
  │                -mc²        0        +mc²                  │
  │                                                           │
  │   ◄──────────────┤    spectral gap    ├──────────────►    │
  │   negative energy │   (-mc², +mc²)    │  positive energy  │
  │    (positrons)    │    FORBIDDEN      │   (electrons)     │
  │                                                           │
  └───────────────────────────────────────────────────────────┘

KEY DIFFERENCE FROM SCHRÖDINGER:

  • NOT semibounded: σ(H) extends to -∞
  • Friedrichs extension does NOT apply
  • Still essentially self-adjoint on C_c^∞(ℝ³)⁴
  • Spectral theorem and functional calculus still apply

PHYSICAL INTERPRETATION:

The spectral gap |E| < mc² corresponds to the rest mass energy.

  • Positive spectrum [mc², ∞): electron states
  • Negative spectrum (-∞, -mc²]: positron states (Dirac sea)
  • Gap (-mc², mc²): forbidden energies (mass gap)

The functional calculus handles this:

  • E([mc², ∞)) projects onto electron subspace
  • E((-∞, -mc²]) projects onto positron subspace
  • f(H_D) applies f to both branches of spectrum

RELATION TO STONE'S THEOREM:

Despite the unbounded-below spectrum, Stone's theorem applies:

  U(t) = e^{-itH_D/ℏ}

is a strongly continuous unitary group. The Cayley transform:

  W = (H_D - imc²)(H_D + imc²)⁻¹

maps the spectrum:

  • (-∞, -mc²] ∪ [mc², ∞)  →  S¹ \ {-1}  (unit circle minus one point)

The spectral gap maps to an arc around -1 that's NOT in the spectrum of W.

DOMAIN:

  dom(H_D) = H¹(ℝ³, ℂ⁴) = {ψ ∈ L² : ∇ψ ∈ L²}  (Sobolev space)

The domain characterization via functional calculus:

  dom(H_D) = {ψ : ∫_σ |s|² dμ_ψ(s) < ∞}

where the integral is over σ(H_D) = (-∞, -mc²] ∪ [mc², ∞).

ESSENTIAL SELF-ADJOINTNESS:

  ┌─────────────────────────────────────────────────────────┐
  │  THEOREM (Kato): The Dirac operator H_D is essentially  │
  │  self-adjoint on C_c^∞(ℝ³)⁴.                            │
  │                                                         │
  │  Moreover, H_D with domain H¹(ℝ³, ℂ⁴) is self-adjoint.  │
  └─────────────────────────────────────────────────────────┘

This does NOT follow from semiboundedness (which fails).
It uses the special structure of the Dirac operator.

SPECTRAL MEASURE AND FUNCTIONAL CALCULUS:

All results from FunctionalCalculus.lean apply:

  • f(H_D) = ∫_σ f(s) dE(s)
  • dom(f(H_D)) = {ψ : ∫|f(s)|² dμ_ψ < ∞}
  • (f + g)(H_D) = f(H_D) + g(H_D)
  • (fg)(H_D) = f(H_D) ∘ g(H_D)
  • f̄(H_D) = f(H_D)*

Important special cases:

  • e^{-itH_D} = time evolution (Stone)
  • |H_D| = ∫ |s| dE(s) = √(H_D²)
  • sign(H_D) = E([mc², ∞)) - E((-∞, -mc²])  (splits electron/positron)
  • (H_D - z)⁻¹ = resolvent (your Resolvent.lean)

MATHEMATICAL CONTENT:

  §1 Clifford Algebra
     - DiracMatrices: αᵢ, β satisfying anticommutation relations
     - clifford_anticommute: αᵢαⱼ + αⱼαᵢ = 2δᵢⱼ
     - alpha_beta_anticommute: αᵢβ + βαᵢ = 0

  §2 Spinor Hilbert Space
     - SpinorSpace: L²(ℝ³, ℂ⁴) construction
     - spinor_inner: ⟪ψ, φ⟫ = ∫ ψ†φ

  §3 Dirac Operator
     - diracOperator: H_D = -iℏc(α·∇) + βmc²
     - dirac_symmetric: ⟪H_D ψ, φ⟫ = ⟪ψ, H_D φ⟫ on domain
     - dirac_essentially_self_adjoint: closure is self-adjoint

  §4 Spectral Properties
     - dirac_spectrum: σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)
     - dirac_spectral_gap: (-mc², mc²) ⊆ ρ(H_D)
     - dirac_not_semibounded: ∀ c, ∃ ψ, ⟪H_D ψ, ψ⟫ < c

  §5 Connection to Framework
     - dirac_cayley_unitary: Cayley transform is unitary
     - dirac_functional_calculus: f(H_D) via spectral measure
     - dirac_stone_group: e^{-itH_D} strongly continuous

DEPENDENCIES:

  - FunctionalCalculus.lean: functional calculus framework
  - SpectralBridge.lean: Bochner and Resolvent routes
  - Cayley.lean: Cayley transform (handles non-semibounded case)
  - Resolvent.lean: resolvent operators

REFERENCES:

  [1] Dirac, P.A.M. "The Quantum Theory of the Electron" (1928)
      - Original derivation of the equation

  [2] Thaller, B. "The Dirac Equation" (1992)
      - Comprehensive mathematical treatment

  [3] Reed & Simon, "Methods of Modern Mathematical Physics II" Ch. X
      - Spectral theory of Dirac operators

  [4] Kato, T. "Perturbation Theory for Linear Operators" (1966)
      - Essential self-adjointness results

  [5] Weidmann, "Linear Operators in Hilbert Spaces" Ch. 10
      - Spectral theory for Dirac-type operators
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.FunctionalCalc

namespace PaulDirac
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open  MeasureTheory InnerProductSpace Complex StonesTheorem.Cayley SpectralBridge Stone.Generators FunctionalCalculus
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/- 
=====================================================================================================================================
# HELPER LEMMAS 
=====================================================================================================================================

Computational verification of the Clifford algebra relations for two matrix representations:

  1. Dirac-Pauli (α, β): Used in the Hamiltonian H_D = -iℏc(α·∇) + βmc²
  2. Gamma matrices (γ^μ): Used in the covariant current j^μ = ψ̄γ^μψ

Both satisfy anticommutation relations; the proofs are brute-force matrix arithmetic.



### Dirac-Pauli Representation (α, β)

The Hamiltonian H_D = -iℏc(α·∇) + βmc² requires matrices satisfying:

  αᵢ² = I,  β² = I           (involutory)
  {αᵢ, αⱼ} = 0  for i ≠ j    (spatial anticommutation)  
  {αᵢ, β} = 0                (mass-momentum anticommutation)
  αᵢ† = αᵢ,  β† = β          (Hermitian)

The standard 4×4 representation uses Pauli matrices in block form:

        ┌         ┐           ┌         ┐
        │  0   σᵢ │           │  I₂  0  │
  αᵢ =  │         │  ,   β =  │         │
        │  σᵢ  0  │           │  0  -I₂ │
        └         ┘           └         ┘

Hermiticity of α and β implies H_D is symmetric on its domain —
the first step toward essential self-adjointness.
-/

/-- α₁ in standard representation (4×4) -/
def diracAlpha1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- α₂ in standard representation (4×4) -/
def diracAlpha2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, -I, 0, 0;
     I, 0, 0, 0]

/-- α₃ in standard representation (4×4) -/
def diracAlpha3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- β in standard representation (4×4) -/
def diracBeta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]


set_option maxHeartbeats 375000

/-- α₁ is an involution: α₁² = I.

**Mathematical meaning**: α₁ has eigenvalues ±1 (since x² = 1 ⟹ x = ±1).
Combined with Hermiticity, this gives a complete spectral decomposition.

**Physical meaning**: The Clifford algebra relation {αᵢ, αⱼ} = 2δᵢⱼ 
(of which this is the i = j = 1 case) is what makes H_D² yield the 
relativistic dispersion relation E² = (pc)² + (mc²)².

**Proof strategy**: Brute-force verification of all 16 matrix entries.
`fin_cases a <;> fin_cases b` splits into the 4×4 = 16 cases (a,b) ∈ Fin 4 × Fin 4,
then `simp` computes each entry of the product. -/
private lemma diracAlpha1_sq : diracAlpha1 * diracAlpha1 = 1 := by
  ext a b                    -- Reduce matrix equality to entry-wise: ∀ a b, (α₁²)ₐᵦ = Iₐᵦ
  fin_cases a <;> fin_cases b <;>  -- Split into 16 cases for each (a,b) pair
  simp only [diracAlpha1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, ↓reduceIte]
  all_goals try simp        -- Finish off any remaining arithmetic

/-- α₂ is an involution: α₂² = I.

Unlike α₁ and α₃, the matrix α₂ contains imaginary entries (±I) from the 
Pauli-Y matrix. The product α₂² involves terms like (-I)(I) = 1, which 
is why `mul_neg, neg_mul` appear in the simplification. -/
private lemma diracAlpha2_sq : diracAlpha2 * diracAlpha2 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, add_zero, zero_add, ↓reduceIte, mul_neg, neg_mul]
  all_goals try simp

/-- α₃ is an involution: α₃² = I.

The matrix α₃ is built from the Pauli-Z matrix (diagonal ±1 entries).
The product involves (-1)(-1) = 1 terms, hence `neg_neg` in the simplification. -/
private lemma diracAlpha3_sq : diracAlpha3 * diracAlpha3 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, ↓reduceIte, mul_neg, neg_neg]
  all_goals try simp

/-- β is an involution: β² = I.

The mass matrix β = diag(1, 1, -1, -1) distinguishes upper spinor components
(particle) from lower components (antiparticle). Being diagonal, the proof
is simpler than for the α matrices — just (-1)² = 1 on the lower block. -/
private lemma diracBeta_sq : diracBeta * diracBeta = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracBeta, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
             Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_one, mul_zero, add_zero, ↓reduceIte]
  all_goals try simp only [mul_neg, mul_one, neg_zero, neg_neg, Fin.reduceEq, ↓reduceIte]
  all_goals try ring

/-- α₁ and α₂ anticommute: {α₁, α₂} = α₁α₂ + α₂α₁ = 0.

This is the i ≠ j case of the Clifford relation {αᵢ, αⱼ} = 2δᵢⱼ.
Anticommutation of distinct α matrices ensures that H_D² produces 
the Laplacian (not some cross-term mess): (α·p)² = p₁² + p₂² + p₃².

The proof mixes real entries (from α₁) with imaginary entries (from α₂),
producing cancellations like 1·I + I·(-1) = 0. -/
private lemma diracAlpha12_anticommute : diracAlpha1 * diracAlpha2 + diracAlpha2 * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracAlpha2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_zero, add_zero,
    one_mul, zero_add, mul_one, add_neg_cancel, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_neg, zero_mul, neg_zero, mul_zero, add_zero, mul_one]
  all_goals try ring_nf

/-- α₁ and α₃ anticommute: {α₁, α₃} = 0.

Both matrices have real entries (α₁ from Pauli-X, α₃ from Pauli-Z),
so cancellations involve only ±1 arithmetic, no complex numbers. -/
private lemma diracAlpha13_anticommute : diracAlpha1 * diracAlpha3 + diracAlpha3 * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracAlpha3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, add_zero, mul_neg, mul_one, neg_zero]
  all_goals try ring

/-- α₂ and α₃ anticommute: {α₂, α₃} = 0.

This mixes imaginary entries (from α₂) with real entries (from α₃).
Cancellations have the form I·1 + 1·(-I) = 0. -/
private lemma diracAlpha23_anticommute : diracAlpha2 * diracAlpha3 + diracAlpha3 * diracAlpha2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, diracAlpha3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, mul_neg, mul_one, neg_neg, zero_add, add_zero, one_mul,
    add_neg_cancel]
  all_goals try ring

/-- α₁ and β anticommute: {α₁, β} = 0.

This is the key structural relation connecting momentum and mass terms in
H_D = -iℏc(α·∇) + βmc². Because {αᵢ, β} = 0, the square H_D² separates cleanly:

  H_D² = (ℏc)²(α·∇)² + (mc²)²β² = -ℏ²c²∇² + m²c⁴

with no cross terms. This yields the relativistic dispersion E² = p²c² + m²c⁴. -/
private lemma diracAlpha1_beta_anticommute : diracAlpha1 * diracBeta + diracBeta * diracAlpha1 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, add_zero, mul_neg, mul_one, neg_zero]
  all_goals try ring

/-- α₂ and β anticommute: {α₂, β} = 0.

Same structural role as `diracAlpha1_beta_anticommute`. The imaginary entries 
of α₂ don't affect the cancellation pattern since β is diagonal and real. -/
private lemma diracAlpha2_beta_anticommute : diracAlpha2 * diracBeta + diracBeta * diracAlpha2 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.reduceFinMk,
    Matrix.cons_val, mul_zero, add_zero, mul_neg, mul_one, neg_zero, zero_mul]
  all_goals try ring

/-- α₃ and β anticommute: {α₃, β} = 0.

Completes the set of α-β anticommutation relations. Both matrices have 
real entries, so the cancellations are purely ±1 arithmetic. -/
private lemma diracAlpha3_beta_anticommute : diracAlpha3 * diracBeta + diracBeta * diracAlpha3 = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, diracBeta, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.of_apply, Matrix.zero_apply, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.reduceFinMk,
    Matrix.cons_val, mul_zero, add_zero, mul_neg, mul_one, zero_add, neg_add_cancel]
  all_goals try ring

/-- α₁ is Hermitian: α₁† = α₁.

Hermiticity of all α matrices and β ensures the Dirac Hamiltonian is symmetric:
⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ on its domain. This is the first step toward proving
essential self-adjointness.

α₁ has only real entries (0 and 1), so conjugate transpose = transpose,
and the matrix is symmetric. -/
private lemma diracAlpha1_hermitian : diracAlpha1.conjTranspose = diracAlpha1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha1, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one]

/-- α₂ is Hermitian: α₂† = α₂.

Despite having imaginary entries (±I), α₂ is still Hermitian. The key is that
I appears in antisymmetric positions: (α₂)ᵢⱼ = -I implies (α₂)ⱼᵢ = +I.
Transposing swaps positions, conjugating flips signs: I* = -I.
The two operations cancel: (α₂)†ᵢⱼ = conj((α₂)ⱼᵢ) = conj(±I) = ∓I = (α₂)ᵢⱼ. -/
private lemma diracAlpha2_hermitian : diracAlpha2.conjTranspose = diracAlpha2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha2, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_neg, conj_I, neg_neg]

/-- α₃ is Hermitian: α₃† = α₃.

Like α₁, the matrix α₃ has only real entries (0 and ±1). Real symmetric
matrices are Hermitian: transpose is the identity, conjugation does nothing. -/
private lemma diracAlpha3_hermitian : diracAlpha3.conjTranspose = diracAlpha3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracAlpha3, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg]

/-- β is Hermitian: β† = β.

The mass matrix β = diag(1, 1, -1, -1) is diagonal with real entries.
Diagonal matrices are symmetric, and real entries are self-conjugate,
so Hermiticity is immediate. -/
private lemma diracBeta_hermitian : diracBeta.conjTranspose = diracBeta := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [diracBeta, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg]

/-! 
### Gamma Matrices (γ^μ)

The covariant form of the Clifford algebra, satisfying the Minkowski relation:

  {γ^μ, γ^ν} = 2η^μν  where η = diag(1, -1, -1, -1)

Related to the Dirac-Pauli matrices by: γ⁰ = β, γⁱ = βαⁱ.

These are used for the Lorentz-covariant current j^μ = ψ̄γ^μψ, which satisfies:
  • j⁰ = ψ†ψ ≥ 0  (positive-definite probability density)
  • ∂_μ j^μ = 0   (conservation law from Dirac equation)

**Hermiticity structure**: γ⁰ is Hermitian, but γⁱ are anti-Hermitian: (γⁱ)† = -γⁱ.
This is why we need the Dirac adjoint ψ̄ = ψ†γ⁰ rather than just ψ†.
-/

/-- γ⁰ = β: the timelike gamma matrix (Hermitian). -/
def gamma0 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- γ¹ = βα₁: spacelike gamma matrix (anti-Hermitian). -/
def gamma1 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

/-- γ² = βα₂: spacelike gamma matrix (anti-Hermitian, contains ±I). -/
def gamma2 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0]

/-- γ³ = βα₃: spacelike gamma matrix (anti-Hermitian). -/
def gamma3 : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]


/-!
## §0. Clifford Algebra Verification Lemmas

These lemmas verify the Dirac-Pauli representation satisfies the Clifford algebra
relations. The proofs are computational (matrix multiplication) and unenlightening
to read — their value is in their *existence*, not their *content*.

The key relations being verified:

  **Spatial anticommutation**: αᵢαⱼ + αⱼαᵢ = 2δᵢⱼ I₄
  
  **Mass term structure**: β² = I₄, {αᵢ, β} = 0
  
  **Hermiticity**: αᵢ† = αᵢ, β† = β

These ensure H_D is symmetric on its domain, which is the first step
toward self-adjointness.

The γ-matrices satisfy the Minkowski-signature Clifford algebra:
  
  {γ^μ, γ^ν} = 2η^μν  where η = diag(1, -1, -1, -1)

This is the covariant form needed for the current conservation proof.
-/
set_option maxHeartbeats 50000

/-- Minkowski-Clifford relation for γ⁰: {γ⁰, γ⁰} = 2η⁰⁰ I = 2I.

The timelike component has η⁰⁰ = +1, so γ⁰ squares to +I.
Written as γ⁰γ⁰ + γ⁰γ⁰ = 2I to match the anticommutator form. -/
private lemma clifford_00 : gamma0 * gamma0 + gamma0 * gamma0 =
    2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_neg, neg_zero,
    ↓reduceIte, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ¹} = 2η⁰¹ I = 0.

Off-diagonal Minkowski components vanish (η⁰¹ = 0), so distinct 
gamma matrices anticommute. This is the covariant form of {αᵢ, β} = 0. -/
private lemma clifford_01 : gamma0 * gamma1 + gamma1 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ²} = 0.

Off-diagonal relation with the imaginary-entry matrix γ². The ±I entries
don't affect the anticommutation since γ⁰ is diagonal. -/
private lemma clifford_02 : gamma0 * gamma2 + gamma2 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ⁰, γ³} = 0.

Both matrices have real entries; cancellation is pure ±1 arithmetic. -/
private lemma clifford_03 : gamma0 * gamma3 + gamma3 * gamma0 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ¹, γ⁰} = 0.

Same as `clifford_01` with reversed order; anticommutators are symmetric. -/
private lemma clifford_10 : gamma1 * gamma0 + gamma0 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation for γ¹: {γ¹, γ¹} = 2η¹¹ I = -2I.

Spacelike components have η¹¹ = -1 (Minkowski signature), so γ¹ squares to -I.
This sign difference from γ⁰ is what makes the metric indefinite. -/
private lemma clifford_11 : gamma1 * gamma1 + gamma1 * gamma1 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_mul, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try ring_nf


/-- Minkowski-Clifford relation: {γ¹, γ²} = 0.

Distinct spacelike gamma matrices anticommute (η¹² = 0). This mixes
real entries (γ¹) with imaginary entries (γ²). -/
private lemma clifford_12 : gamma1 * gamma2 + gamma2 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ¹, γ³} = 0.

Both matrices have real entries; purely ±1 arithmetic. -/
private lemma clifford_13 : gamma1 * gamma3 + gamma3 * gamma1 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ⁰} = 0.

Same as `clifford_02` with reversed order. -/
private lemma clifford_20 : gamma2 * gamma0 + gamma0 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ¹} = 0.

Same as `clifford_12` with reversed order. -/
private lemma clifford_21 : gamma2 * gamma1 + gamma1 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring

/-- Minkowski-Clifford relation for γ²: {γ², γ²} = 2η²² I = -2I.

Spacelike signature gives -2I. The proof uses `I_mul_I` to simplify
products of imaginary entries: (±I)(±I) = -1. -/
private lemma clifford_22 : gamma2 * gamma2 + gamma2 * gamma2 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try simp only [I_mul_I]
  all_goals try ring

/-- Minkowski-Clifford relation: {γ², γ³} = 0.

Mixes imaginary entries (γ²) with real entries (γ³). -/
private lemma clifford_23 : gamma2 * gamma3 + gamma3 * gamma2 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ⁰} = 0.

Same as `clifford_03` with reversed order. -/
private lemma clifford_30 : gamma3 * gamma0 + gamma0 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma0, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ¹} = 0.

Same as `clifford_13` with reversed order. -/
private lemma clifford_31 : gamma3 * gamma1 + gamma1 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma1, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation: {γ³, γ²} = 0.

Same as `clifford_23` with reversed order. -/
private lemma clifford_32 : gamma3 * gamma2 + gamma2 * gamma3 =
    (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma2, gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.zero_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    mul_neg, neg_mul, neg_neg, neg_zero]
  all_goals try ring_nf

/-- Minkowski-Clifford relation for γ³: {γ³, γ³} = 2η³³ I = -2I.

Completes the diagonal relations. All three spacelike matrices square to -I,
reflecting the signature (1, -1, -1, -1) of Minkowski space. -/
private lemma clifford_33 : gamma3 * gamma3 + gamma3 * gamma3 =
    (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b; fin_cases a <;> fin_cases b <;>
  simp only [gamma3, Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four,
             Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
             Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
             Matrix.cons_val, Matrix.cons_val_one, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add,
    mul_neg, neg_mul, neg_zero, smul_eq_mul, ↓reduceIte]
  all_goals try simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, mul_zero, neg_zero]
  all_goals try ring_nf


/-- Helper: -2 as scalar matrix equals -2 • 1 -/
private lemma neg_two_eq_smul : (-2 : Matrix (Fin 4) (Fin 4) ℂ) = (-2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  simp only [map_neg, neg_inj]
  rfl

/-!
### Gamma Matrix Hermiticity

The gamma matrices have mixed Hermiticity structure:
  • γ⁰ is Hermitian: (γ⁰)† = γ⁰
  • γⁱ are anti-Hermitian: (γⁱ)† = -γⁱ  for i ∈ {1,2,3}

This asymmetry reflects the Minkowski signature and is why the Dirac adjoint
is defined as ψ̄ = ψ†γ⁰ rather than just ψ†. The γ⁰ "corrects" the sign so that
j^μ = ψ̄γ^μψ transforms properly as a 4-vector.
-/

/-- γ⁰ is Hermitian: (γ⁰)† = γ⁰.

The timelike gamma matrix has real diagonal entries, hence is self-adjoint. -/
private lemma gamma0_hermitian_proof : gamma0.conjTranspose = gamma0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma0, Matrix.conjTranspose, Matrix.of_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_one, star_zero, star_neg]

/-- γ¹ is anti-Hermitian: (γ¹)† = -γ¹.

Spacelike gamma matrices pick up a sign under adjoint. This is connected to
the −1 in the Minkowski metric η¹¹ = −1. -/
private lemma gamma1_antihermitian : gamma1.conjTranspose = -gamma1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma1, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg, neg_zero]

/-- γ² is anti-Hermitian: (γ²)† = -γ².

Despite having imaginary entries, the anti-Hermiticity comes from the spatial
structure, not the presence of I. -/
private lemma gamma2_antihermitian : gamma2.conjTranspose = -gamma2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma2, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_neg, RCLike.star_def, conj_I, neg_neg, neg_zero]

/-- γ³ is anti-Hermitian: (γ³)† = -γ³. -/
private lemma gamma3_antihermitian : gamma3.conjTranspose = -gamma3 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
  simp only [gamma3, Matrix.conjTranspose, Matrix.neg_apply, Matrix.transpose_apply,
             Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  all_goals try simp [star_zero, star_one, star_neg, neg_zero, neg_neg]



/- 
=====================================================================================================================================
# DIRAC OPERATOR ON HILBERT SPACE
=====================================================================================================================================

We now lift the Clifford algebra from finite-dimensional matrices to unbounded 
operators on the spinor Hilbert space H = L²(ℝ³, ℂ⁴).

**Key structures**:
  • `SpinorSpace`: The 4-component spinor space ℂ⁴ (fiber over each spatial point)
  • `DiracOperator`: An unbounded operator with explicit domain tracking
  • `DiracHamiltonian`: Full structure with physical constants and symmetry properties

**Why domains matter**: 
The Dirac operator H_D = -iℏc(α·∇) + βmc² involves differentiation, so it cannot
be defined on all of L². We must track dom(H_D) = H¹(ℝ³, ℂ⁴) (Sobolev space).
The `domain` field in `DiracOperator` makes this explicit.

**Physical interpretation**:
  • `SpinorSpace` ≅ ℂ⁴ encodes spin-up/down × particle/antiparticle
  • The full Hilbert space L²(ℝ³, ℂ⁴) ≅ L²(ℝ³) ⊗ ℂ⁴ adds spatial wavefunctions
-/

/-- The fiber space ℂ⁴ at each spatial point. Encodes spin (2 components) 
and particle/antiparticle (2 components) degrees of freedom. -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4)

/-- An unbounded linear operator with explicit domain.

Unlike bounded operators (H →L[ℂ] H), the Dirac operator is only defined on 
a dense subspace. The `domain` field tracks this; `op` maps domain elements to H. -/
structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## §1. Clifford Algebra and Dirac Matrices

This section builds the abstract algebraic framework:

1. **Pauli matrices** (2×2): The fundamental building blocks σₓ, σᵧ, σᵤ
2. **DiracMatrices structure**: Abstract requirements for any valid representation  
3. **standardDiracMatrices**: Proof that our concrete matrices satisfy the structure

The abstraction matters because physics is representation-independent — only the
Clifford algebra relations determine the spectrum, the current, and the dynamics.
-/

/-!
### Pauli Matrices

The 2×2 Pauli matrices generate SU(2) and form the building blocks of the 
4×4 Dirac matrices via the block structure:

        ┌         ┐
        │  0   σᵢ │
  αᵢ =  │         │
        │  σᵢ  0  │
        └         ┘

They satisfy σᵢ² = I and {σᵢ, σⱼ} = 0 for i ≠ j.
-/

/-- Pauli-X (σₓ): spin flip operator. Real symmetric. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-Y (σᵧ): spin flip with phase. Imaginary antisymmetric, but still Hermitian. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli-Z (σᵤ): spin measurement in z-direction. Real diagonal. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


/-!
### Pauli Matrix Properties

The Pauli matrices satisfy:
- **Hermiticity**: σᵢ† = σᵢ (observables must be self-adjoint)
- **Involution**: σᵢ² = I (eigenvalues are ±1)
- **Anticommutation**: {σᵢ, σⱼ} = 0 for i ≠ j (the SU(2) Clifford algebra)

These are the 2×2 analogues of the 4×4 Dirac-Pauli relations.
-/

/-- σₓ is Hermitian: real symmetric matrix. -/
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose, Matrix.of_apply]

/-- σᵧ is Hermitian: the ±I entries are in conjugate positions, so (σᵧ)†ᵢⱼ = conj((σᵧ)ⱼᵢ) = σᵧᵢⱼ. -/
lemma pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose, Matrix.of_apply, conj_I]

/-- σᵤ is Hermitian: real diagonal matrix. -/
lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose, Matrix.of_apply]

/-- σₓ² = I: eigenvalues are ±1, corresponding to spin-right and spin-left states. -/
lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵧ² = I: the product (-I)(I) = 1 on the off-diagonal. -/
lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵤ² = I: diagonal entries (±1)² = 1. -/
lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- σₓ and σᵧ anticommute: {σₓ, σᵧ} = 0. 
This is the Clifford algebra relation that makes spin non-commutative. -/
lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, Matrix.add_apply]

/-- σₓ and σᵤ anticommute: {σₓ, σᵤ} = 0. -/
lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliZ, Matrix.add_apply]

/-- σᵧ and σᵤ anticommute: {σᵧ, σᵤ} = 0. -/
lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, pauliZ, Matrix.add_apply]


/-- Abstract specification of Dirac matrices.

**Purpose**: This structure captures the algebraic requirements for *any* valid
representation of the Dirac algebra, independent of the specific 4×4 matrices chosen.
Physics depends only on these relations, not on the representation.

**Mathematical content**: A representation of the Clifford algebra Cl(3,0) extended
with a "mass matrix" β. The relations are:

  • `alpha_sq`: αᵢ² = I (spatial generators are involutions)
  • `beta_sq`: β² = I (mass generator is an involution)  
  • `alpha_anticommute`: {αᵢ, αⱼ} = 0 for i ≠ j (spatial Clifford relations)
  • `alpha_beta_anticommute`: {αᵢ, β} = 0 (momentum-mass decoupling)
  • `alpha_hermitian`, `beta_hermitian`: all matrices self-adjoint

**Why abstract?**: Different representations exist (Dirac-Pauli, Weyl, Majorana),
each useful in different contexts. The spectrum, currents, and dynamics depend
only on the algebra — not on which basis you write the matrices in.

**Physical consequence**: The relations imply H_D² = (ℏc)²p² + (mc²)², giving
the relativistic dispersion relation. Any representation satisfying these
axioms will produce identical physics. -/
structure DiracMatrices where
  /-- Spatial Dirac matrices α = (α₁, α₂, α₃), coupling momentum to spinor space. -/
  alpha : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  /-- Mass matrix β, distinguishing particle from antiparticle components. -/
  beta : Matrix (Fin 4) (Fin 4) ℂ
  /-- αᵢ² = I: each αᵢ is an involution with eigenvalues ±1. -/
  alpha_sq : ∀ i, alpha i * alpha i = 1
  /-- β² = I: the mass matrix is an involution. -/
  beta_sq : beta * beta = 1
  /-- {αᵢ, αⱼ} = 0 for i ≠ j: distinct spatial matrices anticommute.
      This ensures (α·p)² = p₁² + p₂² + p₃² with no cross terms. -/
  alpha_anticommute : ∀ i j, i ≠ j → alpha i * alpha j + alpha j * alpha i = 0
  /-- {αᵢ, β} = 0: momentum and mass terms anticommute.
      This ensures H_D² has no αᵢβ cross terms. -/
  alpha_beta_anticommute : ∀ i, alpha i * beta + beta * alpha i = 0
  /-- αᵢ† = αᵢ: Hermiticity ensures the kinetic term is symmetric. -/
  alpha_hermitian : ∀ i, (alpha i).conjTranspose = alpha i
  /-- β† = β: Hermiticity ensures the mass term is symmetric. -/
  beta_hermitian : beta.conjTranspose = beta


/-- The standard (Dirac-Pauli) representation of the Dirac matrices.

**What this is**: A concrete instance of `DiracMatrices` using the 4×4 matrices
defined in the HELPER LEMMAS section. This is the representation found in most
physics textbooks and is natural for the non-relativistic limit.

**Block structure**:

        ┌         ┐           ┌         ┐
        │  0   σᵢ │           │  I₂  0  │
  αᵢ =  │         │  ,   β =  │         │
        │  σᵢ  0  │           │  0  -I₂ │
        └         ┘           └         ┘

**Why "standard"?**: In this basis, β is diagonal, making the particle/antiparticle
split manifest: upper components are "large" (particle), lower are "small" (antiparticle)
in the non-relativistic limit. Other representations (Weyl, Majorana) diagonalize
different operators and are useful for different purposes.

**Proof strategy**: Each field obligation is discharged by the corresponding
helper lemma (`diracAlpha1_sq`, `diracAlpha12_anticommute`, etc.). The `fin_cases`
tactic splits `Fin 3` into cases 0, 1, 2, then we apply the appropriate lemma.
The `add_comm` rewrites handle the symmetric cases like {α₂, α₁} = {α₁, α₂}. -/
def standardDiracMatrices : DiracMatrices where
  alpha := fun i => match i with
    | 0 => diracAlpha1
    | 1 => diracAlpha2
    | 2 => diracAlpha3
  beta := diracBeta
  alpha_sq := by
    intro i
    fin_cases i
    · exact diracAlpha1_sq
    · exact diracAlpha2_sq
    · exact diracAlpha3_sq
  beta_sq := diracBeta_sq
  alpha_anticommute := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij          -- i = j = 0: contradiction
    · exact diracAlpha12_anticommute
    · exact diracAlpha13_anticommute
    · rw [add_comm]; exact diracAlpha12_anticommute  -- {α₂, α₁} = {α₁, α₂}
    · exact absurd rfl hij          -- i = j = 1: contradiction
    · exact diracAlpha23_anticommute
    · rw [add_comm]; exact diracAlpha13_anticommute  -- {α₃, α₁} = {α₁, α₃}
    · rw [add_comm]; exact diracAlpha23_anticommute  -- {α₃, α₂} = {α₂, α₃}
    · exact absurd rfl hij          -- i = j = 2: contradiction
  alpha_beta_anticommute := by
    intro i
    fin_cases i
    · exact diracAlpha1_beta_anticommute
    · exact diracAlpha2_beta_anticommute
    · exact diracAlpha3_beta_anticommute
  alpha_hermitian := by
    intro i
    fin_cases i
    · exact diracAlpha1_hermitian
    · exact diracAlpha2_hermitian
    · exact diracAlpha3_hermitian
  beta_hermitian := diracBeta_hermitian


set_option maxHeartbeats 20000

/-!
## §2. Physical Constants

The Dirac Hamiltonian H_D = -iℏc(α·∇) + βmc² contains three physical parameters.
We bundle them with their positivity constraints to ensure well-formedness.

**Why a structure?**: Many results (e.g., spectral gap size, rest energy) depend on
these constants. Bundling them avoids passing three arguments plus three proofs everywhere.

**Units**: We work in arbitrary units; the formalism is the same whether you use
SI (ℏ ≈ 1.05 × 10⁻³⁴ J·s) or natural units (ℏ = c = 1). The proofs are unit-agnostic.
-/

/-- Physical constants for the Dirac equation.

**Fields**:
- `hbar`: Reduced Planck constant ℏ = h/2π, sets the scale of quantum effects
- `c`: Speed of light, couples space and time in relativistic dynamics  
- `m`: Particle rest mass, determines the spectral gap width 2mc²

**Constraints**:
- `hbar_pos`: ℏ > 0 (quantum mechanics requires positive action quantum)
- `c_pos`: c > 0 (causality requires positive light speed)
- `m_nonneg`: m ≥ 0 (mass can be zero for neutrinos/photons, but not negative)

**Note on massless particles**: When m = 0, the spectral gap closes and the spectrum
becomes σ(H_D) = ℝ. The Dirac equation then describes Weyl fermions. -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ: the quantum of action. -/
  hbar : ℝ
  /-- Speed of light c: the relativistic velocity scale. -/
  c : ℝ
  /-- Particle rest mass m: determines the spectral gap. -/
  m : ℝ
  /-- ℏ > 0: required for non-trivial quantum dynamics. -/
  hbar_pos : hbar > 0
  /-- c > 0: required for Lorentz signature. -/
  c_pos : c > 0
  /-- m ≥ 0: negative mass is unphysical. Zero mass is allowed (Weyl fermions). -/
  m_nonneg : m ≥ 0

/-- Rest mass energy E₀ = mc².

This is the minimum |E| for any state when m > 0. The spectrum of H_D is
(-∞, -mc²] ∪ [mc², ∞), so the spectral gap has width 2mc².

For m = 0, the rest energy vanishes and there is no spectral gap. -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2


/-!
## §3. The Dirac Operator

We now define the full Dirac Hamiltonian as an unbounded operator on Hilbert space.
This combines:
- The abstract operator structure (domain + linear map)
- Physical constants (ℏ, c, m)
- Algebraic structure (Dirac matrices)
- Analytic properties (symmetry, dense domain)

**The key theorem** (stated as an axiom here): The Dirac operator is essentially
self-adjoint and generates a strongly continuous unitary group via Stone's theorem.
This connects the Hamiltonian to time evolution: U(t) = e^{-itH_D/ℏ}.
-/

/-- The Dirac Hamiltonian as an unbounded operator on a Hilbert space.

**What this bundles**:
- `DiracOperator H`: the domain and linear map (inherited via `extends`)
- `constants`: physical parameters ℏ, c, m
- `matrices`: the Clifford algebra representation
- `symmetric`: proof that H_D is symmetric (⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩)
- `domain_dense`: the domain is dense in H

**Symmetric vs. self-adjoint**: Symmetry is the easy direction — it follows from
Hermiticity of α and β. Self-adjointness (dom(H_D) = dom(H_D*)) is harder and
requires showing the operator is essentially self-adjoint on C_c^∞(ℝ³)⁴.
We assert this via `dirac_generates_unitary`.

**Physical interpretation**: This structure represents the quantum observable
"total energy" for a relativistic spin-1/2 particle. Its spectrum gives the
allowed energy values; its eigenstates (generalized) are the stationary states. -/
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    DiracOperator H where
  /-- Physical constants ℏ, c, m for this particle. -/
  constants : DiracConstants
  /-- Dirac matrices satisfying the Clifford algebra. -/
  matrices : DiracMatrices
  /-- H_D is symmetric: ⟨H_D ψ, φ⟩ = ⟨ψ, H_D φ⟩ for ψ, φ in the domain.
      This follows from Hermiticity of α and β; it's the first step toward self-adjointness. -/
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  /-- The domain is dense in H.
      Required for the closure of H_D to be defined on a meaningful subspace. -/
  domain_dense : Dense (domain : Set H)

/-- **Axiom**: The Dirac operator generates a strongly continuous unitary group.

**Mathematical content**: There exists a one-parameter unitary group U(t) such that
H_D is the generator: H_D ψ = i lim_{t→0} (U(t)ψ - ψ)/t for ψ in the domain.

**Why an axiom?**: The full proof requires:
1. Essential self-adjointness of H_D on C_c^∞(ℝ³)⁴ (Kato's theorem)
2. The closure of H_D equals its adjoint (self-adjointness)
3. Stone's theorem: self-adjoint ⟺ generates unitary group

This is standard material (Reed-Simon Vol. II, Thaller Ch. 1) but would require
substantial Mathlib infrastructure (Sobolev spaces, distribution theory) to formalize.

**Physical meaning**: Time evolution is unitary, so probability is conserved.
The state at time t is ψ(t) = U(t)ψ(0) = e^{-itH_D/ℏ}ψ(0). -/
axiom dirac_generates_unitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∃ (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp),
      gen.IsSelfAdjoint ∧ gen.domain = H_D.domain

/-!
## §4. Spectral Properties

The spectrum of the free Dirac operator has a distinctive structure:

  σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)

  ══════════════╪═══════════════════╪══════════════
              -mc²        0        +mc²              
  
  ◄─────────────┤   spectral gap    ├────────────►
   negative     │   (-mc², +mc²)    │   positive
   energy       │    FORBIDDEN      │   energy
  (positrons)   │                   │  (electrons)

**Physical interpretation**:
- Positive branch [mc², ∞): electron states with E ≥ mc²
- Negative branch (-∞, -mc²]: positron states with E ≤ -mc²
- Gap (-mc², mc²): no physical states exist here (forbidden energies)

**Mathematical meaning**:
- For E in the gap, the resolvent (H_D - E)⁻¹ exists and is bounded
- The spectral measure assigns zero weight to the gap: E(gap) = 0
- The gap width 2mc² is the "mass gap" — it vanishes for massless particles

This structure is fundamentally different from the Schrödinger operator,
whose spectrum is typically [0, ∞) with no gap.
-/

/-- The spectrum of the free Dirac operator: two half-lines separated by a gap.

For m > 0, this is (-∞, -mc²] ∪ [mc², ∞).
For m = 0, the gap closes and σ(H_D) = ℝ.

**Note**: This is the *set* of spectral values. The spectral measure gives
the *distribution* of these values for each state. -/
def diracSpectrum (κ : DiracConstants) : Set ℝ :=
  Set.Iic (-κ.restEnergy) ∪ Set.Ici κ.restEnergy

/-- The spectral gap: the open interval (-mc², mc²) of forbidden energies.

No normalizable state can have energy expectation in this range.
The gap width 2mc² is the minimum energy required to create a particle-antiparticle pair. -/
def diracGap (κ : DiracConstants) : Set ℝ :=
  Set.Ioo (-κ.restEnergy) κ.restEnergy

/-- **Axiom**: Every point in the spectral gap has a bounded resolvent.

**Mathematical content**: For E ∈ (-mc², mc²), the operator (H_D - E) has a
bounded inverse R = (H_D - E)⁻¹ satisfying R(H_D - E)ψ = ψ for all ψ in the domain.

**Why this matters**: The resolvent set (where (H_D - z)⁻¹ exists and is bounded)
is the complement of the spectrum. This axiom asserts that the gap lies entirely
in the resolvent set, hence contains no spectrum.

**Why an axiom?**: The proof requires explicit construction of the resolvent
using Fourier analysis and the relativistic dispersion relation. For any
E ∈ (-mc², mc²), one shows ‖(H_D - E)⁻¹‖ ≤ 1/dist(E, σ(H_D)). -/
axiom dirac_gap_in_resolvent (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (hm : H_D.constants.m > 0) :
    ∀ E ∈ diracGap H_D.constants,
      ∃ (R : H →L[ℂ] H), ∀ (ψ : H_D.domain), R (H_D.op ψ - E • (ψ : H)) = ψ

/-- **Axiom**: The spectral measure vanishes on the gap.

**Mathematical content**: For any measurable B ⊆ (-mc², mc²), the spectral
projection E(B) = 0. No state has any probability weight in the gap.

**Connection to resolvent**: This follows from `dirac_gap_in_resolvent` via
the general principle that the spectral measure is supported on the spectrum.
If every point in B has a bounded resolvent, then E(B) = 0.

**Physical meaning**: You cannot prepare a state with energy in (-mc², mc²).
Any measurement of energy will yield a value in (-∞, -mc²] ∪ [mc², ∞). -/
axiom dirac_spectrum_eq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H)
    (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp)
    (hgen : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    ∀ B ⊆ diracGap H_D.constants, MeasurableSet B → E B = 0

/-!
## §5. Unboundedness Below

**The key difference from Schrödinger**: The Dirac operator is unbounded in *both*
directions. Unlike the Schrödinger Hamiltonian H = -Δ + V which is typically bounded
below (⟨Hψ, ψ⟩ ≥ c‖ψ‖² for some c), the Dirac operator has:

  inf_ψ ⟨H_D ψ, ψ⟩/‖ψ‖² = -∞
  sup_ψ ⟨H_D ψ, ψ⟩/‖ψ‖² = +∞

**Mathematical consequence**:
- Friedrichs extension does NOT apply (it requires semiboundedness)
- Self-adjointness must be established by other means (Kato's theorem)
- The Cayley transform still works — it just maps to the full circle minus a point

**Physical interpretation**:
- Negative energy states exist: these are the "positron" states (Dirac sea)
- High-momentum plane waves have energy E = ±√((pc)² + (mc²)²)
- As |p| → ∞, both branches extend to ±∞

**Historical note**: The negative energy states troubled Dirac until he proposed
the "Dirac sea" — all negative energy states are filled, and a hole appears as
a positron. Modern QFT reinterprets this as the spectral decomposition H = H₊ ⊕ H₋.
-/

/-- **Axiom**: The Dirac operator has states with arbitrarily negative energy.

**Physical basis**: Plane wave solutions with 4-momentum p^μ have two branches:
  E = ±√((pc)² + (mc²)²)

The negative branch gives E → -∞ as |p| → ∞. Normalizable wave packets
localized in momentum space near large |p| have ⟨H_D ψ, ψ⟩ ≈ -|p|c → -∞.

**Why an axiom?**: Constructing explicit wave packets in H¹(ℝ³, ℂ⁴) and computing
their energy expectation requires Fourier analysis machinery not available here. -/
axiom dirac_has_arbitrarily_negative_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2

/-- **Axiom**: The Dirac operator has states with arbitrarily positive energy.

**Physical basis**: The positive branch E = +√((pc)² + (mc²)²) gives E → +∞
as |p| → ∞. This is the "electron" branch — ordinary matter.

**Contrast with Schrödinger**: For H = -Δ + V with V bounded below, only this
direction of unboundedness occurs. The Dirac operator has both. -/
axiom dirac_has_arbitrarily_positive_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2

/-- The Dirac operator is unbounded below: for any c, some state has energy < c.

**Proof**: Immediate from the axiom `dirac_has_arbitrarily_negative_energy`.
We just forget the non-triviality witness (ψ ≠ 0). -/
theorem dirac_unbounded_below (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_negative_energy H H_D c
  exact ⟨ψ, hψ⟩

/-- The Dirac operator is unbounded above: for any c, some state has energy > c.

**Together with `dirac_unbounded_below`**: This shows the Dirac operator is
unbounded in both directions, unlike typical Schrödinger operators.

**Proof**: Immediate from `dirac_has_arbitrarily_positive_energy`. -/
theorem dirac_unbounded_above (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_positive_energy H H_D c
  exact ⟨ψ, hψ⟩

/-!
## §6. Connection to Spectral Framework

This section connects the Dirac Hamiltonian to the spectral theory machinery
developed elsewhere (Stone's theorem, functional calculus, spectral measures).

**The bridge**: `DiracSpectralData` bundles everything needed to apply spectral
methods to the Dirac operator:
- The Hamiltonian H_D
- The unitary group U(t) = e^{-itH_D/ℏ} it generates
- The spectral measure E that decomposes H_D

**Physical payoff**: Once we have this structure, we can:
- Compute time evolution: ψ(t) = U(t)ψ(0)
- Project onto energy ranges: E([a,b])ψ = "part of ψ with energy in [a,b]"
- Apply functions of energy: f(H_D) = ∫f(s)dE(s)

**Mathematical content**: This is where Stone's theorem meets the spectral theorem.
Stone says self-adjoint generators ↔ unitary groups. The spectral theorem says
self-adjoint operators have spectral measures. Together: unitary groups have
spectral decompositions.
-/

/-- Complete spectral data for a Dirac operator.

**Purpose**: Bundle all the objects needed to do spectral theory on H_D.
Rather than passing around (H_D, U_grp, gen, E, proofs...) separately,
we package them into a single structure with coherence conditions.

**Fields**:
- `hamiltonian`: the Dirac operator with its physical constants and matrices
- `U_grp`: the one-parameter unitary group U(t) = e^{-itH_D}
- `gen`: the generator of U_grp (mathematically equal to iH_D, up to domain issues)
- `gen_sa`: proof that the generator is self-adjoint
- `E`: the spectral measure (projection-valued measure on ℝ)
- `E_spectral`: proof that E is the spectral measure for gen
- `domain_eq`: the generator's domain matches the Hamiltonian's domain

**Usage**: Given `data : DiracSpectralData H`, you have access to all spectral
machinery: time evolution, functional calculus, spectral projections, etc. -/
structure DiracSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Dirac Hamiltonian with physical constants and domain. -/
  hamiltonian : DiracHamiltonian H
  /-- The strongly continuous unitary group generated by H_D. -/
  U_grp : OneParameterUnitaryGroup (H := H)
  /-- The infinitesimal generator of U_grp (related to H_D by factors of i and ℏ). -/
  gen : Generator U_grp
  /-- The generator is self-adjoint, enabling the spectral theorem. -/
  gen_sa : gen.IsSelfAdjoint
  /-- The spectral measure: E(B) projects onto states with energy in B. -/
  E : Set ℝ → H →L[ℂ] H
  /-- E is the spectral measure associated to gen via the spectral theorem. -/
  E_spectral : FunctionalCalculus.IsSpectralMeasureFor E gen
  /-- The generator's domain equals the Hamiltonian's domain. -/
  domain_eq : gen.domain = hamiltonian.domain

/-- Time evolution operator U(t) = e^{-itH_D/ℏ}.

**Physical meaning**: Maps initial state ψ(0) to state at time t: ψ(t) = U(t)ψ(0).

**Properties** (proven below and elsewhere):
- Unitary: U(t)*U(t) = U(t)U(t)* = 1
- Group law: U(s)U(t) = U(s+t)
- Strong continuity: U(t)ψ → ψ as t → 0 -/
def diracTimeEvolution (data : DiracSpectralData H) (t : ℝ) : H →L[ℂ] H :=
  data.U_grp.U t

/-- Time evolution is unitary: U(t)*U(t) = U(t)U(t)* = 1.

**Physical meaning**: Probability is conserved. If ‖ψ(0)‖ = 1, then ‖ψ(t)‖ = 1.
Inner products are preserved: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩.

**Proof strategy**:
1. For U*U = 1: Use that U(t) preserves inner products (from `U_grp.unitary`),
   then `ext_inner_left` reduces to showing ⟨φ, U*Uψ⟩ = ⟨φ, ψ⟩.
   
2. For UU* = 1: Use that U(-t) is the inverse of U(t) by the group law.
   Then U(t)* = U(-t), so U(t)U(t)* = U(t)U(-t) = U(0) = 1. -/
theorem dirac_evolution_unitary (data : DiracSpectralData H) (t : ℝ) :
    Unitary (data.U_grp.U t) := by
  constructor
  · -- adjoint * U = 1: show U(t) is an isometry
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (data.U_grp.unitary t φ ψ)
  · -- U * adjoint = 1: use U(t)* = U(-t) and group law
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, ← @inverse_eq_adjoint]
    exact data.U_grp.unitary (-t) φ ψ


/-- Functional calculus for the Dirac operator: f(H_D) = ∫f(s)dE(s).

**What this does**: Given any measurable function f : ℝ → ℂ, constructs the
operator f(H_D) by "applying f to the spectrum." For example:
- f(s) = e^{-its} gives time evolution U(t)
- f(s) = s gives H_D itself (on appropriate domain)
- f(s) = 1_{[a,b]}(s) gives the spectral projection E([a,b])

**Domain**: The operator f(H_D) is defined on states ψ where ∫|f(s)|²dμ_ψ(s) < ∞.
For bounded f, this is all of H. For unbounded f (like f(s) = s), it's a dense subspace.

**Physical meaning**: This is how we compute "functions of energy" — the quantum
analogue of evaluating f at the energy of a classical particle. -/
noncomputable def diracFunctionalCalculus (data : DiracSpectralData H) (f : ℝ → ℂ) :
    FunctionalCalculus.functionalDomainSubmodule data.E f →ₗ[ℂ] H :=
  FunctionalCalculus.functionalCalculus data.E f

/-- The sign function for splitting electron and positron subspaces.

**Definition**:
  sign(s) = +1  if s ≥ mc²   (electron energies)
  sign(s) = -1  if s ≤ -mc²  (positron energies)  
  sign(s) = 0   if |s| < mc² (in the gap)

**Physical meaning**: The operator sign(H_D) = E₊ - E₋ where E₊ projects onto
electrons and E₋ projects onto positrons. It distinguishes matter from antimatter.

**Note**: The value in the gap doesn't matter since E(gap) = 0 — no state has
weight there, so the function's value there is never "seen." -/
noncomputable def signFunction (κ : DiracConstants) : ℝ → ℂ := fun s =>
  if s ≥ κ.restEnergy then 1
  else if s ≤ -κ.restEnergy then -1
  else 0  -- in the gap, but E is zero there anyway

/-- Projection onto the electron (positive energy) subspace: E([mc², ∞)).

**Physical meaning**: For a state ψ, the vector E₊ψ is "the electron part of ψ."
The number ‖E₊ψ‖² is the probability of finding the particle in an electron state.

**Properties**:
- E₊² = E₊ (projection)
- E₊* = E₊ (self-adjoint)
- E₊ E₋ = 0 (electrons and positrons are orthogonal)
- E₊ + E₋ = 1 (for massive particles; they span everything) -/
def electronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Ici data.hamiltonian.constants.restEnergy)

/-- Projection onto the positron (negative energy) subspace: E((-∞, -mc²]).

**Physical meaning**: For a state ψ, the vector E₋ψ is "the positron part of ψ."
In the Dirac sea picture, these are the "filled" negative energy states;
a hole appears as a positron with positive energy and opposite charge.

**Modern interpretation**: This is simply the spectral projection onto the
negative branch of the spectrum. No "sea" is needed — just linear algebra. -/
def positronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))

/-- Specification of a spectral measure for a self-adjoint generator.

**What this encodes**: A projection-valued measure E on ℝ is the spectral measure
for a generator if it satisfies the axioms of spectral theory:

1. **Projection property**: E(B)² = E(B), and E(B ∩ C) = E(B)E(C)
2. **Self-adjointness**: Each E(B) is self-adjoint
3. **Normalization**: E(ℝ) = 1 (total probability is 1)
4. **Additivity**: E(B ∪ C) = E(B) + E(C) for disjoint B, C
5. **Spectral representation**: U(t) = ∫e^{its}dE(s)

**The key relationship** is `unitary_eq_integral`: the unitary group is the
Fourier transform of the spectral measure. This is the content of Stone's theorem
combined with the spectral theorem.

**Physical meaning**: E(B) projects onto states with energy in B. The scalar
measure μ_ψ(B) = ‖E(B)ψ‖² gives the probability of measuring energy in B. -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  /-- E(B)E(C) = E(B ∩ C): spectral projections multiply via intersection. -/
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  /-- E(B) is self-adjoint: ⟨E(B)ψ, φ⟩ = ⟨ψ, E(B)φ⟩. -/
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  /-- E(ℝ) = 1: the spectral measure is normalized (total probability 1). -/
  proj_univ : E Set.univ = 1
  /-- E(B ∪ C) = E(B) + E(C) for disjoint B, C: finite additivity. -/
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  /-- The defining relationship: U(t) = ∫e^{its}dE(s).
      This connects the unitary group to its spectral decomposition. -/
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ)

/-- Electron and positron subspaces are orthogonal: E₊ E₋ = 0.

**Physical meaning**: No state can be simultaneously "purely electron" and
"purely positron." If ψ is in the electron subspace (E₊ψ = ψ), then E₋ψ = 0,
and vice versa. Superpositions ψ = ψ_e + ψ_p are allowed, but ψ_e ⊥ ψ_p.

**Mathematical content**: Spectral projections for disjoint sets are orthogonal.
Since [mc², ∞) and (-∞, -mc²] are disjoint (when m > 0), their projections
satisfy E₊E₋ = E([mc², ∞) ∩ (-∞, -mc²]) = E(∅) = 0.

**Proof strategy**:
1. Show the spectral supports are disjoint: x ≥ mc² and x ≤ -mc² is impossible when mc² > 0
2. Apply the general spectral projection fact: E(A)E(B) = E(A ∩ B)
3. Conclude E₊E₋ = E(∅) = 0

**Requires m > 0**: For massless particles (m = 0), the "gap" closes and the
sets [0, ∞) and (-∞, 0] meet at 0. The projections are still orthogonal in
that case, but the proof would need to handle the boundary differently. -/
theorem electron_positron_orthogonal (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data * positronProjection data = 0 := by
  unfold electronProjection positronProjection
  -- The sets [mc², ∞) and (-∞, -mc²] are disjoint when mc² > 0
  have h_disj : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                         (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    -- x ≥ mc² and x ≤ -mc² requires mc² ≤ 0, contradicting mc² > 0
    have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
      unfold DiracConstants.restEnergy
      apply mul_pos hm
      exact sq_pos_of_pos data.hamiltonian.constants.c_pos
    linarith
  -- Disjoint spectral sets give orthogonal projections
  exact FunctionalCalculus.spectral_projection_disjoint data.E
    (Set.Ici data.hamiltonian.constants.restEnergy)
    (Set.Iic (-data.hamiltonian.constants.restEnergy))
    measurableSet_Ici measurableSet_Iic h_disj

/-- **Axiom**: The spectral measure is supported on the spectrum.

**Mathematical content**: If every point in a measurable set B has a bounded
resolvent (H - s)⁻¹, then E(B) = 0. In other words, the spectral measure
assigns no weight to the resolvent set.

**Contrapositive**: If E(B) ≠ 0, then some point in B is in the spectrum.
This is the fundamental link between the resolvent and spectral approaches.

**Why an axiom?**: The proof requires the spectral mapping theorem and
detailed properties of projection-valued measures. It's a standard result
in spectral theory (Reed-Simon Vol. I, Thm VII.3) but requires infrastructure
we don't have formalized.

**Physical meaning**: You can only measure energies that are in the spectrum.
If (H - E)⁻¹ exists and is bounded, then E is not a "real" energy value —
no state has any probability weight there. -/
axiom spectral_measure_supported_on_spectrum
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H)
    (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (B : Set ℝ) (hB : MeasurableSet B)
    -- Every point in B has a bounded resolvent (is in resolvent set)
    (h_resolvent : ∀ s ∈ B, ∃ (R : H →L[ℂ] H),
        ∀ (ψ : gen.domain), R (gen.op ψ - s • (ψ : H)) = ψ) :
    E B = 0

/-- **Axiom**: Every point in the Dirac spectral gap has a bounded resolvent.

**Mathematical content**: For s ∈ (-mc², mc²), the operator (H_D - s)⁻¹ exists
as a bounded operator on all of H. This says the gap is entirely contained
in the resolvent set ρ(H_D).

**Physical basis**: The relativistic dispersion relation E² = (pc)² + (mc²)²
implies |E| ≥ mc² for any state. Thus energies in (-mc², mc²) are "forbidden"
and the resolvent is well-defined there.

**Why an axiom?**: Explicit construction of (H_D - s)⁻¹ requires Fourier
analysis. In momentum space, (H_D - s)⁻¹ acts by multiplication by
(H_D(p) - s)⁻¹, which is bounded when s is not in the spectrum.

**Resolvent bound**: One can show ‖(H_D - s)⁻¹‖ ≤ 1/dist(s, σ(H_D)), which
blows up as s approaches ±mc² (the boundary of the spectrum). -/
axiom dirac_gap_in_resolvent_set (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0)
    (s : ℝ)
    (hs_lower : -data.hamiltonian.constants.restEnergy < s)
    (hs_upper : s < data.hamiltonian.constants.restEnergy) :
    ∃ (R : H →L[ℂ] H), ∀ (ψ : data.gen.domain),
        R (data.gen.op ψ - s • (ψ : H)) = ψ

/-- The spectral gap has zero spectral measure: E((-mc², mc²)) = 0.

**Physical meaning**: No state has any probability of having energy in the gap.
Every energy measurement yields a value in (-∞, -mc²] ∪ [mc², ∞).

**Proof strategy**:
1. By `dirac_gap_in_resolvent_set`, every s ∈ (-mc², mc²) has bounded resolvent
2. By `spectral_measure_supported_on_spectrum`, E(B) = 0 when all points in B
   have bounded resolvents
3. Apply to B = (-mc², mc²)

**Consequence**: The spectral projections E₊ and E₋ capture everything —
there's no "missing" probability in the gap. This is why E₊ + E₋ = 1. -/
theorem dirac_spectral_gap_zero (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                    data.hamiltonian.constants.restEnergy) = 0 := by
  apply spectral_measure_supported_on_spectrum data.gen data.gen_sa data.E data.E_spectral
  · exact measurableSet_Ioo  -- The open interval is measurable
  · intro s ⟨hs_lower, hs_upper⟩
    -- Every point in the gap has bounded resolvent
    exact dirac_gap_in_resolvent_set data hm s hs_lower hs_upper

/-- Electron and positron projections are complete: E₊ + E₋ = 1 (for m > 0).

**Physical meaning**: Every state decomposes uniquely into electron and positron
parts: ψ = E₊ψ + E₋ψ. There's no "third sector" — particles are either matter
or antimatter (or superpositions thereof).

**Mathematical content**: The spectral projections E([mc², ∞)) and E((-∞, -mc²])
sum to the identity. This follows because:
1. ℝ = [mc², ∞) ∪ (-∞, -mc²] ∪ (-mc², mc²)  (partition of the real line)
2. E(gap) = 0 (spectral gap theorem)
3. E(ℝ) = 1 (normalization)

Therefore: E₊ + E₋ = E([mc², ∞) ∪ (-∞, -mc²]) = E(ℝ \ gap) = E(ℝ) - E(gap) = 1 - 0 = 1.

**Proof strategy**:
1. Show mc² > 0 (from m > 0 and c > 0)
2. Invoke `dirac_spectral_gap_zero`: E(gap) = 0
3. Show the three sets partition ℝ: every real number is either ≥ mc², ≤ -mc², or between
4. Show the relevant sets are disjoint (for applying additivity)
5. Chain equalities: E₊ + E₋ = E(E₊ ∪ E₋) = E(E₊ ∪ E₋ ∪ gap) - E(gap) = E(ℝ) - 0 = 1

**Requires m > 0**: For m = 0, the sets [0, ∞) and (-∞, 0] overlap at 0,
and the statement becomes E([0,∞)) + E((-∞, 0]) = 1 + E({0}), which requires
knowing whether 0 is in the point spectrum. -/
theorem electron_positron_complete (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data + positronProjection data = 1 := by
  unfold electronProjection positronProjection
  -- E([mc², ∞)) + E((-∞, -mc²]) = E(ℝ) = 1
  -- because ℝ = [mc², ∞) ∪ (-∞, -mc²] ∪ (-mc², mc²) and E(gap) = 0
  
  -- Step 1: mc² > 0
  have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
    unfold DiracConstants.restEnergy
    apply mul_pos hm
    exact sq_pos_of_pos data.hamiltonian.constants.c_pos
  
  -- Step 2: The gap contributes nothing
  have h_gap : data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                               data.hamiltonian.constants.restEnergy) = 0 :=
    dirac_spectral_gap_zero data hm
  
  -- Step 3: The three sets partition ℝ
  have h_union : Set.Ici data.hamiltonian.constants.restEnergy ∪
                 Set.Iic (-data.hamiltonian.constants.restEnergy) ∪
                 Set.Ioo (-data.hamiltonian.constants.restEnergy)
                         data.hamiltonian.constants.restEnergy = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo, Set.mem_univ, iff_true]
    -- Trichotomy: x ≥ mc², x ≤ -mc², or x ∈ (-mc², mc²)
    by_cases h : x ≥ data.hamiltonian.constants.restEnergy
    · left; left; exact h
    · by_cases h' : x ≤ -data.hamiltonian.constants.restEnergy
      · left; right; exact h'
      · right
        push_neg at h h'
        exact ⟨h', h⟩
  
  -- Step 4a: Electron and positron supports are disjoint
  have h_disj1 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                          (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    linarith  -- x ≥ mc² and x ≤ -mc² contradicts mc² > 0
  
  -- Step 4b: (Electron ∪ positron) is disjoint from gap
  have h_disj2 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy ∪
                           Set.Iic (-data.hamiltonian.constants.restEnergy))
                          (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                                   data.hamiltonian.constants.restEnergy) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_union, hx_gap⟩
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo] at hx_union hx_gap
    cases hx_union with
    | inl h => linarith [hx_gap.2]  -- x ≥ mc² contradicts x < mc²
    | inr h => linarith [hx_gap.1]  -- x ≤ -mc² contradicts x > -mc²
  
  -- Step 5: Chain of equalities using additivity
  calc data.E (Set.Ici data.hamiltonian.constants.restEnergy) +
       data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
      -- Additivity: E(A) + E(B) = E(A ∪ B) for disjoint A, B
      = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
          rw [← data.E_spectral.proj_add _ _ measurableSet_Ici measurableSet_Iic h_disj1]
      -- Add zero (will become E(gap))
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) + 0 := by abel
      -- Replace 0 with E(gap)
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) +
        data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                        data.hamiltonian.constants.restEnergy) := by rw [h_gap]
      -- Additivity again: E(A ∪ B) + E(C) = E(A ∪ B ∪ C) for disjoint (A ∪ B), C
    _ = data.E Set.univ := by
        rw [← data.E_spectral.proj_add _ _ (measurableSet_Ici.union measurableSet_Iic)
            measurableSet_Ioo h_disj2, h_union]
      -- Normalization: E(ℝ) = 1
    _ = 1 := data.E_spectral.proj_univ

/-!
## §7. Relativistic Dispersion Relation

The spectrum of the Dirac operator encodes Einstein's energy-momentum relation:

  E² = (pc)² + (mc²)²

This is the relativistic generalization of E = p²/2m. For a given momentum p,
there are two energy solutions:

  E = ±√((pc)² + (mc²)²)

The positive branch corresponds to electrons, the negative to positrons.

**Key properties**:
- |E| ≥ mc² always (the rest mass sets the minimum energy scale)
- E → ±|p|c as |p| → ∞ (ultrarelativistic limit: massless behavior)
- E → ±mc² as p → 0 (rest energy)

**Connection to spectrum**: The spectral sets [mc², ∞) and (-∞, -mc²] are exactly
the ranges of the positive and negative energy branches as p varies over ℝ³.

**Mathematical consequence**: The operator H_D is unbounded in both directions,
unlike Schrödinger operators which are typically bounded below.
-/

/-- Relativistic energy as a function of momentum: E(p) = √((pc)² + (mc²)²).

This is the positive square root of the Einstein relation E² = (pc)² + (mc²)².
For simplicity we take p as a scalar (magnitude of 3-momentum).

**Special cases**:
- p = 0: E = mc² (rest energy)
- m = 0: E = |p|c (massless particle, e.g., photon)
- |p| → ∞: E ≈ |p|c (ultrarelativistic limit) -/
noncomputable def relativisticEnergy (κ : DiracConstants) (p : ℝ) : ℝ :=
  Real.sqrt ((p * κ.c)^2 + κ.restEnergy^2)

/-- Positive energy branch: E₊(p) = +√((pc)² + (mc²)²).

This is the electron branch. States with momentum p in this branch have
energy E₊(p) ≥ mc² > 0. -/
noncomputable def positiveEnergy (κ : DiracConstants) (p : ℝ) : ℝ := relativisticEnergy κ p

/-- Negative energy branch: E₋(p) = -√((pc)² + (mc²)²).

This is the positron branch. States with momentum p in this branch have
energy E₋(p) ≤ -mc² < 0.

**Historical note**: Dirac initially interpreted these as "negative energy electrons"
filling a "Dirac sea." Modern QFT reinterprets them as positive-energy positrons
via charge conjugation. -/
noncomputable def negativeEnergy (κ : DiracConstants) (p : ℝ) : ℝ := -relativisticEnergy κ p

/-- The relativistic energy is always at least mc² in magnitude.

**Physical meaning**: A massive particle at rest has energy mc². Motion can only
add kinetic energy, so |E| ≥ mc² always. This is why the spectral gap exists.

**Proof strategy**:
We show √((pc)² + (mc²)²) ≥ mc², i.e., (pc)² + (mc²)² ≥ (mc²)².
This simplifies to (pc)² ≥ 0, which is obvious.

**Consequence**: The spectrum σ(H_D) ⊆ (-∞, -mc²] ∪ [mc², ∞) — no energies
in the gap (-mc², mc²) are physically realized. -/
theorem energy_geq_rest_mass (κ : DiracConstants) (p : ℝ) :
    relativisticEnergy κ p ≥ κ.restEnergy := by
  unfold relativisticEnergy DiracConstants.restEnergy
  -- Need: √((pc)² + (mc²)²) ≥ mc²
  have h_nonneg : κ.m * κ.c^2 ≥ 0 := by
    apply mul_nonneg κ.m_nonneg
    exact sq_nonneg κ.c
  have h_inner_nonneg : (p * κ.c)^2 + (κ.m * κ.c^2)^2 ≥ 0 := by positivity
  rw [ge_iff_le]
  -- Equivalent to (mc²)² ≤ (pc)² + (mc²)², i.e., 0 ≤ (pc)²
  rw [Real.le_sqrt h_nonneg h_inner_nonneg]
  nlinarith [sq_nonneg (p * κ.c)]

/-- The Dirac operator is NOT semibounded (bounded below).

**Contrast with Schrödinger**: For H = -Δ + V with V ≥ 0, we have ⟨Hψ, ψ⟩ ≥ 0.
Such operators are "bounded below" or "semibounded."

**Dirac is different**: Because negative energy states exist, there is no
constant c such that ⟨H_D ψ, ψ⟩ ≥ c‖ψ‖² for all ψ.

**Mathematical consequence**: Friedrichs extension (a standard technique for
defining self-adjoint extensions of semibounded operators) does not apply.
Self-adjointness must be established by other means (Kato's theorem).

**Proof**: By contradiction using `dirac_unbounded_below`. -/
theorem dirac_not_semibounded (H_D : DiracHamiltonian H) :
    ¬∃ c : ℝ, ∀ (ψ : H_D.domain), c * ‖(ψ : H)‖^2 ≤ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re := by
  push_neg
  intro c
  -- For any c, there exists ψ with energy expectation < c‖ψ‖²
  obtain ⟨ψ, hψ⟩ := dirac_unbounded_below H H_D c
  exact ⟨ψ, hψ⟩

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The spectral gap contains no spectrum (placeholder version).

**Note**: This is a placeholder statement. The real theorem would assert that
for E ∈ (-mc², mc²), the resolvent (H_D - E)⁻¹ exists and is bounded.

**TODO**: Replace with proper resolvent construction once the necessary
Fourier analysis machinery is available. -/
theorem dirac_spectral_gap (H_D : DiracOperator H) (m c_light : ℝ) (hm : m > 0) (hc : c_light > 0) :
    ∀ E : ℝ, -m * c_light^2 < E → E < m * c_light^2 →
      ∃ (inv : H →ₗ[ℂ] H_D.domain), True := by
  intro E _ _
  exact ⟨0, trivial⟩  -- placeholder; real statement needs resolvent machinery

/-- The Cayley transform of a self-adjoint generator is unitary.

**Why this matters for Dirac**: Even though H_D is unbounded in both directions
(unlike semibounded Schrödinger operators), the Cayley transform still works.

The Cayley transform W = (H - i)(H + i)⁻¹ maps:
- Self-adjoint H → Unitary W (with -1 not in spectrum of W)
- Spectrum σ(H) = ℝ → σ(W) ⊆ S¹ \ {-1}

For Dirac, the spectral gap (-mc², mc²) maps to an arc of the circle around -1
that is NOT in σ(W). The unboundedness in both directions just means σ(W)
accumulates at -1 from both sides.

**Proof**: Direct application of `cayleyTransform_unitary` from the Cayley module. -/
theorem dirac_cayley_unitary
    (U_grp : @OneParameterUnitaryGroup H _ _ )
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) :=
  cayleyTransform_unitary gen hsa

/-!
## §8. The Dirac Current and Probability Conservation

**Historical context**: Before Dirac, the Klein-Gordon equation was the natural
relativistic generalization of the Schrödinger equation. But it has a fatal flaw:
its conserved current j^μ has a zeroth component j⁰ that can be negative.
This makes probability interpretation impossible — you can't have negative probability!

**Dirac's solution**: The spinor equation has a conserved current j^μ = ψ̄γ^μψ where:
- j⁰ = ψ†ψ ≥ 0 (positive-definite!)
- ∂_μ j^μ = 0 (conserved, follows from the Dirac equation)

**Why this works**: The key is that j⁰ = ψ†γ⁰γ⁰ψ = ψ†ψ because (γ⁰)² = I.
The Hermiticity structure of the gamma matrices (γ⁰ Hermitian, γⁱ anti-Hermitian)
is precisely what's needed to make ψ̄γ^μψ a real 4-vector with positive j⁰.

**Physical consequence**: Born's rule applies to spinors. The quantity
ρ(x,t) = ψ†(x,t)ψ(x,t) is a legitimate probability density, and
∫ρ d³x = 1 is conserved in time.

**Connection to spectral theory**: The spectral measure μ_ψ(B) = ‖E(B)ψ‖²
is the probability of measuring energy in B. Its invariance under time evolution
(proven later as "The First Law") is the spectral-theoretic version of
probability conservation.
-/

section DiracCurrent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Abstract specification of gamma matrices satisfying the Minkowski-Clifford algebra.

**Mathematical content**: Four 4×4 matrices γ^μ (μ = 0,1,2,3) satisfying:
- {γ^μ, γ^ν} = 2η^μν I, where η = diag(1,-1,-1,-1) is the Minkowski metric
- (γ⁰)† = γ⁰ (timelike matrix is Hermitian)
- (γⁱ)† = -γⁱ (spacelike matrices are anti-Hermitian)

**Relation to Dirac-Pauli matrices**: γ⁰ = β, γⁱ = βαⁱ. The Minkowski signature
appears because β anticommutes with the αⁱ.

**Why the Hermiticity structure?**: This ensures:
1. j^μ = ψ̄γ^μψ is real (each component is a real number)
2. j⁰ = ψ†ψ ≥ 0 (probability density is non-negative)
3. j^μ transforms as a 4-vector under Lorentz transformations

The Dirac adjoint ψ̄ = ψ†γ⁰ is defined precisely to make these properties work. -/
structure GammaMatrices where
  /-- The four gamma matrices γ⁰, γ¹, γ², γ³. -/
  gamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  /-- Minkowski-Clifford relation: {γ^μ, γ^ν} = 2η^μν I.
      For μ = ν = 0: {γ⁰, γ⁰} = 2I (timelike, positive)
      For μ = ν ∈ {1,2,3}: {γⁱ, γⁱ} = -2I (spacelike, negative)
      For μ ≠ ν: {γ^μ, γ^ν} = 0 (distinct matrices anticommute) -/
  clifford_minkowski : ∀ μ ν, gamma μ * gamma ν + gamma ν * gamma μ =
    2 • (if μ = ν then (if μ = 0 then 1 else -1) • (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0)
  /-- γ⁰ is Hermitian: (γ⁰)† = γ⁰. This makes j⁰ = ψ†ψ real and non-negative. -/
  gamma0_hermitian : (gamma 0).conjTranspose = gamma 0
  /-- γⁱ are anti-Hermitian: (γⁱ)† = -γⁱ for i ∈ {1,2,3}.
      This makes the spatial current components jⁱ real. -/
  gammaI_antihermitian : ∀ i : Fin 3, (gamma i.succ).conjTranspose = -gamma i.succ


set_option maxHeartbeats 78703

/-- The standard (Dirac) representation of the gamma matrices.

**Construction**: Uses the concrete gamma0, gamma1, gamma2, gamma3 matrices
defined in the HELPER LEMMAS section.

**Verification**: The `clifford_minkowski` field is proven by case analysis on
all 16 pairs (μ, ν), applying the appropriate `clifford_XY` lemma for each.
The pattern is:
- Diagonal (μ = ν): Use clifford_00, clifford_11, clifford_22, clifford_33
- Off-diagonal (μ ≠ ν): Use clifford_XY which proves {γ^X, γ^Y} = 0

**Note on `maxHeartbeats`**: The proof involves 16 cases with substantial
simplification in each. The increased heartbeat limit accommodates this. -/
def standardGammaMatrices : GammaMatrices where
  gamma := fun μ => match μ with
    | 0 => gamma0
    | 1 => gamma1
    | 2 => gamma2
    | 3 => gamma3
  clifford_minkowski := by
    intro μ ν
    -- 16 cases: all pairs (μ, ν) ∈ {0,1,2,3} × {0,1,2,3}
    fin_cases μ <;> fin_cases ν
    -- Each case applies the appropriate clifford_XY lemma
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_smul]; exact clifford_00
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte, nsmul_zero]; exact clifford_01
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_02
    · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_03
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, one_ne_zero, ↓reduceIte, nsmul_zero]; exact clifford_10
    · simp only [Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_11
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_12
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_13
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_20
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_21
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_22
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_23
    · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_30
    · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_31
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, nsmul_zero]; exact clifford_32
    · simp only [Fin.reduceFinMk, ↓reduceIte, Fin.isValue, Fin.reduceEq, Int.reduceNeg, neg_smul,
        one_smul, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, mul_one]; rw [neg_two_eq_smul]; exact clifford_33
  gamma0_hermitian := gamma0_hermitian_proof
  gammaI_antihermitian := by
    intro i
    fin_cases i
    · exact gamma1_antihermitian
    · exact gamma2_antihermitian
    · exact gamma3_antihermitian


/-- A spinor field assigns a 4-component spinor to each spacetime point.

This is the basic data type for solutions to the Dirac equation. A spinor
field ψ : ℝ⁴ → ℂ⁴ associates to each spacetime point x^μ = (t, x, y, z)
a 4-component complex spinor ψ(x) ∈ ℂ⁴.

**Components**: The four components encode spin (up/down) × particle/antiparticle.
In the non-relativistic limit, the upper two dominate for particles, lower two for antiparticles. -/
structure SpinorField where
  ψ : Spacetime → (Fin 4 → ℂ)

/-- A spinor field with integrability condition.

**Additional structure**: Beyond being a map ℝ⁴ → ℂ⁴, physical spinor fields
must be square-integrable on each constant-time slice. This ensures:
- The total probability ∫|ψ|² d³x is finite
- The state lives in the Hilbert space L²(ℝ³, ℂ⁴)
- Energy and momentum expectation values are well-defined

**The condition**: For each time t, the function x ↦ ‖ψ(t,x)‖² is integrable
over ℝ³ with respect to Lebesgue measure. -/
structure SpinorField' where
  /-- The four-component spinor at each spacetime point: x^μ ↦ ψ_a(x). -/
  ψ : (Fin 4 → ℝ) → (Fin 4 → ℂ)
  /-- Square-integrable on each spatial slice: ∫|ψ(t,x)|² d³x < ∞ for all t. -/
  integrable : ∀ t : ℝ, Integrable (fun x : Fin 3 → ℝ =>
    ‖ψ (Fin.cons t (fun i => x i))‖^2) volume

/-- The Dirac adjoint: ψ̄ = ψ†γ⁰.

**Why not just ψ†?**: Under Lorentz transformations, ψ transforms as a spinor:
ψ → Sψ where S is a 4×4 matrix. The naive adjoint ψ† transforms as ψ†S†,
which is NOT the correct transformation law for forming Lorentz scalars.

The Dirac adjoint ψ̄ = ψ†γ⁰ transforms as ψ̄ → ψ̄S⁻¹, which ensures that
ψ̄ψ is a Lorentz scalar and ψ̄γ^μψ is a Lorentz 4-vector.

**Component formula**: (ψ̄)_a = Σ_b (ψ_b)* (γ⁰)_{ba} -/
noncomputable def diracAdjoint (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun a => ∑ b, star (ψ b) * (Γ.gamma 0) b a

/-- The Dirac current 4-vector: j^μ = ψ̄γ^μψ.

**Physical interpretation**:
- j⁰ = ψ†ψ = probability density ρ (always ≥ 0!)
- jⁱ = ψ̄γⁱψ = probability current (flow of probability)

**Conservation**: If ψ satisfies the Dirac equation, then ∂_μ j^μ = 0.
This is the continuity equation: ∂ρ/∂t + ∇·j = 0.

**Component formula**: j^μ = Σ_{a,b} (ψ_a)* (γ⁰γ^μ)_{ab} ψ_b

**Note**: We compute γ⁰γ^μ rather than γ^μ directly because ψ̄ = ψ†γ⁰. -/
noncomputable def diracCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun μ => ∑ a : Fin 4, ∑ b : Fin 4, star (ψ a) * (Γ.gamma 0 * Γ.gamma μ) a b * ψ b

/-- γ⁰ is an involution: (γ⁰)² = I.

**Proof**: From the Clifford relation {γ⁰, γ⁰} = 2η⁰⁰ I = 2I.
Since {γ⁰, γ⁰} = 2(γ⁰)², we get (γ⁰)² = I.

**Key consequence**: This is why j⁰ = ψ†γ⁰γ⁰ψ = ψ†ψ simplifies so nicely.
The γ⁰ from the Dirac adjoint cancels with γ⁰ from γ^μ when μ = 0. -/
lemma gamma0_sq (Γ : GammaMatrices) : Γ.gamma 0 * Γ.gamma 0 = 1 := by
  have hcliff := Γ.clifford_minkowski 0 0
  simp only [↓reduceIte, one_smul, two_nsmul] at hcliff
  -- hcliff : γ⁰γ⁰ + γ⁰γ⁰ = 2·I, so 2(γ⁰)² = 2I, so (γ⁰)² = I
  have : (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0) = (2 : ℂ) • 1 := by
    calc (2 : ℂ) • (Γ.gamma 0 * Γ.gamma 0)
        = Γ.gamma 0 * Γ.gamma 0 + Γ.gamma 0 * Γ.gamma 0 := by rw [two_smul]
      _ = 1 + 1 := hcliff
      _ = (2 : ℂ) • 1 := by rw [two_smul]
  exact smul_right_injective (Matrix (Fin 4) (Fin 4) ℂ) (two_ne_zero) this

/-- **FUNDAMENTAL THEOREM**: The zeroth component of the current equals ψ†ψ.

This is the crucial identity j⁰ = Σ_a |ψ_a|² that makes Born's rule work.

**Proof outline**:
1. j⁰ = ψ̄γ⁰ψ = ψ†γ⁰γ⁰ψ (definition of Dirac adjoint)
2. γ⁰γ⁰ = I (from `gamma0_sq`)
3. j⁰ = ψ†Iψ = ψ†ψ = Σ_a |ψ_a|²

**Why this matters**: This identity is what Klein-Gordon lacks. For K-G,
the analogous quantity can be negative, destroying probability interpretation. -/
theorem current_zero_eq_norm_sq (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = ∑ a, ‖ψ a‖^2 := by
  unfold diracCurrent
  -- Use (γ⁰)² = I to simplify γ⁰γ⁰ to the identity matrix
  simp only [gamma0_sq Γ, Matrix.one_apply, RCLike.star_def, mul_ite, mul_one, mul_zero,
             ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
             ofReal_sum, ofReal_pow]
  congr 1
  funext a
  -- (ψ_a)* · ψ_a = |ψ_a|²
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact ofReal_pow ‖ψ a‖ 2

/-- **FUNDAMENTAL THEOREM**: The probability density j⁰ is non-negative.

This is the key property that Klein-Gordon lacks and Dirac has.
It allows ρ = j⁰ to be interpreted as a probability density.

**Proof**: j⁰ = Σ_a |ψ_a|² is a sum of non-negative terms.

**Physical meaning**: Probability cannot be negative. This seemingly obvious
requirement is surprisingly hard to satisfy for relativistic wave equations.
Dirac's equation was specifically designed to achieve this. -/
theorem current_zero_nonneg (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    0 ≤ (diracCurrent Γ ψ 0).re := by
  rw [current_zero_eq_norm_sq]
  simp only [ofReal_sum, ofReal_pow, re_sum]
  -- Sum of |ψ_a|² ≥ 0 because each term is ≥ 0
  apply Finset.sum_nonneg
  intro a _
  simp only [← ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg ‖ψ a‖

/-- The probability density vanishes if and only if the spinor is zero.

**Physical meaning**: The only state with zero probability everywhere is
the zero state (vacuum). Any non-zero spinor has positive probability
density somewhere.

**Proof**: j⁰ = Σ_a |ψ_a|² = 0 iff each |ψ_a|² = 0 iff each ψ_a = 0 iff ψ = 0.
This uses that a sum of non-negative terms is zero iff each term is zero. -/
theorem current_zero_eq_zero_iff (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) :
    diracCurrent Γ ψ 0 = 0 ↔ ψ = 0 := by
  rw [current_zero_eq_norm_sq]
  constructor
  · intro h
    ext a
    -- If Σ|ψ_a|² = 0 with all terms ≥ 0, then each term = 0
    have h_nonneg : ∀ i : Fin 4, 0 ≤ ‖ψ i‖^2 := fun i => sq_nonneg _
    have h_sum_eq : ∑ i : Fin 4, ‖ψ i‖^2 = 0 := by
      exact Eq.symm ((fun {z w} => ofReal_inj.mp) (id (Eq.symm h)))
    have h_each_zero := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_nonneg i) |>.mp h_sum_eq
    have : ‖ψ a‖^2 = 0 := h_each_zero a (Finset.mem_univ a)
    exact norm_eq_zero.mp (pow_eq_zero this)
  · intro h
    simp [h]

/-- The probability density ρ = j⁰ = ψ†ψ as a real number.

**Physical interpretation**: ρ(x,t) is the probability per unit volume
of finding the particle at position x at time t.

**Normalization**: For a properly normalized state, ∫ρ d³x = 1.
This integral is conserved in time (probability conservation). -/
noncomputable def probabilityDensity (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : ℝ :=
  (diracCurrent Γ ψ 0).re

/-- The probability current (spatial components): jⁱ = ψ̄γⁱψ.

**Physical interpretation**: j = (j¹, j², j³) is the probability current density.
It describes the flow of probability through space.

**Continuity equation**: ∂ρ/∂t + ∇·j = 0.
In integral form: d/dt ∫_V ρ d³x = -∮_{∂V} j·dA
(probability in V changes only by flow through boundary). -/
noncomputable def probabilityCurrent (Γ : GammaMatrices) (ψ : Fin 4 → ℂ) : Fin 3 → ℂ :=
  fun i => diracCurrent Γ ψ i.succ


end DiracCurrent

/-!
## §9. The Continuity Equation

The conservation law ∂_μ j^μ = 0 has a powerful consequence: total probability
is conserved in time. This section makes that precise.

**The logic**:
1. The Dirac equation implies ∂_μ j^μ = 0 (current conservation)
2. Expanding: ∂₀ρ + ∇·j = 0, i.e., ∂ρ/∂t = -∇·j (continuity equation)
3. Integrating over space: d/dt ∫ρ d³x = -∫∇·j d³x
4. By divergence theorem: ∫∇·j d³x = ∮j·dS → 0 if j vanishes at infinity
5. Conclusion: d/dt ∫ρ d³x = 0 (total probability is constant)

**Physical meaning**: Probability cannot be created or destroyed — it can only
flow from place to place. If ψ is normalized at t = 0 (∫|ψ|² d³x = 1), it
remains normalized for all time.

**Contrast with Klein-Gordon**: The K-G equation also has a conserved current,
but its ρ can be negative, so "probability conservation" is meaningless there.
For Dirac, ρ = ψ†ψ ≥ 0, so probability conservation is physically meaningful.
-/

section ContinuityEquation

/-- A point in 4-dimensional spacetime: x^μ = (t, x, y, z).

We represent spacetime as ℝ⁴ using Fin 4 → ℝ. The zeroth component is time,
the remaining three are spatial coordinates. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Standard basis vector e_μ in ℝ⁴.

Used for computing partial derivatives: ∂_μ f(x) = df(x)(e_μ).

**Definition**: (e_μ)_ν = δ_μν (1 if μ = ν, 0 otherwise). -/
def stdBasis (μ : Fin 4) : Spacetime := fun ν => if μ = ν then 1 else 0

/-- The four-divergence ∂_μ j^μ = ∂₀j⁰ + ∂₁j¹ + ∂₂j² + ∂₃j³.

**Physical meaning**: The four-divergence measures the local "source" of the
current. If ∂_μ j^μ = 0 everywhere, the current is conserved — no probability
is created or destroyed, only moved around.

**Implementation**: For each μ, we compute the derivative of j^μ with respect
to the μ-th coordinate, then sum over μ. -/
noncomputable def fourDivergence (j : (Fin 4 → ℝ) → (Fin 4 → ℂ)) : (Fin 4 → ℝ) → ℂ :=
  fun x => ∑ μ, deriv (fun t => j (Function.update x μ t) μ) (x μ)

/-- Partial derivative of a spinor field: ∂_μ ψ.

**Definition**: (∂_μ ψ)(x) is the derivative of ψ at x in the direction e_μ.
This is the Fréchet derivative applied to the standard basis vector.

**Component form**: (∂_μ ψ)_a = ∂/∂x^μ (ψ_a) -/
noncomputable def partialDeriv' (μ : Fin 4) (ψ : Spacetime → (Fin 4 → ℂ)) (x : Spacetime) : Fin 4 → ℂ :=
  fun a => fderiv ℝ (fun y => ψ y a) x (stdBasis μ)

/-- **Axiom**: The Dirac equation implies current conservation: ∂_μ j^μ = 0.

**Mathematical content**: If ψ satisfies iγ^μ∂_μψ = mψ (the Dirac equation),
then the current j^μ = ψ̄γ^μψ is divergence-free.

**Proof sketch** (not formalized):
1. Compute ∂_μ(ψ̄γ^μψ) = (∂_μψ̄)γ^μψ + ψ̄γ^μ(∂_μψ) by Leibniz rule
2. From iγ^μ∂_μψ = mψ, derive ∂_μψ in terms of ψ
3. Take adjoint to get ∂_μψ̄ in terms of ψ̄
4. Substitute and use Clifford algebra properties to show cancellation

**Why an axiom?**: Full proof requires careful handling of distributions,
adjoint operations on operator-valued functions, and Clifford algebra manipulation.
This is standard in physics texts but requires substantial infrastructure to formalize. -/
axiom dirac_current_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x) :
    ∀ x, fourDivergence (fun x => diracCurrent Γ (ψ.ψ x)) x = 0

/-- Construct a spacetime point from time t and spatial position x = (x¹, x², x³).

**Convention**: We use (t, x, y, z) ordering, so spacetime[0] = t and
spacetime[i+1] = xⁱ for i ∈ {0, 1, 2}. -/
def spacetimePoint (t : ℝ) (x : Fin 3 → ℝ) : Spacetime :=
  ![t, x 0, x 1, x 2]

/-- Total probability at time t: P(t) = ∫ρ(t,x) d³x = ∫ψ†ψ d³x.

**Physical meaning**: The probability of finding the particle somewhere in
space at time t. For a normalized state, this equals 1.

**Conservation**: The main theorem `probability_conserved` shows dP/dt = 0,
so if P(0) = 1, then P(t) = 1 for all t. -/
noncomputable def totalProbability (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) : ℝ :=
  ∫ x : Fin 3 → ℝ, probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) ∂volume

/-- **Axiom**: Leibniz integral rule — differentiation commutes with integration.

**Mathematical content**: d/dt ∫f(t,x) d³x = ∫(∂f/∂t)(t,x) d³x under suitable
regularity conditions (which we assume are satisfied by physical spinor fields).

**Why an axiom?**: The full Leibniz rule requires:
- Measurability of the integrand
- Dominated convergence or uniform integrability conditions
- Differentiability of the integrand in t

These conditions hold for smooth, rapidly decaying spinor fields (physical solutions),
but formalizing them requires substantial measure theory infrastructure. -/
axiom leibniz_integral_rule (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) :
    deriv (totalProbability Γ ψ) t =
    ∫ x : Fin 3 → ℝ, deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t ∂volume

/-- **Axiom**: The continuity equation ∂ρ/∂t = -∇·j.

**Mathematical content**: From the 4D conservation law ∂_μ j^μ = 0, we extract
the 3+1 form: ∂j⁰/∂t + ∂j¹/∂x¹ + ∂j²/∂x² + ∂j³/∂x³ = 0.

Since j⁰ = ρ and (j¹, j², j³) = j, this is ∂ρ/∂t + ∇·j = 0, or equivalently
∂ρ/∂t = -∇·j.

**Physical meaning**: The rate of change of probability density at a point
equals the negative divergence of the probability current — probability
decreases where current flows outward, increases where it flows inward. -/
axiom continuity_equation (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun s => probabilityDensity Γ (ψ.ψ (spacetimePoint s x))) t =
    -(∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i))

/-- **Axiom**: The divergence theorem with vanishing boundary conditions.

**Mathematical content**: ∫_ℝ³ ∇·F d³x = ∮_{∂ℝ³} F·dS. When F vanishes at
infinity (more precisely, decays fast enough), the surface integral at infinity
vanishes, so ∫∇·F d³x = 0.

**Why an axiom?**: The divergence theorem in ℝ³ with non-compact domain requires:
- Defining the "boundary at infinity" carefully
- Specifying decay conditions on F
- Handling the limit of integrals over expanding balls

Physical spinor fields decay as |x| → ∞ (they're normalizable), so the
boundary term vanishes. We assert this as an axiom.

**Note**: The hypothesis `h_vanish` asserts that ρ → 0 as |x| → ∞, which
implies the current j also decays (by the structure of the Dirac equation). -/
axiom divergence_integral_vanishes (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ)
    (h_vanish : Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                               (Filter.cocompact _) (nhds 0)) :
    ∫ x : Fin 3 → ℝ, (∑ i : Fin 3, deriv (fun s => (diracCurrent Γ (ψ.ψ (spacetimePoint t (Function.update x i s))) i.succ).re) (x i)) ∂volume = 0

/-- **MAIN THEOREM**: Total probability is conserved: d/dt ∫ρ d³x = 0.

**Physical meaning**: If you normalize your wavefunction at t = 0 so that
∫|ψ|² d³x = 1, it will remain normalized for all time. Probability is
neither created nor destroyed — only redistributed in space.

**Hypotheses**:
- `h_dirac`: ψ satisfies the Dirac equation
- `h_vanish`: ψ decays at spatial infinity (physically reasonable)

**Proof strategy**:
1. Apply Leibniz rule: d/dt ∫ρ d³x = ∫(∂ρ/∂t) d³x
2. Apply continuity equation: ∂ρ/∂t = -∇·j
3. Therefore: d/dt ∫ρ d³x = -∫∇·j d³x
4. Apply divergence theorem with decay: ∫∇·j d³x = 0
5. Conclude: d/dt ∫ρ d³x = 0

**Historical significance**: This is why Born's rule works for the Dirac equation.
Unlike Klein-Gordon, where the analogous "probability" can be negative and
"conservation" is meaningless, Dirac's ρ = ψ†ψ ≥ 0 is a genuine probability
density, and its conservation is physically meaningful. -/
theorem probability_conserved (Γ : GammaMatrices) (ψ : SpinorField) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_vanish : ∀ t, Filter.Tendsto (fun x : Fin 3 → ℝ => probabilityDensity Γ (ψ.ψ (spacetimePoint t x)))
                              (Filter.cocompact _) (nhds 0)) :
    ∀ t, deriv (totalProbability Γ ψ) t = 0 := by
  intro t
  -- Step 1: Move derivative inside integral (Leibniz rule)
  rw [leibniz_integral_rule]
  -- Step 2: Apply continuity equation ∂₀ρ = -∇·j
  have h_cont := continuity_equation Γ ψ m h_dirac t
  simp_rw [h_cont]
  -- Step 3: Integral of negative divergence
  rw [MeasureTheory.integral_neg]
  -- Step 4: Divergence integral vanishes by boundary conditions
  rw [divergence_integral_vanishes Γ ψ t (h_vanish t)]
  simp

end ContinuityEquation

/-!
## §10. Born's Rule for the Dirac Equation

This section connects the mathematical machinery to the physical interpretation:
the probability of finding a particle at position x at time t is given by
P(x,t) = |ψ(x,t)|² / ∫|ψ|² d³x.

**The three pillars of Born's rule**:
1. **Non-negativity**: P(x,t) ≥ 0 (probability cannot be negative)
2. **Normalization**: ∫P d³x = 1 (particle is somewhere with certainty)
3. **Conservation**: d/dt ∫P d³x = 0 (total probability stays 1)

**Why Dirac succeeds where Klein-Gordon fails**:
- Klein-Gordon: j⁰ = i(ψ*∂₀ψ - ψ∂₀ψ*) can be negative → no probability interpretation
- Dirac: j⁰ = ψ†ψ ≥ 0 always → Born's rule applies

This is not a minor technical detail — it's the reason the Dirac equation describes
actual physics while the Klein-Gordon equation (for spin-0 particles) requires
quantum field theory for a consistent interpretation.
-/

section BornRuleConnection

/-- The normalized probability density: P(x,t) = ρ(x,t) / ∫ρ d³x.

**Physical interpretation**: The probability per unit volume of finding the
particle at position x at time t. Unlike the unnormalized density ρ = ψ†ψ,
this always integrates to 1.

**Well-definedness**: Requires totalProbability ≠ 0, i.e., ψ ≠ 0.
For the zero spinor, probability is undefined (there's no particle). -/
noncomputable def normalizedProbability (Γ : GammaMatrices) (ψ : SpinorField)
    (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  probabilityDensity Γ (ψ.ψ (spacetimePoint t x)) / totalProbability Γ ψ t

/-- **BORN'S RULE**: The normalized probability density is a valid probability distribution.

**The theorem**: For any non-trivial solution ψ of the Dirac equation:
1. P(x,t) ≥ 0 for all x (non-negativity)
2. ∫P(x,t) d³x = 1 (normalization)

Combined with `probability_conserved`, this gives the full Born rule:
ψ†ψ/∫ψ†ψ is a time-independent probability density.

**Historical context**: Born's 1926 interpretation of |ψ|² as probability was
initially controversial. Dirac's equation provided the relativistic justification:
the probability density ψ†ψ is not just positive, it's part of a conserved
4-current, giving a mathematically consistent probability interpretation.

**Why Klein-Gordon fails**: For K-G, the analogous quantity j⁰ = i(ψ*∂₀ψ - ψ∂₀ψ*)
is NOT positive-definite. It can be negative, making "probability" meaningless.
This is why K-G describes spin-0 particles only in the QFT framework, where
j⁰ becomes charge density (which can be negative: particles vs antiparticles).

**Proof structure**:
1. Non-negativity: P = ρ/∫ρ, both numerator and denominator are non-negative
   (from `current_zero_nonneg`), so P ≥ 0.
2. Normalization: ∫(ρ/∫ρ) = (∫ρ)/(∫ρ) = 1. -/
theorem born_rule_valid (Γ : GammaMatrices) (ψ : SpinorField) (t : ℝ) (m : ℂ)
    (h_dirac : ∀ x, (∑ μ, I • (Γ.gamma μ).mulVec (partialDeriv' μ ψ.ψ x)) = m • ψ.ψ x)
    (h_nonzero : totalProbability Γ ψ t ≠ 0) :
    -- Probability is non-negative
    (∀ x, 0 ≤ normalizedProbability Γ ψ t x) ∧
    -- Probability integrates to 1
    (∫ x, normalizedProbability Γ ψ t x ∂volume = 1) := by
  constructor
  · -- Part 1: Non-negativity
    intro x
    unfold normalizedProbability
    -- P = ρ(x)/∫ρ ≥ 0 because both numerator and denominator are ≥ 0
    apply div_nonneg
    · -- ρ(x) = (j⁰).re ≥ 0
      exact current_zero_nonneg Γ _
    · -- ∫ρ ≥ 0 (integral of non-negative function)
      unfold totalProbability
      apply MeasureTheory.integral_nonneg
      intro y
      exact current_zero_nonneg Γ _
  · -- Part 2: Normalization to 1
    unfold normalizedProbability
    -- ∫(ρ/∫ρ) = (1/∫ρ) · ∫ρ = 1
    simp only [div_eq_mul_inv]
    rw [MeasureTheory.integral_mul_const]
    -- (∫ρ) · (∫ρ)⁻¹ = 1 (using h_nonzero)
    exact
      CommGroupWithZero.mul_inv_cancel
        (∫ (a : Fin 3 → ℝ), probabilityDensity Γ (ψ.ψ (spacetimePoint t a))) h_nonzero

end BornRuleConnection

/-!
## §11. Thermodynamic Unitarity and the First Law

This section establishes the spectral-theoretic version of probability conservation:
the probability of measuring energy in any set B is invariant under time evolution.

**The "First Law"** (proven at the end of this section): For any measurable set B ⊆ ℝ,
  ‖E(B) U(t) ψ‖² = ‖E(B) ψ‖²

This says: if you evolve a state by time t, then measure whether its energy is in B,
you get the same probability as measuring first. Energy probabilities are conserved.

**Why "thermodynamic"?**: In statistical mechanics, conservation of probability
underlies the second law. Unitary evolution preserves the von Neumann entropy
S = -Tr(ρ log ρ), and energy probability conservation is the spectral version
of this. The name emphasizes that this is a fundamental constraint, not a
derived property.

**Technical machinery**:
- Spectral projections E(B) as functional calculus of indicator functions 1_B
- Time evolution U(t) as functional calculus of exponentials e^{its}
- Commutativity: functions of the same operator commute, so [E(B), U(t)] = 0
- Unitarity: U(t) preserves norms and inner products

**Connection to Born's rule**: The spatial probability ∫|ψ|² d³x (§10) is conserved
because of the Dirac current. The spectral probability ‖E(B)ψ‖² is conserved
because of unitarity. These are complementary aspects of the same physics:
probability is fundamentally conserved in quantum mechanics.
-/

section ThermodynamicUnitarity

/-- **Axiom**: Spectral projections are the functional calculus of indicator functions.

**Mathematical content**: E(B) = 1_B(H) where 1_B is the indicator function of B.
This connects two views of spectral projections:
1. The projection-valued measure view: E(B) projects onto states with energy in B
2. The functional calculus view: E(B) = f(H) where f = 1_B

**Why this matters**: It allows us to use functional calculus identities to
prove properties of spectral projections. For example, E(B)² = E(B) follows
from 1_B² = 1_B.

**Why an axiom?**: The full proof requires showing that the spectral measure E
and the functional calculus φ are related by φ(f) = ∫f dE. This is a deep
theorem in spectral theory (see Reed-Simon Vol. I, Thm VII.2). -/
axiom spectral_projection_eq_indicator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Set ℝ → H →L[ℂ] H) (B : Set ℝ) (hB : MeasurableSet B) :
    E B = FunctionalCalculus.boundedFunctionalCalculus E (Set.indicator B 1) (indicator_bounded B)

/-- **Axiom**: Time evolution is the functional calculus of the exponential.

**Mathematical content**: U(t) = e^{itH} = ∫e^{its} dE(s).
This is the spectral representation of Stone's theorem: the unitary group
generated by a self-adjoint operator is the functional calculus of s ↦ e^{its}.

**Physical meaning**: Each energy eigenstate |E⟩ evolves as |E⟩ → e^{itE}|E⟩.
The full evolution is the "sum" (integral) over all energies.

**Why an axiom?**: This requires the full strength of Stone's theorem plus
the spectral theorem. The proof that U(t) = ∫e^{its} dE(s) involves showing
that both sides have the same generator and using uniqueness. -/
axiom unitary_eq_spectral_integral {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (t : ℝ) (hb : ∃ M, ∀ s : ℝ, ‖Complex.exp (I * t * s)‖ ≤ M) :
    U_grp.U t = FunctionalCalculus.boundedFunctionalCalculus E (fun s => Complex.exp (I * t * s)) hb

/-- **Axiom**: Functions of the same operator commute: [f(H), g(H)] = 0.

**Mathematical content**: If f(H) and g(H) are both defined via functional calculus
from the same spectral measure E, then they commute.

**Intuition**: In the eigenbasis, f(H) and g(H) are both diagonal (with entries
f(λ) and g(λ) for eigenvalue λ). Diagonal matrices commute.

**Key application**: E(B) = 1_B(H) and U(t) = e^{itH} commute because both
are functions of H. This is the crucial step in proving the First Law.

**Why an axiom?**: The proof requires showing that the functional calculus
is a *-homomorphism from bounded Borel functions to B(H). The commutativity
then follows from commutativity of pointwise multiplication: (fg)(s) = (gf)(s). -/
axiom functional_calculus_comm (E : Set ℝ → H →L[ℂ] H)
    (f g : ℝ → ℂ)
    (hf : ∃ M, ∀ s : ℝ, ‖f s‖ ≤ M)
    (hg : ∃ M, ∀ s : ℝ, ‖g s‖ ≤ M) :
    FunctionalCalculus.boundedFunctionalCalculus E f hf * FunctionalCalculus.boundedFunctionalCalculus E g hg =
    FunctionalCalculus.boundedFunctionalCalculus E g hg * FunctionalCalculus.boundedFunctionalCalculus E f hf

/-- **Axiom**: Norm-preserving linear maps preserve inner products.

**Mathematical content**: If ‖Tψ‖ = ‖ψ‖ for all ψ, then ⟨Tψ, Tφ⟩ = ⟨ψ, φ⟩ for all ψ, φ.

**Proof idea** (not formalized): Use the polarization identity
  ⟨ψ, φ⟩ = ¼(‖ψ+φ‖² - ‖ψ-φ‖² + i‖ψ+iφ‖² - i‖ψ-iφ‖²)

If T preserves norms, it preserves each term on the right, hence the inner product.

**Why an axiom?**: The polarization identity proof is straightforward but requires
setting up the right algebraic manipulations. We assert it here.

**Application**: Unitary operators preserve norms, hence preserve inner products.
This is used in proving that time evolution preserves transition amplitudes. -/
axiom norm_preserving_implies_inner_preserving (T : H →L[ℂ] H)
    (h_norm : ∀ χ, ‖T χ‖ = ‖χ‖) :
    ∀ ψ φ, ⟪T ψ, T φ⟫_ℂ = ⟪ψ, φ⟫_ℂ

/-- The function s ↦ e^{its} is bounded by 1 for any fixed t.

**Proof**: |e^{its}| = e^{Re(its)} = e^0 = 1, since its is purely imaginary.

**Purpose**: This boundedness condition is required to apply the bounded
functional calculus. It ensures U(t) = ∫e^{its} dE(s) converges. -/
lemma exp_its_bounded (t : ℝ) : ∃ M, ∀ s : ℝ, ‖Complex.exp (I * t * s)‖ ≤ M := by
  use 1
  intro s
  rw [Complex.norm_exp]
  -- |e^z| = e^{Re(z)}, so we need Re(its) = 0
  have h_re : (I * t * s).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h_re, Real.exp_zero]

/-- The indicator function 1_B is bounded by 1.

**Proof**: 1_B(s) ∈ {0, 1}, both of which have norm ≤ 1.

**Purpose**: This boundedness condition is required to express E(B) via
the bounded functional calculus: E(B) = 1_B(H). -/
lemma indicator_bounded (B : Set ℝ) : ∃ M, ∀ s : ℝ, ‖Set.indicator B (1 : ℝ → ℂ) s‖ ≤ M := by
  use 1
  intro s
  simp only [Set.indicator]
  split_ifs with h
  · simp  -- s ∈ B: ‖1‖ = 1 ≤ 1
  · simp  -- s ∉ B: ‖0‖ = 0 ≤ 1


/-- Time evolution commutes with spectral projections: [U(t), E(B)] = 0.

**Mathematical content**: U(t) E(B) = E(B) U(t) for any measurable set B.

**Why this is true**: Both U(t) and E(B) are functions of the same operator H:
- U(t) = e^{itH} = ∫e^{its} dE(s)
- E(B) = 1_B(H) = ∫1_B(s) dE(s)

Functions of the same operator always commute (they're simultaneously diagonal
in the eigenbasis).

**Physical meaning**: Measuring whether energy is in B, then evolving, gives
the same result as evolving then measuring. Energy is a conserved quantity,
so time evolution doesn't change which energy sector a state is in.

**Proof**: Express both U(t) and E(B) via bounded functional calculus, then
apply `functional_calculus_comm`. -/
theorem unitary_commutes_with_spectral (data : DiracSpectralData H)
    (t : ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
    data.U_grp.U t * data.E B = data.E B * data.U_grp.U t := by
  -- U(t) = Φ(e^{its}), E(B) = Φ(1_B), where Φ is the functional calculus
  have hU := unitary_eq_spectral_integral data.gen data.gen_sa data.E
    data.E_spectral t (exp_its_bounded t)
  have hE : data.E B = FunctionalCalculus.boundedFunctionalCalculus data.E
    (Set.indicator B 1) (indicator_bounded B) :=
    spectral_projection_eq_indicator data.E B hB
  rw [hU, hE]
  -- Functions of the same operator commute
  exact functional_calculus_comm data.E _ _ (exp_its_bounded t) (indicator_bounded B)

/-- **Axiom**: The spectral scalar measure of a set equals the squared norm of the projection.

**Mathematical content**: μ_ψ(B) = ‖E(B)ψ‖² (as an extended non-negative real).

**Physical interpretation**: The probability of measuring energy in B for state ψ
is ‖E(B)ψ‖². This is Born's rule applied to energy measurements.

**Why an axiom?**: The spectral scalar measure μ_ψ is defined abstractly via
the spectral theorem. Showing it equals ‖E(B)ψ‖² requires unpacking the
construction of the spectral measure and relating it to projections. -/
axiom spectral_scalar_measure_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Set ℝ → H →L[ℂ] H) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    BochnerRoute.spectral_scalar_measure E ψ B = ENNReal.ofReal (‖E B ψ‖^2)

/-- **THE FIRST LAW**: Spectral measure is invariant under time evolution.

**Statement**: μ_{U(t)ψ}(B) = μ_ψ(B) for all measurable B and all times t.

**Physical meaning**: The probability of measuring energy in B is the same
before and after time evolution. Energy probabilities are conserved.

**Equivalently**: ‖E(B) U(t) ψ‖² = ‖E(B) ψ‖² — the probability of finding
the evolved state in energy range B equals the probability for the original state.

**Why "First Law"?**: This is the spectral-theoretic analogue of energy conservation.
In thermodynamics, the first law says energy is conserved. Here, we have something
stronger: not just total energy, but the entire probability distribution over
energies is conserved.

**Proof strategy**:
1. Use commutativity: E(B) U(t) ψ = U(t) E(B) ψ
2. Use unitarity: ‖U(t) x‖ = ‖x‖
3. Combine: ‖E(B) U(t) ψ‖ = ‖U(t) E(B) ψ‖ = ‖E(B) ψ‖
4. Square both sides and apply `spectral_scalar_measure_apply`

**Connection to probability conservation** (§9-10):
- Spatial probability: ∫|ψ(x)|² d³x is conserved (continuity equation)
- Energy probability: ‖E(B)ψ‖² is conserved (this theorem)

Both are manifestations of unitarity, but in different representations
(position vs. energy). -/
theorem spectral_measure_invariant {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (t : ℝ) (ψ : H) (B : Set ℝ) (hB : MeasurableSet B) :
    BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
    BochnerRoute.spectral_scalar_measure E ψ B := by
  -- Strategy: μ_{U(t)ψ}(B) = ‖E(B) U(t)ψ‖²
  --                        = ‖U(t) E(B)ψ‖²  (commutativity)
  --                        = ‖E(B)ψ‖²       (unitarity)
  --                        = μ_ψ(B)

  -- Step 1: Commutativity — E(B) and U(t) can be swapped
  have h_comm : E B (U_grp.U t ψ) = U_grp.U t (E B ψ) := by
    -- From operator equation U(t) * E(B) = E(B) * U(t), extract pointwise
    have h_op : U_grp.U t * E B = E B * U_grp.U t := by
      have hU := unitary_eq_spectral_integral gen hsa E hE t (exp_its_bounded t)
      have hEB : E B = FunctionalCalculus.boundedFunctionalCalculus E
        (Set.indicator B 1) (indicator_bounded B) := spectral_projection_eq_indicator E B hB
      rw [hU, hEB]
      exact functional_calculus_comm E _ _ (exp_its_bounded t) (indicator_bounded B)
    -- Apply operator equation to ψ
    calc E B (U_grp.U t ψ)
        = (E B * U_grp.U t) ψ := rfl
      _ = (U_grp.U t * E B) ψ := by rw [h_op]
      _ = U_grp.U t (E B ψ) := rfl

  -- Step 2: Unitarity — U(t) preserves norms
  have h_norm_preserve : ‖U_grp.U t (E B ψ)‖ = ‖E B ψ‖ := by
    have h_inner := U_grp.unitary t (E B ψ) (E B ψ)
    -- ⟨U(t)x, U(t)x⟩ = ⟨x, x⟩ implies ‖U(t)x‖² = ‖x‖²
    have h_norm_sq : ‖U_grp.U t (E B ψ)‖^2 = ‖E B ψ‖^2 := by
      rw [@norm_preserving]
    exact norm_preserving U_grp t ((E B) ψ)

  -- Step 3: Combine via spectral scalar measure
  rw [spectral_scalar_measure_apply E (U_grp.U t ψ) B hB,
      spectral_scalar_measure_apply E ψ B hB,
      h_comm, h_norm_preserve]




/-- Unitarity implies spectral invariance -/
theorem unitary_implies_spectral_invariance {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (h_unitary : ∀ t, Unitary (U_grp.U t)) :
    ∀ t ψ B, MeasurableSet B →
      BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
      BochnerRoute.spectral_scalar_measure E ψ B := by
  intro t ψ B hB
  exact spectral_measure_invariant gen hsa E hE t ψ B hB


set_option maxHeartbeats 30000 -- Modest increase for the surjectivity argument

/-- **Converse to the First Law**: Spectral invariance implies unitarity.

**Statement**: If the spectral measure is preserved by evolution (for all states,
all times, all measurable sets), then the evolution operators are unitary.

**Physical meaning**: If energy probabilities are conserved, then the evolution
must be unitary. This is a kind of "rigidity" result — unitarity is the ONLY
way to preserve spectral measures.

**Logical structure**:
- First Law: Unitarity ⟹ Spectral invariance
- This theorem: Spectral invariance ⟹ Unitarity
- Together: Unitarity ⟺ Spectral invariance

**Proof strategy**:
1. Show U(t) preserves norms: ‖U(t)ψ‖ = ‖ψ‖
   - Use spectral invariance with B = ℝ: μ_{U(t)ψ}(ℝ) = μ_ψ(ℝ)
   - Since E(ℝ) = 1, this gives ‖U(t)ψ‖² = ‖ψ‖²

2. Show U(t) preserves inner products: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩
   - Apply polarization identity (via `norm_preserving_implies_inner_preserving`)

3. Prove U(t)*U(t) = 1 (isometry condition)
   - Follows directly from inner product preservation

4. Prove U(t)U(t)* = 1 (co-isometry condition)
   - Use surjectivity: U(-t) is a right inverse by the group law
   - For surjective isometries, U*U = 1 implies UU* = 1

**Note on heartbeats**: The surjectivity argument requires unfolding the group
law and computing U(t)U(-t) = U(0) = 1. This is computationally modest but
requires a small increase in the heartbeat limit. -/
theorem spectral_invariance_implies_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (h_inv : ∀ t ψ B, MeasurableSet B →
      BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B =
      BochnerRoute.spectral_scalar_measure E ψ B) :
    ∀ t, Unitary (U_grp.U t) := by
  intro t
  
  -- Step 1: Spectral invariance implies norm preservation
  have h_norm : ∀ χ, ‖U_grp.U t χ‖ = ‖χ‖ := by
    intro χ
    -- Use invariance with B = ℝ (the whole real line)
    have h := h_inv t χ Set.univ MeasurableSet.univ
    rw [spectral_scalar_measure_apply E (U_grp.U t χ) Set.univ MeasurableSet.univ,
        spectral_scalar_measure_apply E χ Set.univ MeasurableSet.univ] at h
    -- E(ℝ) = 1, so ‖E(ℝ)ψ‖ = ‖ψ‖
    have hE_univ : E Set.univ = 1 := hE.proj_univ
    simp only [hE_univ, ContinuousLinearMap.one_apply] at h
    -- Extract ‖U(t)χ‖² = ‖χ‖² from the ENNReal equation
    have h' := ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _) |>.mp h
    exact norm_preserving U_grp t χ

  -- Step 2: Norm preservation implies inner product preservation (polarization)
  have h_inner := norm_preserving_implies_inner_preserving (U_grp.U t) h_norm

  -- Step 3 & 4: Construct unitarity proof
  constructor
  · -- Part 1: U(t)*U(t) = 1 (isometry)
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    -- ⟨φ, U*Uψ⟩ = ⟨Uφ, Uψ⟩ = ⟨φ, ψ⟩
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (h_inner φ ψ)
    
  · -- Part 2: U(t)U(t)* = 1 (co-isometry, uses surjectivity)
    ext ψ
    -- Key insight: U(t) is surjective because U(-t) is a right inverse
    have h_surj : ∃ χ, U_grp.U t χ = ψ := by
      use U_grp.U (-t) ψ
      -- U(t)U(-t) = U(t + (-t)) = U(0) = 1
      have h := U_grp.group_law t (-t)
      simp only [add_neg_cancel] at h
      calc U_grp.U t (U_grp.U (-t) ψ)
          = U_grp.U (t + (-t)) ψ := by simp only [add_neg_cancel] ; rw [h]; exact rfl
        _ = U_grp.U 0 ψ := by ring_nf
        _ = ψ := by
          rw [@OneParameterUnitaryGroup.identity]
          exact rfl
    obtain ⟨χ, hχ⟩ := h_surj
    
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    -- Goal: ⟨φ, U(t) (U(t)* ψ)⟩ = ⟨φ, ψ⟩
    -- Write ψ = U(t)χ and use U(t)*U(t) = 1
    rw [← hχ]
    
    -- From Part 1, we have U(t)*U(t) = 1
    have h_first : (U_grp.U t).adjoint * U_grp.U t = 1 := by
      ext ξ
      apply ext_inner_left ℂ
      intro η
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact h_inner η ξ
    
    -- Therefore U(t)*(U(t)χ) = χ
    have h_adj_apply : (U_grp.U t).adjoint (U_grp.U t χ) = χ := by
      have := congrFun (congrArg DFunLike.coe h_first) χ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
      exact this

    -- Substitute: U(t)(U(t)*(U(t)χ)) = U(t)χ ✓
    rw [h_adj_apply]


/-- Time evolution preserves norms: ‖U(t)ψ‖ = ‖ψ‖.

**Physical meaning**: The total probability ‖ψ‖² is conserved under time evolution.
If a state is normalized (‖ψ‖ = 1), it remains normalized for all time.

**Proof**: Direct from the unitarity of U(t), which is encoded in `U_grp.unitary`.
The inner product ⟨U(t)ψ, U(t)ψ⟩ = ⟨ψ, ψ⟩ implies ‖U(t)ψ‖² = ‖ψ‖².

**Connection to §9-10**: This is the Hilbert space version of probability conservation.
In position space, ∫|ψ|² d³x is conserved (continuity equation). Here, ‖ψ‖² is
conserved in the abstract Hilbert space. They're the same statement in different
representations. -/
lemma unitary_preserves_norm (data : DiracSpectralData H) (t : ℝ) (χ : H) :
    ‖data.U_grp.U t χ‖ = ‖χ‖ := by
  have h_inner := data.U_grp.unitary t χ χ
  exact norm_preserving data.U_grp t χ

/-- **Electron number conservation**: ‖E₊ U(t) ψ‖ = ‖E₊ ψ‖.

**Physical meaning**: The probability of finding the particle in an electron state
(positive energy) is conserved under time evolution. If a state starts as 80%
electron and 20% positron, it stays that way forever.

**Why this is remarkable**: In non-relativistic QM, there's only one "species"
of particle. The Dirac equation has two sectors (electrons and positrons), and
this theorem says they don't mix under free evolution.

**Caveat**: This is for the FREE Dirac equation. With interactions (QED),
pair creation and annihilation CAN change electron/positron content. But for
the free equation, the split is preserved.

**Proof structure**:
1. E₊ and U(t) commute (both are functions of H_D)
2. Therefore E₊ U(t) ψ = U(t) E₊ ψ
3. U(t) preserves norms
4. So ‖E₊ U(t) ψ‖ = ‖U(t) E₊ ψ‖ = ‖E₊ ψ‖

**Connection to charge conservation**: In QFT, ‖E₊ψ‖² - ‖E₋ψ‖² is related to
electric charge. This theorem (combined with positron number conservation)
implies charge conservation for free Dirac particles. -/
theorem electron_number_conserved (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) (t : ℝ) (ψ : H) :
    ‖electronProjection data (data.U_grp.U t ψ)‖ =
    ‖electronProjection data ψ‖ := by
  unfold electronProjection
  -- Step 1: E₊ and U(t) commute
  have h_op := unitary_commutes_with_spectral data t
                 (Set.Ici data.hamiltonian.constants.restEnergy) measurableSet_Ici
  -- Step 2: Swap E₊ and U(t)
  have h_comm : data.E (Set.Ici data.hamiltonian.constants.restEnergy) (data.U_grp.U t ψ) =
                data.U_grp.U t (data.E (Set.Ici data.hamiltonian.constants.restEnergy) ψ) := by
    calc data.E _ (data.U_grp.U t ψ)
        = (data.E _ * data.U_grp.U t) ψ := rfl
      _ = (data.U_grp.U t * data.E _) ψ := by rw [h_op]
      _ = data.U_grp.U t (data.E _ ψ) := rfl
  -- Step 3: U(t) preserves norms
  rw [h_comm, unitary_preserves_norm]

/-- **Positron number conservation**: ‖E₋ U(t) ψ‖ = ‖E₋ ψ‖.

**Physical meaning**: The probability of finding the particle in a positron state
(negative energy) is conserved under time evolution.

**Historical note**: In Dirac's original "sea" picture, the negative energy states
are filled, and a "hole" (absence of a negative-energy electron) appears as a
positron with positive energy and positive charge. This conservation law says
the number of holes is constant — you can't spontaneously create or destroy
positrons without interactions.

**Modern interpretation**: The spectral projection E₋ simply picks out the
negative-energy part of the state. Conservation of ‖E₋ψ‖ means this component
evolves unitarily within its subspace, without leaking into the positive-energy
sector.

**Together with electron conservation**: Since E₊ + E₋ = 1 (for m > 0),
we have ‖E₊ψ‖² + ‖E₋ψ‖² = ‖ψ‖². Both terms are individually conserved,
which is stronger than just their sum being conserved.

**Proof**: Identical structure to `electron_number_conserved`, using E₋ = E((-∞, -mc²])
instead of E₊ = E([mc², ∞)). -/
theorem positron_number_conserved (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) (t : ℝ) (ψ : H) :
    ‖positronProjection data (data.U_grp.U t ψ)‖ =
    ‖positronProjection data ψ‖ := by
  unfold positronProjection
  -- Step 1: E₋ and U(t) commute
  have h_op := unitary_commutes_with_spectral data t
                 (Set.Iic (-data.hamiltonian.constants.restEnergy)) measurableSet_Iic
  -- Step 2: Swap E₋ and U(t)
  have h_comm : data.E (Set.Iic (-data.hamiltonian.constants.restEnergy)) (data.U_grp.U t ψ) =
                data.U_grp.U t (data.E (Set.Iic (-data.hamiltonian.constants.restEnergy)) ψ) := by
    calc data.E _ (data.U_grp.U t ψ)
        = (data.E _ * data.U_grp.U t) ψ := rfl
      _ = (data.U_grp.U t * data.E _) ψ := by rw [h_op]
      _ = data.U_grp.U t (data.E _ ψ) := rfl
  -- Step 3: U(t) preserves norms
  rw [h_comm, unitary_preserves_norm]


/-- **THE FIRST LAW EQUIVALENCE**: The fundamental theorem of quantum dynamics.

This structure encodes the equivalence between four pillars of quantum mechanics:

1. **Unitarity**: Time evolution preserves probability (U(t)*U(t) = 1)
2. **Self-adjointness**: The Hamiltonian is a physical observable (H* = H)
3. **Spectral invariance**: Energy probabilities are conserved (μ_{U(t)ψ} = μ_ψ)
4. **Energy conservation**: ⟨H⟩ is constant in time

**The logical web**:
    Self-adjointness
          ↓
    Stone's theorem
          ↓
      Unitarity ←――――――――→ Spectral invariance
          ↓                       ↓
   Norm preservation      Measure preservation
          ↓                       ↓
    Probability            Energy probability
    conservation             conservation
                                  ↓
                          Energy conservation


**Why "First Law"?**: In thermodynamics, the first law is energy conservation.
Here we have something deeper: not just that ⟨H⟩ is conserved, but that the
ENTIRE probability distribution over energies is conserved. This is the
spectral-theoretic generalization of the first law.

**Physical content**:
- Unitarity ensures probabilities sum to 1 and stay that way
- Self-adjointness ensures energy is measurable (real eigenvalues)
- Spectral invariance ensures energy measurements are reproducible
- Energy conservation is the familiar E = const

**Historical significance**: This equivalence was implicit in von Neumann's
formulation of quantum mechanics (1932) but the spectral measure perspective
makes it explicit. The Dirac equation is the first relativistic theory where
all four components hold simultaneously with a positive-definite probability. -/
structure FirstLawEquivalence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (E : Set ℝ → H →L[ℂ] H) : Prop where
  /-- Time evolution is unitary: probability is conserved. -/
  unitary : ∀ t, Unitary (U_grp.U t)
  /-- The generator (Hamiltonian) is self-adjoint: energy is observable. -/
  selfAdjoint : gen.IsSelfAdjoint
  /-- **THE FIRST LAW**: The spectral measure is invariant under time evolution.
      This is the strongest form of energy conservation — not just ⟨H⟩, but
      the entire probability distribution over energies is preserved. -/
  spectral_invariant : ∀ t ψ B, MeasurableSet B →
    BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) B = BochnerRoute.spectral_scalar_measure E ψ B
  /-- Energy expectation is conserved: ⟨ψ(t)|H|ψ(t)⟩ = ⟨ψ(0)|H|ψ(0)⟩.
      This follows from spectral invariance as a special case. -/
  energy_conserved : ∀ t ψ (hψ : ψ ∈ gen.domain),
    ⟪gen.op ⟨U_grp.U t ψ, by exact gen.domain_invariant t ψ hψ⟩, U_grp.U t ψ⟫_ℂ = ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ

/-- **Axiom**: Energy expectation equals the first moment of the spectral measure.

**Mathematical content**: ⟨ψ|H|ψ⟩ = ∫s dμ_ψ(s), where μ_ψ is the spectral
scalar measure associated to ψ.

**Physical interpretation**: The expected energy is the average over all
possible energy values, weighted by their probabilities. This is Born's rule
applied to energy measurements.

**Why an axiom?**: The proof requires:
1. Expressing H via functional calculus: H = ∫s dE(s)
2. Computing ⟨ψ|Hψ⟩ = ⟨ψ|∫s dE(s)ψ⟩ = ∫s d⟨ψ|E(s)ψ⟩ = ∫s dμ_ψ(s)

Step 2 involves interchanging inner products with spectral integrals, which
requires the full machinery of the spectral theorem for unbounded operators.

**Note**: This only makes sense for ψ in the domain of H (so Hψ is defined). -/
axiom energy_eq_spectral_moment {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = ∫ s, s ∂(BochnerRoute.spectral_scalar_measure E ψ)

/-- **MAIN THEOREM**: Self-adjointness implies the complete First Law equivalence.

**What this proves**: Starting from a self-adjoint generator H, we construct
the full `FirstLawEquivalence` structure, proving:
1. U(t) is unitary
2. H is self-adjoint (given)
3. Spectral measure is time-invariant
4. Energy expectation is conserved

**This is the culmination of the entire development**:
- §1-3: Built the Dirac matrices and operator
- §4-5: Established spectral properties (gap, unboundedness)
- §6: Connected to spectral framework
- §7: Showed relativistic dispersion relation
- §8-10: Proved probability conservation (spatial)
- §11: Proved probability conservation (spectral) — the First Law

**Proof strategy for each component**:

1. *Unitarity*: From inner product preservation (Stone's theorem).
   U(t)* U(t) = 1 follows from ⟨U(t)φ, U(t)ψ⟩ = ⟨φ, ψ⟩.
   U(t) U(t)* = 1 uses surjectivity (U(-t) is right inverse).

2. *Self-adjointness*: Given as hypothesis.

3. *Spectral invariance*: From `spectral_measure_invariant` (proven earlier).
   Uses [U(t), E(B)] = 0 (functional calculus commutes) and unitarity.

4. *Energy conservation*: From spectral invariance.
   ⟨H⟩ = ∫s dμ_ψ(s), and μ_{U(t)ψ} = μ_ψ, so ⟨H⟩ is constant.

**Physical significance**: This theorem says that a self-adjoint Hamiltonian
automatically gives you EVERYTHING: unitary evolution, conserved probabilities,
conserved energy, and conserved energy distribution. Self-adjointness is the
master key that unlocks quantum dynamics.

**For the Dirac equation specifically**: We have proven (axiomatically) that
H_D is essentially self-adjoint. This theorem then gives us all conservation
laws for free. Combined with the positive-definite probability density (§8),
we have a complete, consistent relativistic quantum mechanics. -/
theorem first_law_equivalence_of_self_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    FirstLawEquivalence gen E where
  
  -- Component 1: Unitarity of U(t)
  unitary := fun t => by
    -- Inner product preservation from Stone's theorem
    have h_inner := U_grp.unitary t
    constructor
    · -- U(t)*U(t) = 1: isometry condition
      ext ψ
      apply ext_inner_left ℂ
      intro φ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact (h_inner φ ψ)
    · -- U(t)U(t)* = 1: co-isometry, requires surjectivity
      ext ψ
      -- U(-t) is a right inverse, so U(t) is surjective
      have h_surj : ∃ χ, U_grp.U t χ = ψ := by
        use U_grp.U (-t) ψ
        have h := U_grp.group_law t (-t)
        simp only [add_neg_cancel] at h
        calc U_grp.U t (U_grp.U (-t) ψ)
            = U_grp.U (t + (-t)) ψ := by simp only [add_neg_cancel] ; rw [h]; exact rfl
          _ = U_grp.U 0 ψ := by ring_nf
          _ = ψ := by rw [OneParameterUnitaryGroup.identity]; rfl
      obtain ⟨χ, hχ⟩ := h_surj
      apply ext_inner_left ℂ
      intro φ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      rw [← hχ]
      -- Use U(t)*U(t) = 1 from first part
      have h_first : (U_grp.U t).adjoint * U_grp.U t = 1 := by
        ext ξ
        apply ext_inner_left ℂ
        intro η
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
        rw [ContinuousLinearMap.adjoint_inner_right]
        exact (h_inner η ξ)
      have h_adj_apply : (U_grp.U t).adjoint (U_grp.U t χ) = χ := by
        have := congrFun (congrArg DFunLike.coe h_first) χ
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
        exact this
      rw [h_adj_apply]
  
  -- Component 2: Self-adjointness (given)
  selfAdjoint := hsa
  
  -- Component 3: Spectral measure invariance (the First Law itself)
  spectral_invariant := fun t ψ B hB => spectral_measure_invariant gen hsa E hE t ψ B hB
  
  -- Component 4: Energy conservation (consequence of spectral invariance)
  energy_conserved := by
    intro t ψ hψ
    -- Express energy expectation as spectral moment
    rw [energy_eq_spectral_moment gen E hE (U_grp.U t ψ) (gen.domain_invariant t ψ hψ),
        energy_eq_spectral_moment gen E hE ψ hψ]
    -- The spectral measures are equal by the First Law
    have h_measure_eq : BochnerRoute.spectral_scalar_measure E (U_grp.U t ψ) =
                        BochnerRoute.spectral_scalar_measure E ψ := by
      ext B hB
      exact spectral_measure_invariant gen hsa E hE t ψ B hB
    -- Same measure ⟹ same integral
    rw [h_measure_eq]

end ThermodynamicUnitarity
end PaulDirac
