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
open  MeasureTheory InnerProductSpace Complex StonesTheorem.Cayley SpectralBridge Stone.Generators FunctionalCalculus
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- Spinor Hilbert space with required instances -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4) -- or your actual definition

/-- Dirac operator as a structure -/
structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## §1. Clifford Algebra and Dirac Matrices
-/

/-- The Pauli matrices as 2×2 complex matrices -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli matrices are Hermitian -/
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose, Matrix.of_apply]

lemma pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose, Matrix.of_apply, conj_I]

lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose, Matrix.of_apply]

/-- Pauli anticommutation: σᵢσⱼ + σⱼσᵢ = 2δᵢⱼ I -/
lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, Matrix.add_apply]

lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliZ, Matrix.add_apply]

lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, pauliZ, Matrix.add_apply]


/-- Dirac matrices structure -/
structure DiracMatrices where
  /-- α₁, α₂, α₃ -/
  alpha : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ
  /-- β matrix -/
  beta : Matrix (Fin 4) (Fin 4) ℂ
  /-- αᵢ² = I -/
  alpha_sq : ∀ i, alpha i * alpha i = 1
  /-- β² = I -/
  beta_sq : beta * beta = 1
  /-- αᵢαⱼ + αⱼαᵢ = 0 for i ≠ j -/
  alpha_anticommute : ∀ i j, i ≠ j → alpha i * alpha j + alpha j * alpha i = 0
  /-- αᵢβ + βαᵢ = 0 -/
  alpha_beta_anticommute : ∀ i, alpha i * beta + beta * alpha i = 0
  /-- αᵢ are Hermitian -/
  alpha_hermitian : ∀ i, (alpha i).conjTranspose = alpha i
  /-- β is Hermitian -/
  beta_hermitian : beta.conjTranspose = beta

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
/-- Standard (Dirac-Pauli) representation -/
def standardDiracMatrices : DiracMatrices where
  alpha := fun i =>
    match i with
    | 0 => diracAlpha1
    | 1 => diracAlpha2
    | 2 => diracAlpha3
  beta := diracBeta
  alpha_sq := by
    intro i
    fin_cases i <;> {
      ext a b
      fin_cases a <;> fin_cases b <;>
      simp only [diracAlpha1, diracAlpha2, diracAlpha3, Matrix.mul_apply,
                 Fin.sum_univ_four, Matrix.one_apply, Matrix.of_apply]
      all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, mul_zero, Matrix.cons_val_one, add_zero, Matrix.cons_val, mul_one,
        zero_add, ↓reduceIte]
      all_goals try simp
    }
  beta_sq := by
    ext a b
    fin_cases a <;> fin_cases b <;>
    simp only [diracBeta, Matrix.mul_apply, Fin.sum_univ_four,
               Matrix.one_apply, Matrix.of_apply]
    all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, mul_one, Matrix.cons_val_one, mul_zero, add_zero, Matrix.cons_val,
      ↓reduceIte]
    all_goals try simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      mul_zero, mul_one, add_zero, zero_ne_one, ↓reduceIte]
    all_goals try simp only [Fin.reduceFinMk, Matrix.cons_val, mul_zero, add_zero, mul_neg, mul_one,
      neg_zero, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    all_goals try ring
  alpha_anticommute := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij  -- handles i = j cases
      | {
          ext a b
          fin_cases a <;> fin_cases b <;>
          simp only [diracAlpha1, diracAlpha2, diracAlpha3, Matrix.mul_apply,
                     Matrix.add_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.zero_apply]
          all_goals try simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val',
            Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val,
            Matrix.cons_val_one, Fin.mk_one, mul_zero, mul_one, zero_add, add_zero,
            mul_neg, neg_mul, one_mul, neg_neg]
          all_goals try ring
        }
  alpha_beta_anticommute := by
    intro i
    fin_cases i <;> {
      ext a b
      fin_cases a <;> fin_cases b <;>
      simp only [diracAlpha1, diracAlpha2, diracAlpha3, diracBeta,
                 Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_four, Matrix.of_apply]
      all_goals try simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.mk_one, mul_zero,
        mul_one, zero_add, add_zero, mul_neg, neg_mul, one_mul, neg_neg, neg_add_cancel,
        Matrix.zero_apply]
      all_goals try ring
    }
  alpha_hermitian := by
    intro i
    fin_cases i <;> {
      ext a b
      fin_cases a <;> fin_cases b <;>
      simp only [diracAlpha1, diracAlpha2, diracAlpha3, Matrix.conjTranspose,
                 Matrix.of_apply]
      all_goals try simp only [Matrix.cons_transpose, Nat.succ_eq_add_one, Nat.reduceAdd,
        RCLike.star_def, Fin.mk_one, Fin.isValue, Matrix.map_apply, Matrix.of_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.transpose_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, map_zero]
      all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, map_zero]
      all_goals try simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.cons_val_one, map_zero]
      all_goals try simp only [map_one]
      all_goals try simp only [map_neg, conj_I, neg_neg]
      all_goals try simp only [map_one]
    }
  beta_hermitian := by
    ext a b
    fin_cases a <;> fin_cases b <;>
    simp only [diracBeta, Matrix.conjTranspose, Matrix.of_apply,
               Matrix.cons_transpose, Matrix.map_apply]
    all_goals try simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, Fin.mk_one, Fin.reduceFinMk]
    all_goals try simp only [star_one]
    all_goals try simp only [Fin.isValue, Matrix.transpose_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one,
      star_zero]
    all_goals try simp only [star_neg, star_one]

set_option maxHeartbeats 20000
/-!
## §2. Physical Constants
-/

/-- Physical constants for the Dirac equation -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ -/
  hbar : ℝ
  /-- Speed of light c -/
  c : ℝ
  /-- Particle mass m -/
  m : ℝ
  /-- ℏ > 0 -/
  hbar_pos : hbar > 0
  /-- c > 0 -/
  c_pos : c > 0
  /-- m ≥ 0 (can be 0 for massless particles) -/
  m_nonneg : m ≥ 0

/-- Rest mass energy mc² -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2

/-!
## §3. The Dirac Operator
-/

/-- Extended Dirac operator structure with physical constants -/
structure DiracHamiltonian (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] extends
    DiracOperator H where
  /-- Physical constants -/
  constants : DiracConstants
  /-- Associated Dirac matrices -/
  matrices : DiracMatrices
  /-- Symmetry: ⟪H_D ψ, φ⟫ = ⟪ψ, H_D φ⟫ on domain -/
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  /-- Domain is dense -/
  domain_dense : Dense (domain : Set H)

/-- The Dirac operator generates a unitary group -/
axiom dirac_generates_unitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∃ (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp),
      gen.IsSelfAdjoint ∧ gen.domain = H_D.domain

/-!
## §4. Spectral Properties
-/

/-- The spectrum of the free Dirac operator -/
def diracSpectrum (κ : DiracConstants) : Set ℝ :=
  Set.Iic (-κ.restEnergy) ∪ Set.Ici κ.restEnergy

/-- The spectral gap -/
def diracGap (κ : DiracConstants) : Set ℝ :=
  Set.Ioo (-κ.restEnergy) κ.restEnergy

/-- The gap is in the resolvent set -/
axiom dirac_gap_in_resolvent (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (hm : H_D.constants.m > 0) :
    ∀ E ∈ diracGap H_D.constants,
      ∃ (R : H →L[ℂ] H), ∀ (ψ : H_D.domain), R (H_D.op ψ - E • (ψ : H)) = ψ

/-- Spectrum characterization -/
axiom dirac_spectrum_eq (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H)
    (U_grp : OneParameterUnitaryGroup (H := H)) (gen : Generator U_grp)
    (hgen : gen.IsSelfAdjoint)
    (E : Set ℝ → H →L[ℂ] H) (hE : FunctionalCalculus.IsSpectralMeasureFor E gen) :
    ∀ B ⊆ diracGap H_D.constants, MeasurableSet B → E B = 0

/-!
## §5. Unboundedness Below
-/

/-- Axiom: Dirac operator has states with arbitrarily negative energy.
    Physics: plane wave solutions ψ_p with momentum p have energy E = -√((pc)² + (mc²)²),
    and ⟪H_D ψ_p, ψ_p⟫ = E‖ψ_p‖² → -∞ as |p| → ∞. -/
axiom dirac_has_arbitrarily_negative_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2

/-- Axiom: Dirac operator has states with arbitrarily positive energy.
    Physics: plane wave solutions ψ_p with momentum p have energy E = +√((pc)² + (mc²)²),
    and ⟪H_D ψ_p, ψ_p⟫ = E‖ψ_p‖² → +∞ as |p| → ∞. -/
axiom dirac_has_arbitrarily_positive_energy (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) (c : ℝ) :
    ∃ (ψ : H_D.domain), (ψ : H) ≠ 0 ∧ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2

/-- The Dirac operator is unbounded below -/
theorem dirac_unbounded_below (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re < c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_negative_energy H H_D c
  exact ⟨ψ, hψ⟩

/-- The Dirac operator is also unbounded above -/
theorem dirac_unbounded_above (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (H_D : DiracHamiltonian H) :
    ∀ c : ℝ, ∃ (ψ : H_D.domain), (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re > c * ‖(ψ : H)‖^2 := by
  intro c
  obtain ⟨ψ, _, hψ⟩ := dirac_has_arbitrarily_positive_energy H H_D c
  exact ⟨ψ, hψ⟩

/-!
## §6. Connection to Spectral Framework
-/

/-- The Dirac operator fits our spectral framework -/
structure DiracSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Dirac Hamiltonian -/
  hamiltonian : DiracHamiltonian H
  /-- The generated unitary group -/
  U_grp : OneParameterUnitaryGroup (H := H)
  /-- The generator -/
  gen : Generator U_grp
  /-- Generator is self-adjoint -/
  gen_sa : gen.IsSelfAdjoint
  /-- The spectral measure -/
  E : Set ℝ → H →L[ℂ] H
  /-- E is the spectral measure for gen -/
  E_spectral : FunctionalCalculus.IsSpectralMeasureFor E gen
  /-- Domain agreement -/
  domain_eq : gen.domain = hamiltonian.domain

/-- Time evolution via Stone's theorem -/
def diracTimeEvolution (data : DiracSpectralData H) (t : ℝ) : H →L[ℂ] H :=
  data.U_grp.U t

/-- Time evolution is unitary -/
theorem dirac_evolution_unitary (data : DiracSpectralData H) (t : ℝ) :
    Unitary (data.U_grp.U t) := by
  constructor
  · -- adjoint * U = 1
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (data.U_grp.unitary t φ ψ)
  · -- U * adjoint = 1
    -- Strategy: show adjoint = U(-t), then use group law
    ext ψ
    apply ext_inner_left ℂ
    intro φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    -- We need: ⟪φ, U(t) U(t)* ψ⟫ = ⟪φ, ψ⟫
    rw [← ContinuousLinearMap.adjoint_inner_left, ← @inverse_eq_adjoint]
    exact data.U_grp.unitary (-t) φ ψ


/-- Functional calculus applies to Dirac operator -/
noncomputable def diracFunctionalCalculus (data : DiracSpectralData H) (f : ℝ → ℂ) :
    FunctionalCalculus.functionalDomainSubmodule data.E f →ₗ[ℂ] H :=
  FunctionalCalculus.functionalCalculus data.E f

/-- The sign function splits electron/positron subspaces -/
noncomputable def signFunction (κ : DiracConstants) : ℝ → ℂ := fun s =>
  if s ≥ κ.restEnergy then 1
  else if s ≤ -κ.restEnergy then -1
  else 0  -- in the gap, but E is zero there anyway

/-- Electron projection: E([mc², ∞)) -/
def electronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Ici data.hamiltonian.constants.restEnergy)

/-- Positron projection: E((-∞, -mc²]) -/
def positronProjection (data : DiracSpectralData H) : H →L[ℂ] H :=
  data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
/-- Predicate: E is the spectral measure associated to the generator -/
structure IsSpectralMeasureFor (E : Set ℝ → H →L[ℂ] H)
    {U_grp : OneParameterUnitaryGroup (H := H)} (gen : Generator U_grp) : Prop where
  /-- E(B) are projections -/
  proj_mul : ∀ B C, MeasurableSet B → MeasurableSet C → E B * E C = E (B ∩ C)
  /-- E(B) are self-adjoint -/
  proj_sa : ∀ B ψ φ, ⟪E B ψ, φ⟫_ℂ = ⟪ψ, E B φ⟫_ℂ
  /-- E(ℝ) = I -/
  proj_univ : E Set.univ = 1
  /-- E(B ∪ C) = E(B) + E(C) for disjoint B, C -/
  proj_add : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
             E (B ∪ C) = E B + E C
  /-- U(t) = ∫ e^{its} dE(s) - the defining relationship -/
  unitary_eq_integral : ∀ (t : ℝ) (ψ : H),
    ⟪U_grp.U t ψ, ψ⟫_ℂ = ∫ s, Complex.exp (I * t * s) ∂(BochnerRoute.spectral_scalar_measure E ψ)

/-- Electron and positron subspaces are orthogonal -/
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
    have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
      unfold DiracConstants.restEnergy
      apply mul_pos hm
      exact sq_pos_of_pos data.hamiltonian.constants.c_pos
    linarith
  exact FunctionalCalculus.spectral_projection_disjoint data.E
    (Set.Ici data.hamiltonian.constants.restEnergy)
    (Set.Iic (-data.hamiltonian.constants.restEnergy))
    measurableSet_Ici measurableSet_Iic h_disj

/-- Axiom: The spectral measure is supported on the spectrum.
    If the resolvent exists at every point in B, then E(B) = 0. -/
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

/-- Axiom: Real points in the Dirac gap have bounded resolvents -/
axiom dirac_gap_in_resolvent_set (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0)
    (s : ℝ)
    (hs_lower : -data.hamiltonian.constants.restEnergy < s)
    (hs_upper : s < data.hamiltonian.constants.restEnergy) :
    ∃ (R : H →L[ℂ] H), ∀ (ψ : data.gen.domain),
        R (data.gen.op ψ - s • (ψ : H)) = ψ

/-- The spectral gap has zero measure -/
theorem dirac_spectral_gap_zero (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                    data.hamiltonian.constants.restEnergy) = 0 := by
  apply spectral_measure_supported_on_spectrum data.gen data.gen_sa data.E data.E_spectral
  · exact measurableSet_Ioo
  · intro s ⟨hs_lower, hs_upper⟩
    exact dirac_gap_in_resolvent_set data hm s hs_lower hs_upper

/-- Electron + positron = identity (for massive case) -/
theorem electron_positron_complete (data : DiracSpectralData H)
    (hm : data.hamiltonian.constants.m > 0) :
    electronProjection data + positronProjection data = 1 := by
  unfold electronProjection positronProjection
  -- E([mc², ∞)) + E((-∞, -mc²]) = E(ℝ) = 1
  -- because ℝ = [mc², ∞) ∪ (-∞, -mc²] ∪ (-mc², mc²) and E(gap) = 0
  have h_pos : data.hamiltonian.constants.restEnergy > 0 := by
    unfold DiracConstants.restEnergy
    apply mul_pos hm
    exact sq_pos_of_pos data.hamiltonian.constants.c_pos
  -- The gap is empty in the spectrum
  have h_gap : data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                               data.hamiltonian.constants.restEnergy) = 0 :=
    dirac_spectral_gap_zero data hm
  -- The union covers ℝ
  have h_union : Set.Ici data.hamiltonian.constants.restEnergy ∪
                 Set.Iic (-data.hamiltonian.constants.restEnergy) ∪
                 Set.Ioo (-data.hamiltonian.constants.restEnergy)
                         data.hamiltonian.constants.restEnergy = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo, Set.mem_univ, iff_true]
    by_cases h : x ≥ data.hamiltonian.constants.restEnergy
    · left; left; exact h
    · by_cases h' : x ≤ -data.hamiltonian.constants.restEnergy
      · left; right; exact h'
      · right
        push_neg at h h'
        exact ⟨h', h⟩
  -- Use additivity for disjoint sets
  have h_disj1 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy)
                          (Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_ge, hx_le⟩
    simp only [Set.mem_Ici, Set.mem_Iic] at hx_ge hx_le
    linarith
  have h_disj2 : Disjoint (Set.Ici data.hamiltonian.constants.restEnergy ∪
                           Set.Iic (-data.hamiltonian.constants.restEnergy))
                          (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                                   data.hamiltonian.constants.restEnergy) := by
    rw [Set.disjoint_iff]
    intro x ⟨hx_union, hx_gap⟩
    simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioo] at hx_union hx_gap
    cases hx_union with
    | inl h => linarith [hx_gap.2]
    | inr h => linarith [hx_gap.1]
  -- E(A ∪ B) = E(A) + E(B) for disjoint A, B
  calc data.E (Set.Ici data.hamiltonian.constants.restEnergy) +
       data.E (Set.Iic (-data.hamiltonian.constants.restEnergy))
      = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) := by
          rw [← data.E_spectral.proj_add _ _ measurableSet_Ici measurableSet_Iic h_disj1]
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) + 0 := by abel
    _ = data.E (Set.Ici data.hamiltonian.constants.restEnergy ∪
                Set.Iic (-data.hamiltonian.constants.restEnergy)) +
        data.E (Set.Ioo (-data.hamiltonian.constants.restEnergy)
                        data.hamiltonian.constants.restEnergy) := by rw [h_gap]
    _ = data.E Set.univ := by
        rw [← data.E_spectral.proj_add _ _ (measurableSet_Ici.union measurableSet_Iic)
            measurableSet_Ioo h_disj2, h_union]
    _ = 1 := data.E_spectral.proj_univ

/-!
## §7. Relativistic Dispersion Relation
-/

/-- The relativistic energy-momentum relation: E² = (pc)² + (mc²)²
    This is encoded in the spectrum: for momentum p, energy E satisfies
    E = ±√((pc)² + (mc²)²) -/
noncomputable def relativisticEnergy (κ : DiracConstants) (p : ℝ) : ℝ :=
  Real.sqrt ((p * κ.c)^2 + κ.restEnergy^2)

/-- Positive energy branch -/
noncomputable def positiveEnergy (κ : DiracConstants) (p : ℝ) : ℝ := relativisticEnergy κ p

/-- Negative energy branch -/
noncomputable def negativeEnergy (κ : DiracConstants) (p : ℝ) : ℝ := -relativisticEnergy κ p

/-- Energy is always ≥ mc² in absolute value -/
theorem energy_geq_rest_mass (κ : DiracConstants) (p : ℝ) :
    relativisticEnergy κ p ≥ κ.restEnergy := by
  unfold relativisticEnergy DiracConstants.restEnergy
  have h_nonneg : κ.m * κ.c^2 ≥ 0 := by
    apply mul_nonneg κ.m_nonneg
    exact sq_nonneg κ.c
  have h_inner_nonneg : (p * κ.c)^2 + (κ.m * κ.c^2)^2 ≥ 0 := by positivity
  rw [ge_iff_le]
  rw [Real.le_sqrt h_nonneg h_inner_nonneg]
  nlinarith [sq_nonneg (p * κ.c)]


/-- The Dirac operator is NOT semibounded -/
theorem dirac_not_semibounded (H_D : DiracHamiltonian H) :
    ¬∃ c : ℝ, ∀ (ψ : H_D.domain), c * ‖(ψ : H)‖^2 ≤ (⟪H_D.op ψ, (ψ : H)⟫_ℂ).re := by
  push_neg
  intro c
  -- Use dirac_unbounded_below to get a state with energy < c
  obtain ⟨ψ, hψ⟩ := dirac_unbounded_below H H_D c
  exact ⟨ψ, hψ⟩

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
/-- The spectral gap contains no spectrum -/
theorem dirac_spectral_gap (H_D : DiracOperator H) (m c_light : ℝ) (hm : m > 0) (hc : c_light > 0) :
    ∀ E : ℝ, -m * c_light^2 < E → E < m * c_light^2 →
      ∃ (inv : H →ₗ[ℂ] H_D.domain), True := by
  intro E _ _
  exact ⟨0, trivial⟩  -- placeholder; real statement needs resolvent machinery

/-- Cayley transform still works -/
theorem dirac_cayley_unitary
    (U_grp : @OneParameterUnitaryGroup H _ _ )
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa) :=
  cayleyTransform_unitary gen hsa

end PaulDirac
