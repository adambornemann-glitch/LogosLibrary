import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson.Core
/-
================================================================================
SUPPORTING LEMMAS FOR ROBERTSON'S UNCERTAINTY RELATION
================================================================================

This file contains the mathematical machinery needed to prove Robertson's
generalized uncertainty principle. The key insight is decomposing the
complex inner product ⟨Aψ, Bψ⟩ into symmetric and antisymmetric parts:

  ⟨Aψ, Bψ⟩ = (1/2)⟨ψ, {A,B}ψ⟩ + (1/2)⟨ψ, [A,B]ψ⟩
           = Real part      + i(Imaginary part)

where {A,B} = AB + BA is the anticommutator and [A,B] = AB - BA is the commutator.

The lemmas establish:
  1. Algebraic properties of complex numbers and real functions
  2. Self-adjointness is preserved under affine transformations
  3. Commutators have purely imaginary expectation values
  4. Anticommutators have purely real expectation values

These combine with Cauchy-Schwarz to yield the uncertainty bound.

References:
  - Robertson, H.P. (1929). "The Uncertainty Principle". Phys. Rev. 34, 163
  - Griffiths, D.J. "Introduction to Quantum Mechanics" Section 3.5
  - Hall, B.C. "Quantum Theory for Mathematicians" Chapter 9
-/
namespace Robertson.Lemmas

open InnerProductSpace MeasureTheory Complex
open scoped BigOperators

/-============================================================================
  SECTION 1: ALGEBRAIC FOUNDATIONS
============================================================================-/

/-
These lemmas establish basic algebraic properties needed throughout the proof.
They may seem elementary, but having them explicitly proven ensures our
uncertainty derivation is completely rigorous.
-/

/--
A complex number is purely imaginary if and only if its real part is zero.

Mathematical significance: A complex number z is purely imaginary when z = -z*.
This characterization is crucial for understanding commutator expectation values,
which are always purely imaginary for self-adjoint operators.

Application in Robertson's proof: We use this to show that ⟨ψ, [A,B]ψ⟩ is
purely imaginary, which means |⟨ψ, [A,B]ψ⟩| = |Im⟨ψ, [A,B]ψ⟩|.
-/
lemma star_eq_neg_iff_re_eq_zero (z : ℂ) : star z = -z ↔ z.re = 0 := by
  -- Expand the complex conjugate: if z = a + bi, then z* = a - bi
  -- So z* = -z means (a - bi) = -(a + bi) = -a - bi
  -- This gives us a = -a, which implies a = 0
  simp [Complex.ext_iff]
  constructor
  · intro h
    -- From z.re = -z.re, we get 2·z.re = 0, thus z.re = 0
    linarith
  · intro h
    -- If z.re = 0, then clearly 0 = -0
    rw [h]
    simp

/--
Monotonicity of squaring for non-negative real numbers.

Mathematical note: This is only true for non-negative numbers!
For negative numbers, the inequality reverses: if x < y < 0, then x² > y².

Application in Robertson's proof: Used when establishing that
variance (which involves squares) preserves certain inequalities.
This is particularly important when applying Cauchy-Schwarz and
needing to take square roots while preserving the inequality direction.
-/
lemma pow_le_pow_of_le_left {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x^2 ≤ y^2 := by
  -- We prove x² ≤ y² by factoring through x² ≤ xy ≤ y²
  -- This leverages the fact that multiplication by non-negative numbers preserves inequalities
  calc
    x^2 = x * x       := by rw [pow_two]
    _   ≤ x * y       := by
                          -- Since 0 ≤ x and x ≤ y, we have x·x ≤ x·y
                          apply mul_le_mul_of_nonneg_left
                          · exact hxy  -- The inequality x ≤ y
                          · exact hx   -- The non-negativity x ≥ 0
    _   ≤ y * y       := by
                          -- Since x ≤ y and 0 ≤ y (by transitivity), we have x·y ≤ y·y
                          apply mul_le_mul_of_nonneg_right
                          · exact hxy  -- The inequality x ≤ y
                          · exact le_trans hx hxy  -- y ≥ x ≥ 0, so y ≥ 0
    _   = y^2         := by rw [pow_two]

/-============================================================================
  SECTION 2: SELF-ADJOINTNESS PRESERVATION
============================================================================-/

/-
Self-adjoint operators are central to quantum mechanics as they represent
observables. These lemmas show that self-adjointness is preserved under
certain transformations, which is crucial when we shift operators by their
expectation values in the uncertainty proof.
-/

/--
Self-adjointness is preserved under affine transformations by real scalars.

Mathematical statement: If A is self-adjoint and λ ∈ ℝ, then A - λI is self-adjoint.

Physical interpretation: Shifting an observable by a real constant (like
subtracting its expectation value) gives another observable. This is why
we can work with Ã = A - ⟨A⟩I in the uncertainty proof.

Technical note: The domain D must be preserved under both A and scalar
multiplication. In practice, this is usually a dense subspace of the
Hilbert space.
-/
lemma isSelfAdjoint_sub_smul_of_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [IsScalarTower ℝ ℂ H] (A : H →ₗ[ℂ] H) (lambda : ℝ) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ) :
    ∀ v w, v ∈ D → w ∈ D → ⟪(A - lambda • 1) v, w⟫_ℂ = ⟪v, (A - lambda • 1) w⟫_ℂ := by
  intros v w hv hw
  -- Expand (A - λI) as pointwise operations
  show ⟪A v - lambda • v, w⟫_ℂ = ⟪v, A w - lambda • w⟫_ℂ

  -- Use linearity of inner product
  simp only [inner_sub_left, inner_sub_right]

  -- Use self-adjointness of A
  rw [hA_sa v w hv hw]

  -- The scalar terms need careful handling due to complex scalars
  ring_nf
  have h1 : ⟪lambda • v, w⟫_ℂ = ⟪(lambda : ℂ) • v, w⟫_ℂ := by congr 1
  have h2 : ⟪v, lambda • w⟫_ℂ = ⟪v, (lambda : ℂ) • w⟫_ℂ := by congr 1
  rw [h1, h2, inner_smul_left, inner_smul_right]

  -- For real λ, we have conj(λ) = λ
  simp only [Complex.conj_ofReal]

/-============================================================================
  SECTION 3: COMMUTATOR AND ANTICOMMUTATOR PROPERTIES
============================================================================-/

/-
The heart of Robertson's proof lies in decomposing the inner product
⟨Aψ, Bψ⟩ using commutators and anticommutators. These lemmas establish
the crucial properties that:
  - Commutator expectation values are purely imaginary
  - Anticommutator expectation values are purely real

This decomposition, combined with Cauchy-Schwarz, yields the uncertainty bound.
-/

/--
The expectation value of a commutator of self-adjoint operators is purely imaginary.

Mathematical insight: For self-adjoint A and B,
  ⟨ψ, [A,B]ψ⟩ = ⟨ψ, ABψ⟩ - ⟨ψ, BAψ⟩
              = ⟨Aψ, Bψ⟩ - ⟨Bψ, Aψ⟩
              = ⟨Aψ, Bψ⟩ - ⟨Aψ, Bψ⟩*

This difference of a complex number and its conjugate is purely imaginary.

Physical interpretation: The commutator [A,B] measures the "incompatibility"
of observables A and B. Its imaginary expectation value directly leads to
the uncertainty relation's lower bound.

Application in Robertson's proof: This shows that the uncertainty bound
|⟨[A,B]⟩|/2 comes from the imaginary part of ⟨Aψ, Bψ⟩.
-/
lemma expectation_commutator_re_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D_A D_B : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D_A → w ∈ D_A → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D_B → w ∈ D_B → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain_ψ_A : ψ ∈ D_A)
    (hdomain_ψ_B : ψ ∈ D_B)
    (hdomain_Bψ_A : B ψ ∈ D_A)
    (hdomain_Aψ_B : A ψ ∈ D_B) :
    (⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ).re = 0 := by
  -- Expand the commutator [A,B] = AB - BA
  simp_rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply]

  -- Use self-adjointness to move operators between sides of inner product
  -- ⟨ψ, ABψ⟩ = ⟨Aψ, Bψ⟩ and ⟨ψ, BAψ⟩ = ⟨Bψ, Aψ⟩
  rw [← hA_sa ψ (B ψ) hdomain_ψ_A hdomain_Bψ_A]
  rw [← hB_sa ψ (A ψ) hdomain_ψ_B hdomain_Aψ_B]

  -- Now we have ⟨Aψ, Bψ⟩ - ⟨Bψ, Aψ⟩ = ⟨Aψ, Bψ⟩ - ⟨Aψ, Bψ⟩*
  rw [← inner_conj_symm]
  rw [Complex.sub_re, Complex.conj_re]

  -- The real part of (z - z*) is Re(z) - Re(z*) = Re(z) - Re(z) = 0
  ring

/--
The expectation value of an anticommutator of self-adjoint operators is purely real.

Mathematical insight: For self-adjoint A and B,
  ⟨ψ, {A,B}ψ⟩ = ⟨ψ, ABψ⟩ + ⟨ψ, BAψ⟩
              = ⟨Aψ, Bψ⟩ + ⟨Bψ, Aψ⟩
              = ⟨Aψ, Bψ⟩ + ⟨Aψ, Bψ⟩*

This sum of a complex number and its conjugate is purely real.

Physical interpretation: The anticommutator {A,B} = AB + BA represents
the "compatible" part of the operators' composition. Unlike the commutator,
it doesn't directly contribute to the uncertainty bound.

Application in Robertson's proof: This separates the real and imaginary
parts of ⟨Aψ, Bψ⟩, allowing us to isolate the commutator contribution
that creates the uncertainty bound.
-/
lemma expectation_anticommutator_im_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D_A D_B : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D_A → w ∈ D_A → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D_B → w ∈ D_B → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain_ψ_A : ψ ∈ D_A)
    (hdomain_ψ_B : ψ ∈ D_B)
    (hdomain_Bψ_A : B ψ ∈ D_A)
    (hdomain_Aψ_B : A ψ ∈ D_B) :
    (⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ).im = 0 := by
  -- Expand the anticommutator {A,B} = AB + BA
  simp_rw [LinearMap.add_apply, inner_add_right, LinearMap.comp_apply]

  -- Use self-adjointness to move operators
  rw [← hA_sa ψ (B ψ) hdomain_ψ_A hdomain_Bψ_A]
  rw [← hB_sa ψ (A ψ) hdomain_ψ_B hdomain_Aψ_B]

  -- Now we have ⟨Aψ, Bψ⟩ + ⟨Bψ, Aψ⟩ = ⟨Aψ, Bψ⟩ + ⟨Aψ, Bψ⟩*
  rw [← inner_conj_symm]
  rw [Complex.add_im, Complex.conj_im]

  -- The imaginary part of (z + z*) is Im(z) + Im(z*) = Im(z) - Im(z) = 0
  ring


/-============================================================================
  SECTION 4: KEY DECOMPOSITION THEOREM
============================================================================-/

/-
This section contains the main decomposition theorem that combines
the above lemmas to show:

  ⟨Aψ, Bψ⟩ = (1/2)⟨ψ, {A,B}ψ⟩ + (i/2)⟨ψ, i[A,B]ψ⟩

where the first term is real and the second provides the uncertainty bound.
-/

/--
The fundamental decomposition of inner products for self-adjoint operators.

This is the key identity that enables Robertson's proof:
  2⟨Aψ, Bψ⟩ = ⟨ψ, {A,B}ψ⟩ + ⟨ψ, [A,B]ψ⟩
            = (real part) + (imaginary part)

From Cauchy-Schwarz: |⟨Aψ, Bψ⟩|² ≤ ‖Aψ‖² · ‖Bψ‖² = Var(A) · Var(B)

The imaginary part gives: |Im⟨Aψ, Bψ⟩| = (1/2)|⟨[A,B]⟩|

Therefore: Var(A) · Var(B) ≥ (1/4)|⟨[A,B]⟩|²

Taking square roots: σ_A · σ_B ≥ (1/2)|⟨[A,B]⟩|

This is Robertson's uncertainty relation!
-/
theorem inner_product_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (_ /-hB_sa-/ : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D) :
    2 * ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ + ⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ := by
  -- This follows from the algebraic identity: AB + BA + (AB - BA) = 2AB
  -- First, let's establish the algebraic fact
  have h_alg : ∀ (x y : ℂ), x + y + (x - y) = 2 * x := by
    intros x y
    ring

  -- Now apply this to our inner products
  -- Note that (A ∘ₗ B) ψ = A (B ψ) and similarly for B ∘ₗ A
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_add_right, inner_sub_right]

  -- We have: ⟪ψ, A (B ψ) + B (A ψ)⟫_ℂ + ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ
  -- = ⟪ψ, A (B ψ)⟫_ℂ + ⟪ψ, B (A ψ)⟫_ℂ + ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, B (A ψ)⟫_ℂ
  -- = 2 * ⟪ψ, A (B ψ)⟫_ℂ

  ring_nf

  -- Now we need to show ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ
  -- This follows from self-adjointness of A
  have h_adj : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2]

  rw [← h_adj]

/-============================================================================
  HELPER LEMMAS FOR CAUCHY-SCHWARZ APPLICATION
============================================================================-/

/-
Variance is non-negative for self-adjoint operators.

This seems obvious but needs proof: Var(A) = ⟨(A - ⟨A⟩I)²⟩ ≥ 0

The proof uses the fact that for self-adjoint operators,
⟨ψ, A²ψ⟩ = ⟨Aψ, Aψ⟩ = ‖Aψ‖² ≥ 0

lemma variance_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D) (hnorm : ‖ψ‖ = 1) :
    0 ≤ (⟪ψ, A (A ψ)⟫_ℂ - (⟪ψ, A ψ⟫_ℂ).re ^ 2).re := by

-/

/-============================================================================
  SECTION 5: DOMAIN PRESERVATION LEMMAS
============================================================================-/

/-
For unbounded operators (like position and momentum), we need to carefully
track domains. These lemmas ensure that the necessary operations preserve
the domain structure required for self-adjointness.
-/

/--
If ψ is in the domain of both A and B, and their commutator is defined,
then the shifted operators (A - ⟨A⟩I) preserve the domain structure
needed for the uncertainty relation.

Note: This is a simplified version. The actual statement would depend on
the specific domain conditions, which can be quite technical for unbounded
operators. In the bounded case, this is trivial since the domain is the
entire Hilbert space.
-/
lemma shifted_operator_domain_preservation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H) (μ : ℝ)
    (hdomain : ψ ∈ D) :
    (A - μ • (1 : H →ₗ[ℂ] H)) ψ ∈ D → A ψ ∈ D := by
  intro h_shifted

  -- We have (A - μI)ψ ∈ D
  -- This means Aψ - μψ ∈ D
  -- Since D is a submodule, ψ ∈ D implies μψ ∈ D
  have h_scaled : μ • ψ ∈ D := by
    -- D is closed under scalar multiplication
    have : (μ : ℂ) • ψ ∈ D := D.smul_mem (μ : ℂ) hdomain
    convert this
    -- μ as a real number coerced to ℂ acts the same as μ •
    --simp only [Complex.ofReal_eq_coe] <-- not needed, no goals to be solved

  -- Since D is closed under addition and (Aψ - μψ) ∈ D and μψ ∈ D
  -- we have Aψ = (Aψ - μψ) + μψ ∈ D
  have h_sum : (A - μ • (1 : H →ₗ[ℂ] H)) ψ + μ • ψ ∈ D := by
    exact D.add_mem h_shifted h_scaled

  -- Now we need to show that (A - μ • 1) ψ + μ • ψ = A ψ
  -- First, expand (A - μ • 1) ψ
  have h_expand : (A - μ • (1 : H →ₗ[ℂ] H)) ψ = A ψ - μ • ψ := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    simp

  -- Rewrite h_sum using this expansion
  rw [h_expand] at h_sum

  -- Now h_sum states: (A ψ - μ • ψ) + μ • ψ ∈ D
  -- This simplifies to A ψ ∈ D by cancellation
  have h_cancel : A ψ - μ • ψ + μ • ψ = A ψ := by
    abel  -- or use: simp only [sub_add_cancel]

  rw [← h_cancel]
  exact h_sum

/-============================================================================
  ADDITIONAL HELPER LEMMAS
============================================================================-/

/--
Helper lemma: The commutator of self-adjoint operators has purely imaginary
expectation values. This is a key ingredient in Robertson's proof.
-/
lemma commutator_expectation_imaginary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D ∧ A (B ψ) ∈ D ∧ B (A ψ) ∈ D) :
    (⟪ψ, (A ∘ₗ B - B ∘ₗ A) ψ⟫_ℂ).re = 0 := by
  -- This follows from the fact that [A,B]† = -[A,B] for self-adjoint A,B
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]

  -- Use self-adjointness to rewrite
  have h1 : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2.1]

  have h2 : ⟪ψ, B (A ψ)⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := by
    rw [hB_sa ψ (A ψ) hdomain.1 hdomain.2.1]

  rw [h1, h2]

  -- Now we have ⟪Aψ, Bψ⟫ - ⟪Bψ, Aψ⟫ = ⟪Aψ, Bψ⟫ - ⟪Aψ, Bψ⟫*
  rw [← inner_conj_symm (B ψ) (A ψ)]

  -- The real part of z - z* is 0
  simp only [Complex.sub_re, Complex.conj_re]
  ring

/--
The anticommutator of self-adjoint operators has real expectation values.
-/
lemma anticommutator_expectation_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ[ℂ] H) (ψ : H) (D : Submodule ℂ H)
    (hA_sa : ∀ v w, v ∈ D → w ∈ D → ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ)
    (hB_sa : ∀ v w, v ∈ D → w ∈ D → ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hdomain : ψ ∈ D ∧ A ψ ∈ D ∧ B ψ ∈ D ∧ A (B ψ) ∈ D ∧ B (A ψ) ∈ D) :
    (⟪ψ, (A ∘ₗ B + B ∘ₗ A) ψ⟫_ℂ).im = 0 := by
  -- The anticommutator {A,B} = AB + BA is self-adjoint when A and B are
  simp only [LinearMap.add_apply, LinearMap.comp_apply, inner_add_right]

  -- Use self-adjointness
  have h1 : ⟪ψ, A (B ψ)⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := by
    rw [hA_sa ψ (B ψ) hdomain.1 hdomain.2.2.1]

  have h2 : ⟪ψ, B (A ψ)⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := by
    rw [hB_sa ψ (A ψ) hdomain.1 hdomain.2.1]

  rw [h1, h2]

  -- Now we have ⟪Aψ, Bψ⟫ + ⟪Bψ, Aψ⟫ = ⟪Aψ, Bψ⟫ + ⟪Aψ, Bψ⟫*
  rw [← inner_conj_symm (B ψ) (A ψ)]

  -- The imaginary part of z + z* is 0
  simp only [Complex.add_im, Complex.conj_im]
  ring


end Robertson.Lemmas
