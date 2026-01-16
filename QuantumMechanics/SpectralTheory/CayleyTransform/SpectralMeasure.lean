/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.CayleyTransform.Spectrum

/-!
# Spectral Measures and the Cayley Transform

This file defines the Möbius image of sets and establishes the compatibility between
spectral measures of a self-adjoint operator `A` and its Cayley transform `U`.

## Main definitions

* `cayleyImage`: The Möbius image `{(μ - i)/(μ + i) | μ ∈ B}` of a set of reals
* `SpectralMeasuresCompatible`: Predicate asserting `E_A(B) = E_U(cayleyImage B)`

## Main statements

* `spectralMeasure_cayley_correspondence`: Compatible spectral measures satisfy
  `E_A(B) = E_U(cayleyImage B)`

## Dependencies

The *existence* of spectral measures for self-adjoint operators and their Cayley
transforms follows from the spectral theorem for bounded unitary operators
(Reed & Simon, Methods of Modern Mathematical Physics I, Theorem VIII.6).
This theorem is not yet formalized in Mathlib.

The results in this file are parameterized by spectral measures satisfying the
compatibility condition — they become fully instantiated once the spectral
theorem is available.
-/

namespace QuantumMechanics.Cayley

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators


    
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inverse Möbius image of a set of complex numbers. -/
def inverseCayleyImage (S : Set ℂ) : Set ℝ :=
  {μ : ℝ | (↑μ - I) * (↑μ + I)⁻¹ ∈ S}

/-- The inverse Möbius transformation, recovering μ from w. -/
noncomputable def inverseMobius (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The inverse Möbius map sends the unit circle (minus 1) to reals. -/
lemma inverseMobius_real (w : ℂ) (hw_norm : ‖w‖ = 1) (hw_ne : w ≠ 1) :
    (inverseMobius w).im = 0 := by
  simp only [inverseMobius]
  have h1_sub_ne : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  set a := w.re with ha
  set b := w.im with hb
  have hab : a^2 + b^2 = 1 := by
    have hw_normSq : normSq w = 1 := by
      exact Real.sqrt_eq_one.mp hw_norm
    have : normSq w = a^2 + b^2 := by simp [normSq, ha, hb, sq]
    rw [hw_normSq] at this
    linarith
  have h_normSq_ne : Complex.normSq (1 - w) ≠ 0 := by exact (map_ne_zero normSq).mpr h1_sub_ne
  have h_normSq_eq : Complex.normSq (1 - w) = (1 - a)^2 + b^2 := by
    simp only [Complex.normSq,MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, sub_re, one_re,
      sub_im, one_im, zero_sub, mul_neg, neg_mul, neg_neg]
    ring
  have h_denom_pos : (1 - a)^2 + b^2 > 0 := by
    rw [← h_normSq_eq]
    exact Complex.normSq_pos.mpr h1_sub_ne
  rw [div_eq_mul_inv, Complex.mul_im]
  simp only [Complex.inv_re, Complex.inv_im, Complex.mul_re, Complex.mul_im,
             Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
             Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
             ← ha, ← hb]
  simp only [zero_mul, one_mul, zero_add, zero_sub, neg_neg]
  rw [h_normSq_eq]
  field_simp [ne_of_gt h_denom_pos]
  nlinarith [sq_nonneg a, sq_nonneg b, hab]


/-- Möbius composed with inverse Möbius is identity on unit circle minus {1}. -/
lemma mobius_inverseMobius (w : ℂ) (_ /-hw_norm-/ : ‖w‖ = 1) (hw_ne : w ≠ 1) :
    (inverseMobius w - I) * (inverseMobius w + I)⁻¹ = w := by
  simp only [inverseMobius]
  have h1_sub_ne : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne)
  have hI_ne : (I : ℂ) ≠ 0 := I_ne_zero
  have h2I_ne : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero hI_ne
  have h_num : I * (1 + w) / (1 - w) - I = 2 * I * w / (1 - w) := by
    field_simp [h1_sub_ne]
    ring
  have h_denom : I * (1 + w) / (1 - w) + I = 2 * I / (1 - w) := by
    field_simp [h1_sub_ne]
    ring
  have h_denom_ne : 2 * I / (1 - w) ≠ 0 := div_ne_zero h2I_ne h1_sub_ne
  rw [h_num, h_denom]
  field_simp [h1_sub_ne, h2I_ne]


/-- Inverse Möbius composed with Möbius is identity on reals. -/
lemma inverseMobius_mobius (μ : ℝ) :
    inverseMobius ((↑μ - I) * (↑μ + I)⁻¹) = μ := by
  simp only [inverseMobius]
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := real_add_I_ne_zero μ
  have h1_sub_ne : 1 - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  field_simp [hμ_ne, h1_sub_ne]
  ring

/-- A complex number with zero imaginary part equals the coercion of its real part. -/
lemma Complex.eq_coe_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = ↑z.re := by
  exact ext rfl hz

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Möbius image of a set of reals under `μ ↦ (μ - i)/(μ + i)`. -/
def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

/-- Predicate asserting that spectral measures for `A` and `U` are compatible. -/
def SpectralMeasuresCompatible {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ B : Set ℝ, E_A B = E_U (cayleyImage B)

/-- Compatible spectral measures satisfy `E_A(B) = E_U(cayleyImage B)`. -/
theorem spectralMeasure_cayley_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H))
    (hcompat : SpectralMeasuresCompatible gen hsa E_A E_U)
    (B : Set ℝ) :
    E_A B = E_U (cayleyImage B) := hcompat B

/-- `cayleyImage` and `inverseCayleyImage` are inverses on the unit circle minus {1}. -/
lemma cayleyImage_inverseCayleyImage (S : Set ℂ) (hS : S ⊆ {w | ‖w‖ = 1 ∧ w ≠ 1}) :
    cayleyImage (inverseCayleyImage S) = S := by
  ext w
  constructor
  rintro ⟨μ, hμ_mem, rfl⟩
  exact hμ_mem

  intro hw
  obtain ⟨hw_norm, hw_ne⟩ := hS hw
  use (inverseMobius w).re
  have him : (inverseMobius w).im = 0 := inverseMobius_real w hw_norm hw_ne
  have hμ_eq : (↑(inverseMobius w).re : ℂ) = inverseMobius w :=
    (Complex.eq_coe_re_of_im_eq_zero him).symm
  have h_mobius_eq : (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹ = w := by
    calc (↑(inverseMobius w).re - I) * (↑(inverseMobius w).re + I)⁻¹
        = (inverseMobius w - I) * (inverseMobius w + I)⁻¹ := by rw [hμ_eq]
      _ = w := mobius_inverseMobius w hw_norm hw_ne
  constructor
  simp only [inverseCayleyImage, Set.mem_setOf_eq]
  rw [h_mobius_eq]
  exact hw

  exact h_mobius_eq.symm



end QuantumMechanics.Cayley
