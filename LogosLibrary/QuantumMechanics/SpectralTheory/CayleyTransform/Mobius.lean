/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The Möbius Map from ℝ to the Unit Circle

This file develops properties of the Möbius transformation `μ ↦ (μ - i)/(μ + i)` which
maps the real line bijectively onto the unit circle minus `{1}`.

## Main statements

* `real_add_I_ne_zero`: `μ + i ≠ 0` for real `μ`
* `mobius_norm_one`: The Möbius image of a real number has norm 1
* `one_sub_mobius`: Formula for `1 - (μ - i)/(μ + i)`
* `mobius_coeff_identity`: Key algebraic identity used in spectral correspondence
-/

namespace QuantumMechanics.Cayley

open Complex

variable (μ : ℝ)

/-- `μ + i ≠ 0` for any real `μ`. -/
lemma real_add_I_ne_zero : (↑μ : ℂ) + I ≠ 0 := by
  intro h
  have : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
  simp at this

/-- The Möbius map sends reals to the unit circle. -/
lemma mobius_norm_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 := by
  simp only [norm_mul, norm_inv]
  have h1 : ‖(↑μ : ℂ) - I‖ = ‖(↑μ : ℂ) + I‖ := by
    have h : starRingEnd ℂ ((↑μ : ℂ) + I) = (↑μ : ℂ) - I := by simp [Complex.ext_iff]
    rw [← h, RCLike.norm_conj]
  have h2 : ‖(↑μ : ℂ) + I‖ ≠ 0 := norm_ne_zero_iff.mpr hμ_ne
  field_simp [h2, h1]
  exact h1

/-- Variant of `mobius_norm_one` with the hypothesis inlined. -/
lemma mobius_norm_eq_one (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1 :=
  mobius_norm_one μ hμ_ne

/-- Formula for `1 - w` where `w` is the Möbius image. -/
lemma one_sub_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/-- Formula for `1 + w` where `w` is the Möbius image. -/
lemma one_add_mobius (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I) := by
  field_simp [hμ_ne]
  ring

/-- Key identity: `i(1 + w) = (1 - w)μ` for the Möbius image `w`. -/
lemma mobius_coeff_identity (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    let w := (↑μ - I) * (↑μ + I)⁻¹
    I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ := by
  simp only
  rw [one_sub_mobius μ hμ_ne, one_add_mobius μ hμ_ne]
  field_simp [hμ_ne]

/-- `1 - w ≠ 0` for the Möbius image `w` of a real. -/
lemma one_sub_mobius_ne_zero (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0 := by
  rw [one_sub_mobius μ hμ_ne]
  simp [hμ_ne]

/-- `‖1 - w‖ > 0` for the Möbius image `w` of a real. -/
lemma one_sub_mobius_norm_pos (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0 :=
  norm_pos_iff.mpr (one_sub_mobius_ne_zero μ hμ_ne)

end QuantumMechanics.Cayley
