/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/PreHilbert/Evolution.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.PreHilbert.Defs

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §2  Evaluation on basis elements

/-- The zero-at-zero lemma needed for `Finsupp.sum_single_index`. -/
lemma pdInner_aux_zero (f : ℝ → ℂ) (β : ℝ →₀ ℂ) (t : ℝ) :
    (β.sum fun s ds => starRingEnd ℂ (0 : ℂ) * ds * f (s - t)) = 0 := by
  simp [map_zero, zero_mul, Finsupp.sum]

/-- Inner product of two point masses.

`⟨cₐ · δₐ, c_b · δ_b⟩_f = c̄ₐ · c_b · f(b - a)` -/
@[simp]
lemma pdInner_single_single (f : ℝ → ℂ) (a b : ℝ) (ca cb : ℂ) :
    pdInner f (Finsupp.single a ca) (Finsupp.single b cb) =
    starRingEnd ℂ ca * cb * f (b - a) := by
  unfold pdInner
  rw [Finsupp.sum_single_index (pdInner_aux_zero f _ a)]
  rw [Finsupp.sum_single_index (by simp [mul_zero])]

/-- Specialization: unit point masses. -/
lemma pdInner_single_one (f : ℝ → ℂ) (a b : ℝ) :
    pdInner f (Finsupp.single a 1) (Finsupp.single b 1) = f (b - a) := by
  simp [map_one]

end SpectralBridge.Bochner.GNS
