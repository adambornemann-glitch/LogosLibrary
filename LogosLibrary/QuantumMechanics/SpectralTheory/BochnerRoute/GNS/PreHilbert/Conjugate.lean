/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/PreHilbert/Conjugate.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.PreHilbert.Linearity

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §4  Conjugate symmetry (requires Hermitian)

/-- **Conjugate symmetry**: `⟨β, α⟩_f = conj ⟨α, β⟩_f`.

This is where the Hermitian condition `f(-t) = conj(f(t))` enters. -/
lemma pdInner_conj_symm {f : ℝ → ℂ} (hH : IsHermitian f) (α β : ℝ →₀ ℂ) :
    pdInner f β α = starRingEnd ℂ (pdInner f α β) := by
  simp only [pdInner, Finsupp.sum]
  rw [map_sum (starRingEnd ℂ)]
  simp_rw [map_sum (starRingEnd ℂ), map_mul, starRingEnd_self_apply]
  simp_rw [show ∀ s t : ℝ, starRingEnd ℂ (f (s - t)) = f (t - s) from
    fun s t => by rw [← hH (s - t), neg_sub]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

/-- Conjugate-linearity in the first argument (corollary of symmetry + linearity):
`⟨α₁ + α₂, β⟩ = ⟨α₁, β⟩ + ⟨α₂, β⟩`. -/
lemma pdInner_add_left {f : ℝ → ℂ} (hH : IsHermitian f) (α₁ α₂ β : ℝ →₀ ℂ) :
    pdInner f (α₁ + α₂) β = pdInner f α₁ β + pdInner f α₂ β := by
  rw [pdInner_conj_symm hH, pdInner_add_right, map_add,
      pdInner_conj_symm hH α₁, pdInner_conj_symm hH α₂]
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]

/-- Conjugate scalar multiplication in first argument:
`⟨c • α, β⟩ = c̄ · ⟨α, β⟩`. -/
lemma pdInner_smul_left {f : ℝ → ℂ} (hH : IsHermitian f) (c : ℂ) (α β : ℝ →₀ ℂ) :
    pdInner f (c • α) β = starRingEnd ℂ c * pdInner f α β := by
  rw [pdInner_conj_symm hH, pdInner_smul_right, map_mul,
      pdInner_conj_symm hH α]
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]

end SpectralBridge.Bochner.GNS
