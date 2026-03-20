/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Existence/GNS/PreHilbert/Linearity.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.Evolution

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp


-- §3  Zero and linearity

/-- `⟨0, β⟩ = 0`. -/
lemma pdInner_zero_left (f : ℝ → ℂ) (β : ℝ →₀ ℂ) :
    pdInner f 0 β = 0 := by
  unfold pdInner; simp [Finsupp.sum]

/-- `⟨α, 0⟩ = 0`. -/
lemma pdInner_zero_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) :
    pdInner f α 0 = 0 := by
  unfold pdInner; simp [Finsupp.sum_zero_index]

/-- Linearity in the second argument: `⟨α, β₁ + β₂⟩ = ⟨α, β₁⟩ + ⟨α, β₂⟩`.

Proof: expand the inner sum using `Finsupp.sum_add_index`. -/
lemma pdInner_add_right (f : ℝ → ℂ) (α β₁ β₂ : ℝ →₀ ℂ) :
    pdInner f α (β₁ + β₂) = pdInner f α β₁ + pdInner f α β₂ := by
  simp only [pdInner]
  -- Step 1: split inner sum — need ∀ t ct so simp_rw can rewrite under the outer binder
  have h_inner : ∀ (t : ℝ) (ct : ℂ),
      (β₁ + β₂).sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) =
      β₁.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) +
      β₂.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) :=
    fun t ct => Finsupp.sum_add_index (fun s => by simp)
      (fun s d₁ d₂ => by ring_nf; simp only [implies_true])
  simp_rw [h_inner]
  -- Step 2: distribute outer α.sum over the pointwise addition
  simp only [Finsupp.sum]
  exact Finset.sum_add_distrib

/-- Scalar multiplication in the second argument: `⟨α, c • β⟩ = c · ⟨α, β⟩`.

Proof: `(c • β)(s) = c · β(s)`, so each term picks up a factor of `c`,
which factors out of the double sum. -/
lemma pdInner_smul_right (f : ℝ → ℂ) (α : ℝ →₀ ℂ) (c : ℂ) (β : ℝ →₀ ℂ) :
    pdInner f α (c • β) = c * pdInner f α β := by
  simp only [pdInner]
  -- Step 1: inner sum — peel c out of (c • β).sum using sum_smul_index
  have h_inner : ∀ (t : ℝ) (ct : ℂ),
      (c • β).sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) =
      c * β.sum (fun s ds => starRingEnd ℂ ct * ds * f (s - t)) := by
    intro t ct
    rw [Finsupp.sum_smul_index (fun s => by simp)]
    simp only [Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  -- Step 2: rewrite under the outer binder, then factor c out of the outer sum
  simp_rw [h_inner]
  simp only [Finsupp.sum, Finset.mul_sum]

end SpectralBridge.Bochner.GNS
