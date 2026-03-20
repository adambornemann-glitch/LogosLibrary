/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: .../BochnerRoute/Existence/GNS/PreHilbert/TransAction.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.PosSemiDef

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §6  The translation action

/-- Translation on a point mass: `U(t)(c · δ_s) = c · δ_{s+t}`. -/
@[simp]
lemma translate_single (t s : ℝ) (c : ℂ) :
    translate t (Finsupp.single s c) = Finsupp.single (s + t) c := by
  unfold translate
  exact Finsupp.mapDomain_single

/-- Translation is ℂ-linear. -/
lemma translate_add_right (t : ℝ) (α β : ℝ →₀ ℂ) :
    translate t (α + β) = translate t α + translate t β := by
  unfold translate
  exact Finsupp.mapDomain_add

lemma translate_smul (t : ℝ) (c : ℂ) (α : ℝ →₀ ℂ) :
    translate t (c • α) = c • translate t α := by
  unfold translate
  exact Finsupp.mapDomain_smul c α

/-- Identity: `U(0) = id`. -/
@[simp]
lemma translate_zero (α : ℝ →₀ ℂ) :
    translate 0 α = α := by
  unfold translate
  simp only [add_zero]
  ext x; exact mapDomain_apply (fun ⦃a₁ a₂⦄ a => a) α x


/-- Group law: `U(s)(U(t)(α)) = U(s + t)(α)`.

Proof: `mapDomain (· + s) ∘ mapDomain (· + t) = mapDomain (· + (t + s))`
since `(x + t) + s = x + (t + s)`. Then use `t + s = s + t`. -/
lemma translate_translate (s t : ℝ) (α : ℝ →₀ ℂ) :
    translate s (translate t α) = translate (s + t) α := by
  unfold translate
  rw [← @mapDomain_comp]
  congr 1; ext x
  ring_nf
  simp only [Function.comp_apply]
  linarith


/-- **Translation isometry**: `⟨U(t)α, U(t)β⟩_f = ⟨α, β⟩_f`.

The kernel `f(s - r)` is translation-invariant: `(s+t) - (r+t) = s - r`.
So translating both arguments does not change the inner product.

This is why `U(t)` extends to a unitary operator on the completion. -/
lemma pdInner_translate {f : ℝ → ℂ} (t : ℝ) (α β : ℝ →₀ ℂ) :
    pdInner f (translate t α) (translate t β) = pdInner f α β := by
  simp only [pdInner, translate]
  rw [Finsupp.sum_mapDomain_index
    (fun r => by simp [Finsupp.sum])
    (fun r c₁ c₂ => by
      simp only [Finsupp.sum, map_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _; ring)]
  have h_inner : ∀ (r : ℝ) (cr : ℂ),
      (mapDomain (· + t) β).sum (fun s ds => starRingEnd ℂ cr * ds * f (s - (r + t))) =
      β.sum (fun s ds => starRingEnd ℂ cr * ds * f (s - r)) := by
    intro r cr
    rw [Finsupp.sum_mapDomain_index (fun s => by simp) (fun s d₁ d₂ => by ring)]
    simp only [Finsupp.sum]
    apply Finset.sum_congr rfl; intro s _
    congr 1; congr 1; ring
  simp_rw [h_inner]


end SpectralBridge.Bochner.GNS
