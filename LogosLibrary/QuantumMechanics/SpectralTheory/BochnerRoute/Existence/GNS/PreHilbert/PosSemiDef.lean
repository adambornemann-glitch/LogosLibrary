/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: LogosLibrary/QuantumMechanics/SpectralTheory/BochnerRoute/Existence/GNS/PreHilbert/PosSemiDef.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.Conjugate

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §5  Positive semi-definiteness (requires PositiveDefinite)

/-- **Bridge lemma**: reindex a `pdInner` self-pairing as a `Fin N` double sum.

Given `α : ℝ →₀ ℂ` with `α.support.card = N`, we enumerate the support
via `α.support.equivFin` and express `⟨α, α⟩_f` as:

  `Σ_{j,k : Fin N} conj(c_j) · c_k · f(t_k - t_j)`

where `t_j` are the support points and `c_j = α(t_j)`. This is exactly
the quadratic form appearing in the `PositiveDefinite` condition. -/
lemma pdInner_self_eq_fin_sum (f : ℝ → ℂ) (α : ℝ →₀ ℂ) :
    pdInner f α α =
    let S := α.support
    let N := S.card
    let e := S.equivFin
    ∑ j : Fin N, ∑ k : Fin N,
      starRingEnd ℂ (α (e.symm j)) * (α (e.symm k)) *
      f ((e.symm k : ℝ) - (e.symm j : ℝ)) := by
  simp only [pdInner, Finsupp.sum]
  set S := α.support
  set e := S.equivFin
  have h_re : ∀ g : ℝ → ℂ, ∑ t ∈ S, g t = ∑ j : Fin S.card, g ↑(e.symm j) := by
    intro g
    rw [← Finset.sum_coe_sort S (f := g)]
    exact Fintype.sum_equiv e (fun i => g i) (fun j => g ↑(e.symm j))
      (fun i => by simp)
  -- Apply twice: once for the outer sum, once for each inner sum
  rw [h_re]; congr 1; ext j; exact h_re _


/-- **Positive semi-definiteness**: `0 ≤ Re ⟨α, α⟩_f` for all `α`.

This is the GNS counterpart of the `PositiveDefinite` condition:
the PD hypothesis gives non-negativity of finite quadratic forms,
and `⟨α, α⟩` is exactly such a form. -/
theorem pdInner_self_re_nonneg {f : ℝ → ℂ} (hPD : PositiveDefinite f) (α : ℝ →₀ ℂ) :
    0 ≤ (pdInner f α α).re := by
  rw [pdInner_self_eq_fin_sum]; dsimp only
  set e := α.support.equivFin
  have h := hPD α.support.card
    (fun j => -(↑(e.symm j) : ℝ))
    (fun j => α (e.symm j))
  convert h using 2
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  congr 1
  abel_nf


/-- The imaginary part of `⟨α, α⟩_f` vanishes (consequence of conjugate symmetry).

From `⟨α, α⟩ = conj ⟨α, α⟩` (self-conjugate), it follows that `⟨α, α⟩` is real.
This requires Hermitian symmetry of `f`. -/
lemma pdInner_self_im_eq_zero {f : ℝ → ℂ} (hH : IsHermitian f) (α : ℝ →₀ ℂ) :
    (pdInner f α α).im = 0 := by
  have h := pdInner_conj_symm hH α α
  have := congr_arg Complex.im h
  simp [Complex.conj_im] at this
  linarith

end SpectralBridge.Bochner.GNS
