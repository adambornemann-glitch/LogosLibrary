/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: .../BochnerRoute/Existence/GNS/PreHilbert.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Existence.GNS.PreHilbert.Cyclic

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp

-- §8  Norm estimates (for strong continuity in Completion.lean)


/-- The "norm squared" of a translate difference:
`‖U(t)ξ - ξ‖² = 2 Re(f(0)) - 2 Re(f(t))`.

This is the estimate that will give strong continuity once we
pass to the completion. The RHS → 0 as t → 0 by `ContinuousAt f 0`. -/
lemma pdInner_translate_diff_cyclic (f : ℝ → ℂ) (hH : IsHermitian f) (t : ℝ) :
    pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector) =
    2 * (f 0).re - f t - starRingEnd ℂ (f t) := by
  set ξ := cyclicVector
  set Uξ := translate t ξ
  have sub_right : ∀ α β γ : ℝ →₀ ℂ,
      pdInner f α (β - γ) = pdInner f α β - pdInner f α γ := by
    intro α β γ
    rw [sub_eq_add_neg, pdInner_add_right, show -γ = (-1 : ℂ) • γ from by ext; simp,
        pdInner_smul_right]; ring
  have sub_left : ∀ α β γ : ℝ →₀ ℂ,
      pdInner f (α - β) γ = pdInner f α γ - pdInner f β γ := by
    intro α β γ
    rw [sub_eq_add_neg, pdInner_add_left hH, show -β = (-1 : ℂ) • β from by ext; simp,
        pdInner_smul_left hH, map_neg, map_one, neg_one_mul]
    ring
  have h_ξξ : pdInner f ξ ξ = f 0 := by
    simp only [ξ, cyclicVector, pdInner_single_one, sub_self]
  rw [sub_left, sub_right, sub_right, pdInner_translate t ξ ξ,
      pdInner_conj_symm hH ξ Uξ, pdInner_cyclic f t, h_ξξ,
      hermitian_at_zero_ofReal hH]
  ring_nf; simp only [Nat.rawCast, Nat.cast_ofNat, ofReal_re]
  grind only


/-- Corollary: the "norm squared" of `U(t)ξ - ξ` is real and non-negative,
and equals `2(Re(f(0)) - Re(f(t)))`.

This is the form most directly useful for strong continuity:
it tends to 0 as t → 0 iff f is continuous at 0. -/
lemma pdInner_translate_diff_re {f : ℝ → ℂ}
    (_hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    (pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector)).re =
    2 * ((f 0).re - (f t).re) := by
  rw [pdInner_translate_diff_cyclic f hH t]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
             Complex.ofReal_im, Complex.conj_re]
  ring_nf; simp only [re_ofNat, sub_left_inj]
  grind only


/-- The difference norm is controlled by the variance `pdVariance`:

  Re⟨U(t)ξ - ξ, U(t)ξ - ξ⟩ = 2 · pdVariance f t

where `pdVariance f t = f(0).re - Re(f(t))` is from `Continuity.lean`.
This connects directly to the oscillation estimates already proved. -/
theorem pdInner_translate_diff_eq_variance {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    (pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector)).re =
    2 * pdVariance f t := by
  rw [pdInner_translate_diff_re hPD hH]
  unfold pdVariance
  exact (mul_right_inj_of_invertible 2).mpr rfl


end SpectralBridge.Bochner.GNS
