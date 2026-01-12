/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner

/-!
# Resolvent Theory for Self-Adjoint Generators

This file develops the resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint generators
of one-parameter unitary groups, establishing its key analytic properties.

## Main definitions

* `resolvent_at_i`: The resolvent at `z = i`, constructed via the self-adjointness criterion.
* `resolvent_at_neg_i`: The resolvent at `z = -i`.
* `resolvent`: The resolvent `R(z)` for any `z` with `Im(z) ≠ 0`.
* `resolventFun`: The resolvent as a function on `OffRealAxis`.
* `OffRealAxis`, `UpperHalfPlane`, `LowerHalfPlane`: Subtypes of `ℂ` for spectral regions.
* `neumannSeries`: The Neumann series `∑ Tⁿ` for `‖T‖ < 1`.

## Main statements

* `resolvent_at_i_unique`: Solutions to `(A - iI)ψ = φ` are unique.
* `lower_bound_estimate`: For `Im(z) ≠ 0`, we have `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖`.
* `self_adjoint_range_all_z`: For self-adjoint `A` and `Im(z) ≠ 0`, the equation
  `(A - zI)ψ = φ` has a unique solution for every `φ`.
* `resolvent_identity`: `R(z) - R(w) = (z - w) R(z) R(w)`.
* `resolvent_bound`: `‖R(z)‖ ≤ 1 / |Im(z)|`.
* `resolvent_adjoint`: `R(z)* = R(z̄)`.
* `resolventFun_hasSum`: Near `z₀`, the resolvent has power series
  `R(z) = ∑ₙ (z - z₀)ⁿ R(z₀)^{n+1}`.

## Implementation notes

* The resolvent is constructed via `LinearMap.mkContinuous` using the lower bound estimate.
* `self_adjoint_range_all_z` is proved by showing the range is closed (via the lower bound)
  and dense (via the orthogonal complement vanishing, which uses self-adjointness).
* The Neumann series machinery is developed independently to prove resolvent analyticity.
* We define `OffRealAxis` as a subtype to bundle the `Im(z) ≠ 0` hypothesis cleanly.

## Physics interpretation

The resolvent `R(z) = (H - zI)⁻¹` is central to scattering theory and spectral analysis.
The bound `‖R(z)‖ ≤ 1/|Im(z)|` shows the resolvent blows up as `z` approaches the real
axis (the spectrum). The resolvent identity encodes the semigroup property of time
evolution in the spectral domain.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995]
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.6

## TODO

* Factor `self_adjoint_range_all_z` into smaller lemmas.
* Prove strong resolvent convergence criteria.
* Connect to spectral measures via Stone's formula.
-/
namespace QuantumMechanics.Resolvent
open InnerProductSpace MeasureTheory Complex Filter Topology  QuantumMechanics.Bochner QuantumMechanics.Generators

set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


lemma resolvent_at_i_spec {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    ∃ (ψ : gen.domain), gen.op ψ - I • (ψ : H) = φ := by
  obtain ⟨ψ, hψ, h_eq⟩ := hsa.2 φ
  exact ⟨⟨ψ, hψ⟩, h_eq⟩


lemma resolvent_at_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁ = φ)
    (h₂ : gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_diff : gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁ - (gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂) = 0 := by
    rw [h₁, h₂]
    simp
  have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
  have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
  have h_factor : gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) - I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub (⟨ψ₁, hψ₁⟩ : gen.domain) (⟨ψ₂, hψ₂⟩ : gen.domain)
    simp only at op_sub
    calc gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) - I • (ψ₁ - ψ₂)
        = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - gen.op (⟨ψ₂, hψ₂⟩ : gen.domain)) - I • (ψ₁ - ψ₂) := by exact congrFun (congrArg HSub.hSub op_sub) (I • (ψ₁ - ψ₂))
      _ = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - gen.op (⟨ψ₂, hψ₂⟩ : gen.domain)) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁) - (gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂) := by abel
      _ = 0 := h_diff
  have h_eigen : gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) = I • (ψ₁ - ψ₂) := by
    exact sub_eq_zero.mp h_factor
  have h_inner : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]
    rfl
  have h_inner' : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = -I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner]
    simp only [Complex.conj_I]
  have h_sym : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)⟫_ℂ := by
    have := gen.symmetric (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)
    simp only at this
    expose_names
    exact this
  have h_real : (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im = 0 := by
    have eq_conj : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ := by
      calc ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ
          = ⟪ψ₁ - ψ₂, gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)⟫_ℂ := h_sym
        _ = (starRingEnd ℂ) ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ :=
            (inner_conj_symm (ψ₁ - ψ₂) (gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain))).symm
    have h_parts := Complex.ext_iff.mp eq_conj
    simp only [Complex.conj_im] at h_parts
    linarith [h_parts.2]
  have h_imag : (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im = -(‖ψ₁ - ψ₂‖ ^ 2) := by
    rw [h_inner']
    rw [mul_comm, Complex.mul_im]
    simp only [Complex.neg_re, Complex.neg_im,
              Complex.I_re, Complex.I_im, mul_zero, neg_zero]
    norm_cast
    ring_nf
    simp
  have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
    have h_eq : -(‖ψ₁ - ψ₂‖ ^ 2) = (0 : ℝ) := by
      calc -(‖ψ₁ - ψ₂‖ ^ 2) = (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
        _ = 0 := h_real
    linarith
  have : ‖ψ₁ - ψ₂‖ = 0 := by
    exact sq_eq_zero_iff.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)


lemma resolvent_solution_mem {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.2 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.2 φ))

lemma resolvent_solution_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.2 φ), resolvent_solution_mem gen hsa φ⟩ -
    I • Classical.choose (hsa.2 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.2 φ))


noncomputable def resolvent_at_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.2 φ)
  map_add' := fun φ₁ φ₂ => by
    let R₁ := Classical.choose (hsa.2 φ₁)
    let R₂ := Classical.choose (hsa.2 φ₂)
    let R_sum := Classical.choose (hsa.2 (φ₁ + φ₂))
    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem gen hsa (φ₁ + φ₂)
    have h₁_eq : gen.op ⟨R₁, h₁_mem⟩ - I • R₁ = φ₁ := resolvent_solution_eq gen hsa φ₁
    have h₂_eq : gen.op ⟨R₂, h₂_mem⟩ - I • R₂ = φ₂ := resolvent_solution_eq gen hsa φ₂
    have h_sum_eq : gen.op ⟨R_sum, h_sum_mem⟩ - I • R_sum = φ₁ + φ₂ :=
      resolvent_solution_eq gen hsa (φ₁ + φ₂)
    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem
    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      have op_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ = gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩ := by
        convert op_add using 1
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - I • (R₁ + R₂) := by rw [op_eq]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ - I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ - I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]
    exact (resolvent_at_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm
  map_smul' := fun c φ => by
    let R_φ := Classical.choose (hsa.2 φ)
    let R_scaled := Classical.choose (hsa.2 (c • φ))
    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem gen hsa (c • φ)
    have h_eq : gen.op ⟨R_φ, h_mem⟩ - I • R_φ = φ := resolvent_solution_eq gen hsa φ
    have h_scaled_eq : gen.op ⟨R_scaled, h_scaled_mem⟩ - I • R_scaled = c • φ :=
      resolvent_solution_eq gen hsa (c • φ)
    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem
    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      have op_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ = c • gen.op ⟨R_φ, h_mem⟩ := by
        convert op_smul using 1
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ - I • (c • R_φ) := by rw [op_eq]
        _ = c • gen.op ⟨R_φ, h_mem⟩ - c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ - I • R_φ) := by rw [smul_sub]
        _ = c • φ := by rw [h_eq]
    exact (resolvent_at_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm
  cont := by
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.2 φ)) := by
      intro φ₁ φ₂
      let ψ₁ := Classical.choose (hsa.2 φ₁)
      let ψ₂ := Classical.choose (hsa.2 φ₂)
      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
      have h₁_eq := resolvent_solution_eq gen hsa φ₁
      have h₂_eq := resolvent_solution_eq gen hsa φ₂
      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem
      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ =
                     gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩ := by
          convert op_sub using 1
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - I • (ψ₁ - ψ₂) := by rw [op_eq]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ - I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂
        have key_expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
                          ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          have expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
              ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖I • Δψ‖ ^ 2 -
              2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
            have h1 : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ)
              rw [this]; norm_cast
            have h2 : ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 = (⟪gen.op ⟨Δψ, h_sub_mem⟩, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩)
              rw [this]; norm_cast
            have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              rw [this]; norm_cast
            have h_cross : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re +
                           (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                           2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
              have h_eq : (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                          (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                        rw [inner_conj_symm]
                  _ = (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]; ring
            rw [h1, inner_sub_left, inner_sub_right, inner_sub_right]
            simp only [Complex.sub_re]
            rw [h2, h3, ← h_cross]
            ring
          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by
            rw [norm_smul]; simp
          have cross_zero : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re = 0 := by
            rw [inner_smul_right]
            have h_real : (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric ⟨Δψ, h_sub_mem⟩ ⟨Δψ, h_sub_mem⟩
              have h_conj : ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                            (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                calc ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ
                    = ⟪Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ := h_sym
                  _ = (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                      rw [inner_conj_symm]
              have := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at this
              linarith [this.2]
            have h1 : I * ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                      I * (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).re := by
              conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ]
              rw [h_real]; simp
            rw [h1, mul_comm]
            simp
          rw [expand, norm_I_smul, cross_zero]
          ring
        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 := by
          rw [key_expand]
          have : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 := sq_nonneg _
          linarith
        have le_norm : ‖Δψ‖ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := by
          have h_nonneg_left : 0 ≤ ‖Δψ‖ := norm_nonneg _
          have h_nonneg_right : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := norm_nonneg _
          by_contra h_not
          push_neg at h_not
          have : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖)]
          linarith
        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound
    exact lip.continuous


lemma resolvent_solution_mem_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.1 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.1 φ))

lemma resolvent_solution_eq_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.1 φ), resolvent_solution_mem_plus gen hsa φ⟩ +
    I • Classical.choose (hsa.1 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.1 φ))

lemma resolvent_at_neg_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ)
    (h₂ : gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂
  have h_diff : gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁ - (gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂) = 0 := by
    rw [h₁, h₂]; simp
  have h_factor : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩ := by
      convert op_sub using 1
    calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
        = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + I • (ψ₁ - ψ₂) := by rw [op_eq]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁) - (gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂) := by abel
      _ = 0 := h_diff
  have h_eigen : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = -I • (ψ₁ - ψ₂) := by
    have := add_eq_zero_iff_eq_neg.mp h_factor
    rw [← neg_smul] at this
    exact this
  have h_inner : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) (-I) * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]
    exact rfl
  have h_inner' : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner]; simp only [map_neg, Complex.conj_I, neg_neg]
  have h_sym : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩⟫_ℂ :=
    gen.symmetric ⟨ψ₁ - ψ₂, h_sub_mem⟩ ⟨ψ₁ - ψ₂, h_sub_mem⟩
  have h_real : (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im = 0 := by
    have eq_conj : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ =
                   (starRingEnd ℂ) ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ := by
      calc ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ
          = ⟪ψ₁ - ψ₂, gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩⟫_ℂ := h_sym
        _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ :=
            (inner_conj_symm (ψ₁ - ψ₂) (gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩)).symm
    have h_parts := Complex.ext_iff.mp eq_conj
    simp only [Complex.conj_im] at h_parts
    linarith [h_parts.2]
  have h_imag : (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im = ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner', mul_comm, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, mul_zero]
    norm_cast; ring_nf
  have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
    calc ‖ψ₁ - ψ₂‖ ^ 2 = (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
      _ = 0 := h_real
  have : ‖ψ₁ - ψ₂‖ = 0 := sq_eq_zero_iff.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)


noncomputable def resolvent_at_neg_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where
  toFun φ := Classical.choose (hsa.1 φ)
  map_add' := fun φ₁ φ₂ => by
    let R₁ := Classical.choose (hsa.1 φ₁)
    let R₂ := Classical.choose (hsa.1 φ₂)
    let R_sum := Classical.choose (hsa.1 (φ₁ + φ₂))
    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem_plus gen hsa (φ₁ + φ₂)
    have h₁_eq : gen.op ⟨R₁, h₁_mem⟩ + I • R₁ = φ₁ := resolvent_solution_eq_plus gen hsa φ₁
    have h₂_eq : gen.op ⟨R₂, h₂_mem⟩ + I • R₂ = φ₂ := resolvent_solution_eq_plus gen hsa φ₂
    have h_sum_eq : gen.op ⟨R_sum, h_sum_mem⟩ + I • R_sum = φ₁ + φ₂ :=
      resolvent_solution_eq_plus gen hsa (φ₁ + φ₂)
    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem
    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      have op_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ = gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩ := by
        convert op_add using 1
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + I • (R₁ + R₂) := by rw [op_eq]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ + I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]
    exact (resolvent_at_neg_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm
  map_smul' := fun c φ => by
    let R_φ := Classical.choose (hsa.1 φ)
    let R_scaled := Classical.choose (hsa.1 (c • φ))
    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem_plus gen hsa (c • φ)
    have h_eq : gen.op ⟨R_φ, h_mem⟩ + I • R_φ = φ := resolvent_solution_eq_plus gen hsa φ
    have h_scaled_eq : gen.op ⟨R_scaled, h_scaled_mem⟩ + I • R_scaled = c • φ :=
      resolvent_solution_eq_plus gen hsa (c • φ)
    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem
    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      have op_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ = c • gen.op ⟨R_φ, h_mem⟩ := by
        convert op_smul using 1
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ + I • (c • R_φ) := by rw [op_eq]
        _ = c • gen.op ⟨R_φ, h_mem⟩ + c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ + I • R_φ) := by rw [smul_add]
        _ = c • φ := by rw [h_eq]
    exact (resolvent_at_neg_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm
  cont := by
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.1 φ)) := by
      intro φ₁ φ₂
      let ψ₁ := Classical.choose (hsa.1 φ₁)
      let ψ₂ := Classical.choose (hsa.1 φ₂)
      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
      have h₁_eq := resolvent_solution_eq_plus gen hsa φ₁
      have h₂_eq := resolvent_solution_eq_plus gen hsa φ₂
      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem
      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩ := by
          convert op_sub using 1
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + I • (ψ₁ - ψ₂) := by rw [op_eq]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ + I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ + I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂
        have key_expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
                          ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          have expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
              ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖I • Δψ‖ ^ 2 +
              2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
            have h1 : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ)
              rw [this]; norm_cast
            have h2 : ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩)
              rw [this]; norm_cast
            have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              rw [this]; norm_cast
            have h_cross : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re +
                           (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                           2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
              have h_eq : (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                          (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                        rw [inner_conj_symm]
                  _ = (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]; ring
            rw [h1, inner_add_left, inner_add_right, inner_add_right]
            simp only [Complex.add_re]
            rw [h2, h3, ← h_cross]
            ring
          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by rw [norm_smul]; simp
          have cross_zero : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re = 0 := by
            rw [inner_smul_right]
            have h_real : (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric ⟨Δψ, h_sub_mem⟩ ⟨Δψ, h_sub_mem⟩
              have h_conj : ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                            (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                calc ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ
                    = ⟪Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ := h_sym
                  _ = (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                      rw [inner_conj_symm]
              have := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at this
              linarith [this.2]
            have h1 : I * ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                      I * (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).re := by
              conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ]
              rw [h_real]; simp
            rw [h1, mul_comm]
            simp
          rw [expand, norm_I_smul, cross_zero]
          ring
        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 := by
          rw [key_expand]
          have : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 := sq_nonneg _
          linarith
        have le_norm : ‖Δψ‖ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := by
          have h_nonneg_left : 0 ≤ ‖Δψ‖ := norm_nonneg _
          have h_nonneg_right : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := norm_nonneg _
          by_contra h_not
          push_neg at h_not
          have : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖)]
          linarith
        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound
    exact lip.continuous


lemma resolvent_at_i_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ‖resolvent_at_i gen hsa‖ ≤ 1 := by
  have h_bound : ∀ φ : H, ‖resolvent_at_i gen hsa φ‖ ≤ ‖φ‖ := by
    intro φ
    let ψ := resolvent_at_i gen hsa φ
    have h_mem : ψ ∈ gen.domain := resolvent_solution_mem gen hsa φ
    have h_eq : gen.op ⟨ψ, h_mem⟩ - I • ψ = φ := resolvent_solution_eq gen hsa φ
    have key_expand : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 = ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 + ‖ψ‖ ^ 2 := by
      have expand : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 =
          ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 + ‖I • ψ‖ ^ 2 - 2 * (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
        have h_inner : (⟪gen.op ⟨ψ, h_mem⟩ - I • ψ, gen.op ⟨ψ, h_mem⟩ - I • ψ⟫_ℂ).re =
            ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, h_mem⟩ - I • ψ)
          rw [this]; norm_cast
        rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
        simp only [Complex.sub_re]
        have h2 : ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, h_mem⟩, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, h_mem⟩)
          rw [this]; norm_cast
        have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
          rw [this]; norm_cast
        rw [h2, h3]
        have h_cross : (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re =
                      2 * (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
          have h_eq : (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
            calc (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re
                = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
              _ = (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
          rw [h_eq]; ring
        rw [h_cross.symm]; ring
      have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp
      have cross_zero : (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re = 0 := by
        rw [inner_smul_right]
        have h_real : (⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ).im = 0 := by
          have h_sym := gen.symmetric ⟨ψ, h_mem⟩ ⟨ψ, h_mem⟩
          have h_conj : ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ := by
            calc ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ
                = ⟪ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ := h_sym
              _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
          have := Complex.ext_iff.mp h_conj
          simp only [Complex.conj_im] at this
          linarith [this.2]
        have h1 : I * ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ = I * (⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ).re := by
          conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ]
          rw [h_real]; simp
        rw [h1, mul_comm]; simp
      rw [expand, norm_I_smul, cross_zero]; ring
    have le_sq : ‖ψ‖ ^ 2 ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 := by
      rw [key_expand]; have : 0 ≤ ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 := sq_nonneg _; linarith
    have le_norm : ‖ψ‖ ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := by
      by_contra h_not; push_neg at h_not
      have : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 < ‖ψ‖ ^ 2 := by
        have h1 : 0 ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := norm_nonneg _
        have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖ψ‖ - ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖)]
      linarith
    calc ‖ψ‖
        ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := le_norm
      _ = ‖φ‖ := by rw [h_eq]
  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro φ
    calc ‖resolvent_at_i gen hsa φ‖
        ≤ ‖φ‖ := h_bound φ
      _ = 1 * ‖φ‖ := by ring


lemma lower_bound_estimate {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (z : ℂ) (_ : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ - z • ψ‖ ≥ |z.im| * ‖ψ‖ := by
  set x := z.re
  set y := z.im
  have h_decomp : gen.op ⟨ψ, hψ⟩ - z • ψ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by
    have hz_eq : z = x + y * I := by simp [x, y]
    calc gen.op ⟨ψ, hψ⟩ - z • ψ
        = gen.op ⟨ψ, hψ⟩ - (x + y * I) • ψ := by rw [hz_eq]
      _ = gen.op ⟨ψ, hψ⟩ - (x • ψ + (y * I) • ψ) := by rw [add_smul]; exact rfl
      _ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by abel
  rw [h_decomp]
  have h_expand : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 =
                ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
                2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
    have h_formula : ∀ (a b : H), ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * (⟪a, b⟫_ℂ).re := by
      intro a b
      have h_inner : (⟪a - b, a - b⟫_ℂ).re = ‖a - b‖ ^ 2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a - b)
        rw [this]; norm_cast
      rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      have h1 : (⟪a, a⟫_ℂ).re = ‖a‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) a
        rw [this]; norm_cast
      have h2 : (⟪b, b⟫_ℂ).re = ‖b‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) b
        rw [this]; norm_cast
      rw [h1, h2]
      have h_cross : (⟪a, b⟫_ℂ).re + (⟪b, a⟫_ℂ).re = 2 * (⟪a, b⟫_ℂ).re := by
        have : (⟪b, a⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
          calc (⟪b, a⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪a, b⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪a, b⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [this]; ring
      rw [h_cross.symm]; ring
    calc ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2
        = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 - 2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re :=
            h_formula (gen.op ⟨ψ, hψ⟩ - x • ψ) ((y * I) • ψ)
      _ = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 + 2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
          have : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re =
                 -(⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re := by
            rw [inner_neg_right]; simp only [Complex.neg_re]
          rw [this]; ring
  have h_norm_scale : ‖(y * I) • ψ‖ = |y| * ‖ψ‖ := by
    calc ‖(y * I) • ψ‖
        = ‖(y * I : ℂ)‖ * ‖ψ‖ := norm_smul _ _
      _ = |y| * ‖ψ‖ := by simp
  have h_cross_zero : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = 0 := by
    rw [inner_neg_right, inner_smul_right]
    have h_real : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).im = 0 := by
      rw [inner_sub_left]
      have h_Areal : (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ :=
                (inner_conj_symm ψ (gen.op ⟨ψ, hψ⟩)).symm
        have h_parts := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]
      have h_xreal : (⟪x • ψ, ψ⟫_ℂ).im = 0 := by
        have h_eq : x • ψ = (x : ℂ) • ψ := (RCLike.real_smul_eq_coe_smul x ψ).symm
        rw [h_eq, inner_smul_left]
        have h_inner_real : (⟪ψ, ψ⟫_ℂ).im = 0 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
          rw [this]; norm_cast
        simp [h_inner_real]
      simp [h_Areal, h_xreal]
    have h_as_real : ⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ = ((⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ), h_real]
      simp
    rw [h_as_real]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [I_re, mul_zero, zero_mul, neg_zero]
  have h_sq : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 ≥ (|y| * ‖ψ‖)^2 := by
    rw [h_expand, h_norm_scale, h_cross_zero]
    simp only [mul_zero, add_zero]
    have : 0 ≤ ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 := sq_nonneg _
    linarith
  by_contra h_not
  push_neg at h_not
  have h1 : 0 ≤ ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖ := norm_nonneg _
  have h2 : 0 ≤ |y| * ‖ψ‖ := by
    apply mul_nonneg
    · exact abs_nonneg _
    · exact norm_nonneg _
  nlinarith [sq_nonneg (|y| * ‖ψ‖ - ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖), h_sq, h_not, h1, h2]


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := by
          apply mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]

lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_norm]
    exact hT
  have h_bound : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => opNorm_pow_le T n
  have h_nonneg : ∀ n, 0 ≤ ‖T^n‖ := fun n => norm_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom h_nonneg h_bound

noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  Finset.sum (Finset.range n) (fun k => T^k)

lemma neumannPartialSum_mul (T : E →L[ℂ] E) (n : ℕ) :
    (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
    ContinuousLinearMap.id ℂ E - T^n := by
  induction n with
  | zero =>
    simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
    simp only [mul_zero]
    ext x : 1
    simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
  | succ n ih =>
    simp only [neumannPartialSum] at ih ⊢
    rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [ih]
    have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
    rw [h_id_eq]
    rw [sub_mul, one_mul]
    rw [← pow_succ']
    abel

lemma neumannPartialSum_cauchy (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    CauchySeq (neumannPartialSum T) := by
  apply cauchySeq_of_summable_dist
  have h_bound : ∀ n, dist (neumannPartialSum T n) (neumannPartialSum T (n + 1)) ≤ ‖T‖^n := by
    intro n
    simp only [neumannPartialSum, dist_eq_norm, Finset.sum_range_succ]
    rw [← norm_neg, neg_sub, add_sub_cancel_left]
    exact opNorm_pow_le T n
  apply Summable.of_nonneg_of_le
  · intro n; exact dist_nonneg
  · exact h_bound
  · exact summable_geometric_of_lt_one (norm_nonneg _) hT

noncomputable def neumannSeries (T : E →L[ℂ] E) (_ /-hT-/ : ‖T‖ < 1) : E →L[ℂ] E :=
  limUnder atTop (neumannPartialSum T)

lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E := by
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) := by
    exact (neumannPartialSum_cauchy T hT).tendsto_limUnder
  have h_mul_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 ((ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT)) := by
    exact Tendsto.const_mul (ContinuousLinearMap.id ℂ E - T) h_lim
  have h_eq : ∀ n, (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
      ContinuousLinearMap.id ℂ E - T^n := neumannPartialSum_mul T
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E - 0)) := by
    exact Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
  simp only [sub_zero] at h_sub_lim
  have h_eq_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_eq]
    exact h_sub_lim
  exact tendsto_nhds_unique h_mul_lim h_eq_lim

lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E := by
  have h_telescope : ∀ n, neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T) =
      ContinuousLinearMap.id ℂ E - T^n := by
    intro n
    induction n with
    | zero =>
      simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
      simp only [zero_mul]
      ext x : 1
      simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
    | succ n ih =>
      simp only [neumannPartialSum] at ih ⊢
      rw [Finset.sum_range_succ]
      rw [add_mul]
      rw [ih]
      have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
      rw [h_id_eq]
      rw [mul_sub, mul_one]
      rw [← pow_succ]
      abel
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    (neumannPartialSum_cauchy T hT).tendsto_limUnder
  have h_mul_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T))) := by
    exact Tendsto.mul_const (ContinuousLinearMap.id ℂ E - T) h_lim
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    have := Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
    simp only [sub_zero] at this
    exact this
  have h_eq_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_telescope]
    exact h_sub_lim
  exact tendsto_nhds_unique h_mul_lim h_eq_lim

lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) := by
  refine ⟨⟨ContinuousLinearMap.id ℂ E - T, neumannSeries T hT, ?_, ?_⟩, rfl⟩
  · exact neumannSeries_mul_left T hT
  · exact neumannSeries_mul_right T hT

lemma resolvent_near_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im > 0) (h_close : ‖z - I‖ < 1) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ
  let R := resolvent_at_i gen hsa
  let lambda_val := z - I
  have h_op_bound : ‖lambda_val • R‖ < 1 := by
    calc ‖lambda_val • R‖
        = ‖lambda_val‖ * ‖R‖ := norm_smul lambda_val R
      _ ≤ ‖lambda_val‖ * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact resolvent_at_i_bound gen hsa
          · exact norm_nonneg _
      _ = ‖z - I‖ := by ring
      _ < 1 := h_close
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    let T := lambda_val • R
    let S := neumannSeries T h_op_bound
    let η := S φ
    let ψ_val := R η
    have h_ψ_mem : ψ_val ∈ gen.domain := resolvent_solution_mem gen hsa η
    have h_ψ_eq : gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val = η := resolvent_solution_eq gen hsa η
    use ⟨ψ_val, h_ψ_mem⟩
    have h_neumann_eq : η - T η = φ := by
      have h_inv := neumannSeries_mul_left T h_op_bound
      calc η - T η
          = (ContinuousLinearMap.id ℂ H - T) η := by simp [T]
        _ = ((ContinuousLinearMap.id ℂ H - T) * S) φ := by simp [η, S]
        _ = ContinuousLinearMap.id ℂ H φ := by rw [h_inv]
        _ = φ := rfl
    calc gen.op ⟨ψ_val, h_ψ_mem⟩ - z • ψ_val
        = gen.op ⟨ψ_val, h_ψ_mem⟩ - (I + lambda_val) • ψ_val := by simp [lambda_val]
      _ = gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val - lambda_val • ψ_val := by rw [add_smul]; abel
      _ = η - lambda_val • ψ_val := by rw [h_ψ_eq]
      _ = η - lambda_val • (R η) := rfl
      _ = η - (lambda_val • R) η := by rfl
      _ = η - T η := rfl
      _ = φ := h_neumann_eq
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'
  have h_sub_mem : (ψ : H) - (ψ' : H) ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property
  have h_diff : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H)) = 0 := by
    have op_sub := gen.op.map_sub ψ ψ'
    have op_eq : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ = gen.op ψ - gen.op ψ' := by
      convert op_sub using 1
    calc gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H))
        = (gen.op ψ - gen.op ψ') - z • ((ψ : H) - (ψ' : H)) := by rw [op_eq]
      _ = (gen.op ψ - gen.op ψ') - (z • (ψ : H) - z • (ψ' : H)) := by rw [smul_sub]
      _ = (gen.op ψ - z • (ψ : H)) - (gen.op ψ' - z • (ψ' : H)) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have h_im_ne : z.im ≠ 0 := ne_of_gt hz
  have h_bound := lower_bound_estimate gen z h_im_ne ((ψ : H) - (ψ' : H)) h_sub_mem
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound
  have h_im_pos : 0 < |z.im| := abs_pos.mpr h_im_ne
  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith
  have h_eq : (ψ : H) = (ψ' : H) := sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  exact Subtype.ext h_eq.symm


theorem self_adjoint_range_all_z
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ
  have h_ker_zero : ∀ (χ : H),
      (∀ (ψ : gen.domain), ⟪gen.op ψ - z • (ψ : H), χ⟫_ℂ = 0) → χ = 0 := by
    intro χ h_orth
    have h_eigen_cond : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
        ⟪gen.op ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by
      intro ψ hψ
      have h := h_orth ⟨ψ, hψ⟩
      simp only at h
      calc ⟪gen.op ⟨ψ, hψ⟩, χ⟫_ℂ
          = ⟪gen.op ⟨ψ, hψ⟩ - z • ψ + z • ψ, χ⟫_ℂ := by simp
        _ = ⟪gen.op ⟨ψ, hψ⟩ - z • ψ, χ⟫_ℂ + ⟪z • ψ, χ⟫_ℂ := by rw [inner_add_left]
        _ = 0 + ⟪z • ψ, χ⟫_ℂ := by rw [h]
        _ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by rw [inner_smul_left]; ring
    set z_bar := (starRingEnd ℂ) z with hz_bar_def
    obtain ⟨η, hη_dom, hη_eq⟩ := hsa.2 ((z_bar - I) • χ)
    obtain ⟨ξ, hξ_dom, hξ_eq⟩ := hsa.1 ((z_bar + I) • χ)
    have h_Aη : gen.op ⟨η, hη_dom⟩ = (z_bar - I) • χ + I • η := by
      calc gen.op ⟨η, hη_dom⟩
          = (gen.op ⟨η, hη_dom⟩ - I • η) + I • η := by simp
        _ = (z_bar - I) • χ + I • η := by rw [hη_eq]
    have h_eigen_η : ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ = z_bar * ⟪η, χ⟫_ℂ := h_eigen_cond η hη_dom
    have h_inner_Aη : ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ =
        (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
      calc ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, χ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, χ⟫_ℂ + ⟪I • η, χ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, χ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]; simp
    have h_conj_zbar_minus_I : (starRingEnd ℂ) (z_bar - I) = z + I := by
      simp [hz_bar_def]
    have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I
    have h_relation_η : (z_bar + I) * ⟪η, χ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      have h1 := h_eigen_η
      have h2 := h_inner_Aη
      rw [h_conj_zbar_minus_I, h_conj_I] at h2
      calc (z_bar + I) * ⟪η, χ⟫_ℂ
          = z_bar * ⟪η, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by ring
        _ = ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by rw [h1]
        _ = ((z + I) * ‖χ‖^2 + (-I) * ⟪η, χ⟫_ℂ) + I * ⟪η, χ⟫_ℂ := by rw [h2]
        _ = (z + I) * ‖χ‖^2 := by ring
    have h_Aξ : gen.op ⟨ξ, hξ_dom⟩ = (z_bar + I) • χ - I • ξ := by
      calc gen.op ⟨ξ, hξ_dom⟩
          = (gen.op ⟨ξ, hξ_dom⟩ + I • ξ) - I • ξ := by simp
        _ = (z_bar + I) • χ - I • ξ := by rw [hξ_eq]
    have h_eigen_ξ : ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ = z_bar * ⟪ξ, χ⟫_ℂ := h_eigen_cond ξ hξ_dom
    have h_inner_Aξ : ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ =
        (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
      calc ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ
          = ⟪(z_bar + I) • χ - I • ξ, χ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪(z_bar + I) • χ, χ⟫_ℂ - ⟪I • ξ, χ⟫_ℂ := by rw [inner_sub_left]
        _ = (starRingEnd ℂ) (z_bar + I) * ⟪χ, χ⟫_ℂ - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]; simp
    have h_conj_zbar_plus_I : (starRingEnd ℂ) (z_bar + I) = z - I := by
      simp [hz_bar_def]; ring
    have h_relation_ξ : (z_bar - I) * ⟪ξ, χ⟫_ℂ = (z - I) * ‖χ‖^2 := by
      have h1 := h_eigen_ξ
      have h2 := h_inner_Aξ
      rw [h_conj_zbar_plus_I, h_conj_I] at h2
      calc (z_bar - I) * ⟪ξ, χ⟫_ℂ
          = z_bar * ⟪ξ, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by ring
        _ = ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by rw [h1]
        _ = ((z - I) * ‖χ‖^2 - (-I) * ⟪ξ, χ⟫_ℂ) - I * ⟪ξ, χ⟫_ℂ := by rw [h2]
        _ = (z - I) * ‖χ‖^2 := by ring
    have h_sym : ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ = ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ :=
      gen.symmetric ⟨η, hη_dom⟩ ⟨ξ, hξ_dom⟩
    have h_LHS : ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, ξ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, ξ⟫_ℂ + ⟪I • η, ξ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, ξ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, ξ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ + (-I) * ⟪η, ξ⟫_ℂ := by rw [h_conj_zbar_minus_I, h_conj_I]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by ring
    have h_RHS : ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ
          = ⟪η, (z_bar + I) • χ - I • ξ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪η, (z_bar + I) • χ⟫_ℂ - ⟪η, I • ξ⟫_ℂ := by rw [inner_sub_right]
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by rw [inner_smul_right, inner_smul_right]
    have h_cancel : (z + I) * ⟪χ, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ := by
      have h : (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
        rw [← h_LHS, ← h_RHS, h_sym]
      calc (z + I) * ⟪χ, ξ⟫_ℂ
          = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by ring
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by rw [h]
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ := by ring
    have h_chi_xi_eq : (z + I) * ⟪χ, ξ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      calc (z + I) * ⟪χ, ξ⟫_ℂ
          = (z_bar + I) * ⟪η, χ⟫_ℂ := h_cancel
        _ = (z + I) * ‖χ‖^2 := h_relation_η
    by_cases h_z_eq_neg_I : z = -I
    ·
      have h_zbar_eq : z_bar = I := by
        simp only [hz_bar_def, h_z_eq_neg_I, map_neg, Complex.conj_I]; ring
      have h_zbar_minus_I : z_bar - I = 0 := by rw [h_zbar_eq]; ring
      have h_z_minus_I : z - I = -2 * I := by rw [h_z_eq_neg_I]; ring
      rw [h_zbar_minus_I, h_z_minus_I] at h_relation_ξ
      simp only [zero_mul] at h_relation_ξ
      have h_two_I_ne : (-2 : ℂ) * I ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, neg_eq_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true]
      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_relation_ξ.symm
        cases this with
        | inl h => exact absurd h h_two_I_ne
        | inr h => exact h
      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h
      exact norm_eq_zero.mp h_norm_zero
    ·
      have h_z_plus_i_ne : z + I ≠ 0 := by
        intro h_eq
        apply h_z_eq_neg_I
        calc z = z + I - I := by ring
          _ = 0 - I := by rw [h_eq]
          _ = -I := by ring
      have h_inner_chi_xi : ⟪χ, ξ⟫_ℂ = ‖χ‖^2 := by
        have := mul_left_cancel₀ h_z_plus_i_ne h_chi_xi_eq
        calc ⟪χ, ξ⟫_ℂ = (‖χ‖^2 : ℂ) := this
          _ = ‖χ‖^2 := by norm_cast
      have h_inner_xi_chi : ⟪ξ, χ⟫_ℂ = ‖χ‖^2 := by
        have h1 : ⟪ξ, χ⟫_ℂ = (starRingEnd ℂ) ⟪χ, ξ⟫_ℂ := (inner_conj_symm ξ χ).symm
        rw [h_inner_chi_xi] at h1
        simp at h1
        exact h1
      have h_final : (z_bar - I) * (‖χ‖^2 : ℂ) = (z - I) * ‖χ‖^2 := by
        calc (z_bar - I) * (‖χ‖^2 : ℂ)
            = (z_bar - I) * ⟪ξ, χ⟫_ℂ := by rw [← h_inner_xi_chi]
          _ = (z - I) * ↑‖χ‖^2 := h_relation_ξ
      have h_diff_zero : (z_bar - z) * (‖χ‖^2 : ℂ) = 0 := by
        have : (z_bar - I) * (‖χ‖^2 : ℂ) - (z - I) * ‖χ‖^2 = 0 := by
          rw [h_final]; ring
        calc (z_bar - z) * (‖χ‖^2 : ℂ)
            = (z_bar - I - (z - I)) * ‖χ‖^2 := by ring
          _ = (z_bar - I) * ‖χ‖^2 - (z - I) * ‖χ‖^2 := by ring
          _ = 0 := this
      have h_zbar_minus_z_ne : z_bar - z ≠ 0 := by
        intro h_eq
        have h_zbar_eq_z : z_bar = z := sub_eq_zero.mp h_eq
        have h_im_zero : z.im = 0 := by
          have h1 : ((starRingEnd ℂ) z).im = z.im := by
            rw [hz_bar_def] at h_zbar_eq_z
            exact congrArg Complex.im h_zbar_eq_z
          simp only [Complex.conj_im] at h1
          linarith
        exact hz h_im_zero
      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_diff_zero
        cases this with
        | inl h => exact absurd h h_zbar_minus_z_ne
        | inr h => exact h
      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h
      exact norm_eq_zero.mp h_norm_zero
  have h_range_closed : IsClosed (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro u φ_lim hu_range hφ_lim
    have hu_cauchy : CauchySeq u := hφ_lim.cauchySeq
    choose ψ_seq hψ_seq using fun n => Set.mem_range.mp (hu_range n)
    have hψ_cauchy : CauchySeq (fun n => (ψ_seq n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hε_scaled : 0 < |z.im| * ε := mul_pos (abs_pos.mpr hz) hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu_cauchy (|z.im| * ε) hε_scaled
      use N
      intro m hm n hn
      have h_sub_mem : (ψ_seq m : H) - (ψ_seq n : H) ∈ gen.domain :=
        gen.domain.sub_mem (ψ_seq m).property (ψ_seq n).property
      have h_bound := lower_bound_estimate gen z hz ((ψ_seq m : H) - (ψ_seq n : H)) h_sub_mem
      have h_diff : gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
                    z • ((ψ_seq m : H) - (ψ_seq n : H)) = u m - u n := by
        have op_sub := gen.op.map_sub (ψ_seq m) (ψ_seq n)
        have op_eq : gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ =
                     gen.op (ψ_seq m) - gen.op (ψ_seq n) := by
          convert op_sub using 1
        calc gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ - z • ((ψ_seq m : H) - (ψ_seq n : H))
            = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - z • ((ψ_seq m : H) - (ψ_seq n : H)) := by rw [op_eq]
          _ = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - (z • (ψ_seq m : H) - z • (ψ_seq n : H)) := by
              rw [smul_sub]
          _ = (gen.op (ψ_seq m) - z • (ψ_seq m : H)) - (gen.op (ψ_seq n) - z • (ψ_seq n : H)) := by abel
          _ = u m - u n := by rw [hψ_seq m, hψ_seq n]
      rw [h_diff] at h_bound
      have h_ubound : dist (u m) (u n) < |z.im| * ε := hN m hm n hn
      rw [dist_eq_norm] at h_ubound
      have h_chain : |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖ < |z.im| * ε := by
        calc |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖
            ≤ ‖u m - u n‖ := h_bound
          _ < |z.im| * ε := h_ubound
      have h_pos : 0 < |z.im| := abs_pos.mpr hz
      rw [dist_eq_norm]
      exact (mul_lt_mul_left h_pos).mp h_chain
    obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy
    let R := resolvent_at_i gen hsa
    have h_AiI : ∀ n, gen.op (ψ_seq n) - I • (ψ_seq n : H) = u n + (z - I) • (ψ_seq n : H) := by
      intro n
      have h := hψ_seq n
      calc gen.op (ψ_seq n) - I • (ψ_seq n : H)
          = (gen.op (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := by
              rw [sub_smul]; abel
        _ = u n + (z - I) • (ψ_seq n : H) := by rw [h]
    have h_AiI_lim : Tendsto (fun n => gen.op (ψ_seq n) - I • (ψ_seq n : H))
                            atTop (𝓝 (φ_lim + (z - I) • ψ_lim)) := by
      have h1 : Tendsto u atTop (𝓝 φ_lim) := hφ_lim
      have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
        Tendsto.const_smul hψ_lim (z - I)
      have h3 : Tendsto (fun n => u n + (z - I) • (ψ_seq n : H)) atTop
                        (𝓝 (φ_lim + (z - I) • ψ_lim)) := Tendsto.add h1 h2
      convert h3 using 1
      ext n
      exact h_AiI n
    have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
                        R (gen.op ⟨ψ, hψ⟩ - I • ψ) = ψ := by
      intro ψ hψ
      let η := gen.op ⟨ψ, hψ⟩ - I • ψ
      have h_Rη_mem := resolvent_solution_mem gen hsa η
      have h_Rη_eq := resolvent_solution_eq gen hsa η
      exact resolvent_at_i_unique gen hsa η (R η) ψ h_Rη_mem hψ h_Rη_eq rfl
    have h_R_lim : Tendsto (fun n => R (gen.op (ψ_seq n) - I • (ψ_seq n : H)))
                          atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) :=
      R.continuous.tendsto _ |>.comp h_AiI_lim
    have h_R_eq : ∀ n, R (gen.op (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := by
      intro n
      exact h_R_inverse (ψ_seq n : H) (ψ_seq n).property
    have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := by
      convert h_R_lim using 1
      ext n
      exact (h_R_eq n).symm
    have h_ψ_lim_eq : ψ_lim = R (φ_lim + (z - I) • ψ_lim) :=
      tendsto_nhds_unique hψ_lim h_ψ_lim_alt
    have h_ψ_lim_domain : ψ_lim ∈ gen.domain := by
      rw [h_ψ_lim_eq]
      exact resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)
    have h_eq : gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim = φ_lim := by
      have h_AiI_ψ_lim : gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                          resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
                         I • R (φ_lim + (z - I) • ψ_lim) = φ_lim + (z - I) • ψ_lim :=
        resolvent_solution_eq gen hsa (φ_lim + (z - I) • ψ_lim)
      have h_op_eq : gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ =
                     gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                            resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ := by
        congr 1
        exact Subtype.ext h_ψ_lim_eq
      calc gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
          = gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                  resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
          z • R (φ_lim + (z - I) • ψ_lim) := by
            have h_smul : z • ψ_lim = z • R (φ_lim + (z - I) • ψ_lim) := by
              rw [h_ψ_lim_eq]
              exact
                congrArg (HSMul.hSMul z)
                  (congrArg (⇑R)
                    (congrArg (HAdd.hAdd φ_lim) (congrArg (HSMul.hSMul (z - I)) h_ψ_lim_eq)))
            rw [h_op_eq, h_smul]
        _ = (gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                    resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
            I • R (φ_lim + (z - I) • ψ_lim)) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          have hz_split : z • R (φ_lim + (z - I) • ψ_lim) =
                          I • R (φ_lim + (z - I) • ψ_lim) + (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
            rw [← add_smul]; congr 1; ring
          rw [hz_split]
          abel
        _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
            rw [h_AiI_ψ_lim]
        _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
        _ = φ_lim := by abel
    exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩
  have h_dense : Dense (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
    set S := Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) with hS_def
    let M : Submodule ℂ H := {
      carrier := S
      add_mem' := by
        intro a b ha hb
        obtain ⟨ψa, hψa⟩ := ha
        obtain ⟨ψb, hψb⟩ := hb
        refine ⟨⟨(ψa : H) + (ψb : H), gen.domain.add_mem ψa.property ψb.property⟩, ?_⟩
        have op_add := gen.op.map_add ψa ψb
        simp only [← hψa, ← hψb]
        calc gen.op ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
            = (gen.op ψa + gen.op ψb) - z • ((ψa : H) + (ψb : H)) := by
                congr 1
          _ = (gen.op ψa + gen.op ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
          _ = (gen.op ψa - z • (ψa : H)) + (gen.op ψb - z • (ψb : H)) := by abel
      zero_mem' := ⟨⟨0, gen.domain.zero_mem⟩, by
        simp only [smul_zero, sub_zero]
        exact gen.op.map_zero⟩
      smul_mem' := by
        intro c a ha
        obtain ⟨ψ, hψ⟩ := ha
        refine ⟨⟨c • (ψ : H), gen.domain.smul_mem c ψ.property⟩, ?_⟩
        have op_smul := gen.op.map_smul c ψ
        simp only [← hψ]
        calc gen.op ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
            = c • gen.op ψ - z • (c • (ψ : H)) := by
                congr 1
          _ = c • gen.op ψ - c • (z • (ψ : H)) := by rw [smul_comm z c]
          _ = c • (gen.op ψ - z • (ψ : H)) := by rw [smul_sub]
    }
    have hM_eq : (M : Set H) = S := rfl
    have h_M_orth : Mᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro χ hχ
      apply h_ker_zero χ
      intro ψ
      have h_mem : gen.op ψ - z • (ψ : H) ∈ M := ⟨ψ, rfl⟩
      exact Submodule.inner_right_of_mem_orthogonal h_mem hχ
    have h_M_top : M.topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      rw [h_M_orth]
      exact Submodule.bot_orthogonal_eq_top
    have h_M_dense : Dense (M : Set H) := by
      rw [dense_iff_closure_eq]
      have h_coe : closure (M : Set H) = (M.topologicalClosure : Set H) :=
        (Submodule.topologicalClosure_coe M).symm
      rw [h_coe, h_M_top]
      rfl
    rw [← hM_eq]
    exact h_M_dense
  have h_eq_univ : Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    have : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at this
    exact Set.mem_range.mp this
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'
  have h_sub_mem : (ψ : H) - (ψ' : H) ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property
  have h_diff : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H)) = 0 := by
    have op_sub := gen.op.map_sub ψ ψ'
    have op_eq : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ = gen.op ψ - gen.op ψ' := by
      convert op_sub using 1
    calc gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H))
        = (gen.op ψ - gen.op ψ') - z • ((ψ : H) - (ψ' : H)) := by rw [op_eq]
      _ = (gen.op ψ - gen.op ψ') - (z • (ψ : H) - z • (ψ' : H)) := by rw [smul_sub]
      _ = (gen.op ψ - z • (ψ : H)) - (gen.op ψ' - z • (ψ' : H)) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have h_bound := lower_bound_estimate gen z hz ((ψ : H) - (ψ' : H)) h_sub_mem
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound
  have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith
  rw [norm_sub_rev] at h_norm_zero
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero))


noncomputable def resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun φ =>
        let ψ : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
        (ψ : H)
      map_add' := fun φ₁ φ₂ => by
        have h₁ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₁).exists
        have h₂ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₂).exists
        have h_sum_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists
        have h_add_mem : ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                         ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H) ∈ gen.domain :=
          gen.domain.add_mem
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain).property
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain).property
        have h_add_eq : gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                                ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ -
                        z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                             ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) = φ₁ + φ₂ := by
          have op_add := gen.op.map_add
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain)
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)
          have op_eq : gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                               ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ =
                       gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                       gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) := by
            convert op_add using 1
          calc gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                       ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ -
               z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                    ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H))
              = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)) -
                z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by rw [op_eq]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)) -
                (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by rw [smul_add]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H)) +
                (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by abel
            _ = φ₁ + φ₂ := by rw [h₁, h₂]
        have h_eq : (Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists : gen.domain) =
                    ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).unique h_sum_eq h_add_eq
        calc ((Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists : gen.domain) : H)
            = (⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
               ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ : gen.domain) := by rw [h_eq]
          _ = ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
              ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H) := rfl
      map_smul' := fun c φ => by
        simp only [RingHom.id_apply]
        have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
        have h_scaled_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists
        have h_smul_mem : c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H) ∈ gen.domain :=
          gen.domain.smul_mem c (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain).property
        have h_smul_eq : gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ -
                         z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) = c • φ := by
          have op_smul := gen.op.map_smul c (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain)
          have op_eq : gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ =
                       c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) := by
            convert op_smul using 1
          calc gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ -
               z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H))
              = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [op_eq]
            _ = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                c • (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [smul_comm z c]
            _ = c • (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [smul_sub]
            _ = c • φ := by rw [h]
        have h_eq : (Classical.choose (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists : gen.domain) =
                    ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (c • φ)).unique h_scaled_eq h_smul_eq
        have h_val := congrArg (↑· : gen.domain → H) h_eq
        simp only at h_val
        exact h_val
    }
    (1 / |z.im|)
    (by
      intro φ
      have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
      have h_mem := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain).property
      have h_bound := lower_bound_estimate gen z hz
        ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H) h_mem
      rw [h] at h_bound
      have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
      calc ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)‖
          = (1 / |z.im|) * (|z.im| * ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)‖) := by field_simp
        _ ≤ (1 / |z.im|) * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_bound
            positivity
    )


theorem resolvent_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent gen z hz hsa - resolvent gen w hw hsa =
    (z - w) • ((resolvent gen z hz hsa).comp (resolvent gen w hw hsa)) := by
  ext φ
  let ψ_w_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa w hw φ).exists
  let ψ_w := (ψ_w_sub : H)
  have h_w_domain : ψ_w ∈ gen.domain := ψ_w_sub.property
  have h_w_eq : gen.op ψ_w_sub - w • ψ_w = φ := Classical.choose_spec (self_adjoint_range_all_z gen hsa w hw φ).exists
  let ψ_z_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  let ψ_z := (ψ_z_sub : H)
  have h_z_domain : ψ_z ∈ gen.domain := ψ_z_sub.property
  have h_z_eq : gen.op ψ_z_sub - z • ψ_z = φ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
  let η_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ_w).exists
  let η := (η_sub : H)
  have h_η_domain : η ∈ gen.domain := η_sub.property
  have h_η_eq : gen.op η_sub - z • η = ψ_w := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ_w).exists
  have h_Rz : resolvent gen z hz hsa φ = ψ_z := rfl
  have h_Rw : resolvent gen w hw hsa φ = ψ_w := rfl
  have h_Rz_ψw : resolvent gen z hz hsa ψ_w = η := rfl
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]
  have h_Az_ψw : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : gen.op ⟨ψ_w, h_w_domain⟩ = φ + w • ψ_w := by
      have h_eq : gen.op ⟨ψ_w, h_w_domain⟩ = gen.op ψ_w_sub := rfl
      calc gen.op ⟨ψ_w, h_w_domain⟩
          = (gen.op ψ_w_sub - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel
  have h_sum_domain : ψ_z + (w - z) • η ∈ gen.domain := by
    apply gen.domain.add_mem h_z_domain
    exact gen.domain.smul_mem (w - z) h_η_domain
  have h_sum_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    have op_add := gen.op.map_add ψ_z_sub ((w - z) • η_sub)
    have h_smul_mem : (w - z) • η ∈ gen.domain := gen.domain.smul_mem (w - z) h_η_domain
    have op_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ =
                 gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩ := by
      convert op_add using 1
    have op_smul := gen.op.map_smul (w - z) η_sub
    have op_smul_eq : gen.op ⟨(w - z) • η, h_smul_mem⟩ = (w - z) • gen.op η_sub := by
      convert op_smul using 1
    calc gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η)
        = (gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩) - z • (ψ_z + (w - z) • η) := by rw [op_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - z • (ψ_z + (w - z) • η) := by rw [op_smul_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - (z • ψ_z + z • ((w - z) • η)) := by rw [smul_add]
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - z • ((w - z) • η)) := by abel
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - (w - z) • (z • η)) := by rw [smul_comm z (w - z) η]
      _ = (gen.op ψ_z_sub - z • ψ_z) + (w - z) • (gen.op η_sub - z • η) := by rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]
  let target := φ + (w - z) • ψ_w
  have h_ψw_solves : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = target := h_Az_ψw
  have h_sum_solves : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η) = target := h_sum_eq
  have h_eq_vals : ψ_w = ψ_z + (w - z) • η := by
    have h1 : (⟨ψ_w, h_w_domain⟩ : gen.domain) = (⟨ψ_z + (w - z) • η, h_sum_domain⟩ : gen.domain) :=
      (self_adjoint_range_all_z gen hsa z hz target).unique h_ψw_solves h_sum_solves
    exact congrArg Subtype.val h1
  calc ψ_z - ψ_w
      = ψ_z - (ψ_z + (w - z) • η) := by rw [h_eq_vals]
    _ = -((w - z) • η) := by abel
    _ = (-(w - z)) • η := by rw [neg_smul]
    _ = (z - w) • η := by ring_nf


theorem resolvent_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent gen z hz hsa‖ ≤ 1 / |z.im| := by
  have h_pointwise : ∀ φ : H, ‖resolvent gen z hz hsa φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
    intro φ
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
    let ψ := (ψ_sub : H)
    have h_domain : ψ ∈ gen.domain := ψ_sub.property
    have h_eq : gen.op ψ_sub - z • ψ = φ :=
      Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
    have h_lower := lower_bound_estimate gen z hz ψ h_domain
    rw [h_eq] at h_lower
    have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
    have h_ψ_bound : ‖ψ‖ ≤ ‖φ‖ / |z.im| := by
      have h_mul : |z.im| * ‖ψ‖ ≤ ‖φ‖ := h_lower
      calc ‖ψ‖
          = (|z.im|)⁻¹ * (|z.im| * ‖ψ‖) := by field_simp
        _ ≤ (|z.im|)⁻¹ * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_mul
            exact inv_nonneg.mpr (abs_nonneg _)
        _ = ‖φ‖ / |z.im| := by rw [inv_mul_eq_div]
    have h_res_eq : resolvent gen z hz hsa φ = ψ := rfl
    calc ‖resolvent gen z hz hsa φ‖
        = ‖ψ‖ := by rw [h_res_eq]
      _ ≤ ‖φ‖ / |z.im| := h_ψ_bound
      _ = (1 / |z.im|) * ‖φ‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg
    · norm_num
    · exact abs_nonneg _
  · exact h_pointwise


theorem resolvent_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    (resolvent gen z hz hsa).adjoint =
    resolvent gen (starRingEnd ℂ z) (by simp only [Complex.conj_im, neg_ne_zero]; exact hz) hsa := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left]
  set z_bar := (starRingEnd ℂ) z with hz_bar_def
  have hz_bar : z_bar.im ≠ 0 := by rw [hz_bar_def]; simp only [Complex.conj_im, neg_ne_zero]; exact hz
  let ξ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ).exists
  let ξ := (ξ_sub : H)
  have hξ_domain : ξ ∈ gen.domain := ξ_sub.property
  have hξ_eq : gen.op ξ_sub - z • ξ = ψ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ).exists
  have hξ_def : resolvent gen z hz hsa ψ = ξ := rfl
  let η_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  let η := (η_sub : H)
  have hη_domain : η ∈ gen.domain := η_sub.property
  have hη_eq : gen.op η_sub - z_bar • η = φ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  have hη_def : resolvent gen z_bar hz_bar hsa φ = η := rfl
  rw [hξ_def, hη_def]
  have hAξ : gen.op ξ_sub = ψ + z • ξ := by
    calc gen.op ξ_sub = (gen.op ξ_sub - z • ξ) + z • ξ := by abel
      _ = ψ + z • ξ := by rw [hξ_eq]
  have hAη : gen.op η_sub = φ + z_bar • η := by
    calc gen.op η_sub = (gen.op η_sub - z_bar • η) + z_bar • η := by abel
      _ = φ + z_bar • η := by rw [hη_eq]
  have h_sym : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪η, gen.op ξ_sub⟫_ℂ := gen.symmetric η_sub ξ_sub
  have h_LHS : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪gen.op η_sub, ξ⟫_ℂ
        = ⟪φ + z_bar • η, ξ⟫_ℂ := by rw [hAη]
      _ = ⟪φ, ξ⟫_ℂ + ⟪z_bar • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = ⟪φ, ξ⟫_ℂ + (starRingEnd ℂ) z_bar • ⟪η, ξ⟫_ℂ := by rw [inner_smul_left]; exact rfl
      _ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by simp [hz_bar_def]
  have h_RHS : ⟪η, gen.op ξ_sub⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪η, gen.op ξ_sub⟫_ℂ
        = ⟪η, ψ + z • ξ⟫_ℂ := by rw [hAξ]
      _ = ⟪η, ψ⟫_ℂ + ⟪η, z • ξ⟫_ℂ := by rw [inner_add_right]
      _ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by rw [inner_smul_right] ; exact rfl
  have h_cancel : ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    rw [← h_LHS, ← h_RHS, h_sym]
  exact add_right_cancel h_cancel



def OffRealAxis : Type := {z : ℂ // z.im ≠ 0}

def UpperHalfPlane : Type := {z : ℂ // 0 < z.im}

def LowerHalfPlane : Type := {z : ℂ // z.im < 0}
instance : Coe UpperHalfPlane OffRealAxis where
  coe z := ⟨z.val, ne_of_gt z.property⟩
instance : Coe LowerHalfPlane OffRealAxis where
  coe z := ⟨z.val, ne_of_lt z.property⟩

noncomputable def resolventFun {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    OffRealAxis → (H →L[ℂ] H) :=
  fun z => resolvent gen z.val z.property hsa

theorem resolventFun_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : OffRealAxis) :
    ‖resolventFun gen hsa z‖ ≤ 1 / |z.val.im| :=
  resolvent_bound gen hsa z.val z.property

theorem resolventFun_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z w : OffRealAxis) :
    resolventFun gen hsa z - resolventFun gen hsa w =
    (z.val - w.val) • ((resolventFun gen hsa z).comp (resolventFun gen hsa w)) :=
  resolvent_identity gen hsa z.val w.val z.property w.property

theorem resolventFun_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : OffRealAxis) :
    (resolventFun gen hsa z).adjoint =
    resolventFun gen hsa ⟨starRingEnd ℂ z.val, by simp; exact z.property⟩ :=
  resolvent_adjoint gen hsa z.val z.property

theorem neumannSeries_summable (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Summable (fun n => T^n) := by
  have h_geom : Summable (fun n => ‖T‖^n) := summable_geometric_of_lt_one (norm_nonneg _) hT
  apply Summable.of_norm_bounded_eventually
  · exact h_geom
  · filter_upwards with n
    exact opNorm_pow_le T n

theorem tsum_eq_neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    ∑' n, T^n = neumannSeries T hT := by
  have h_summable := neumannSeries_summable T hT
  have h_cauchy := neumannPartialSum_cauchy T hT
  have h_tendsto_neumann : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    h_cauchy.tendsto_limUnder
  have h_tendsto_tsum : Tendsto (fun n => ∑ i ∈ Finset.range n, T^i) atTop (𝓝 (∑' n, T^n)) :=
    h_summable.hasSum.tendsto_sum_nat
  have h_eq_partial : (fun n => ∑ i ∈ Finset.range n, T^i) = neumannPartialSum T := by
    ext n
    simp only [neumannPartialSum]
  rw [h_eq_partial] at h_tendsto_tsum
  exact tendsto_nhds_unique h_tendsto_tsum h_tendsto_neumann

theorem neumannSeries_hasSum (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    HasSum (fun n => T^n) (neumannSeries T hT) := by
  rw [← tsum_eq_neumannSeries T hT]
  exact (neumannSeries_summable T hT).hasSum

lemma im_ne_zero_of_near {z₀ : ℂ} (_ /-hz₀-/ : z₀.im ≠ 0) {z : ℂ}
    (hz : ‖z - z₀‖ < |z₀.im|) : z.im ≠ 0 := by
  have h_im_diff : |z.im - z₀.im| ≤ ‖z - z₀‖ := abs_im_le_norm (z - z₀)
  have h_im_close : |z.im - z₀.im| < |z₀.im| := lt_of_le_of_lt h_im_diff hz
  intro hz_eq
  rw [hz_eq, zero_sub, abs_neg] at h_im_close
  exact lt_irrefl _ h_im_close


theorem resolventFun_hasSum {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z₀ : OffRealAxis) (z : ℂ) (hz : ‖z - z₀.val‖ < |z₀.val.im|) :
    ∃ (hz' : z.im ≠ 0),
    HasSum (fun n => (z - z₀.val)^n • (resolventFun gen hsa z₀)^(n+1))
           (resolvent gen z hz' hsa) := by
  have hz' : z.im ≠ 0 := im_ne_zero_of_near z₀.property hz
  use hz'
  set R₀ := resolventFun gen hsa z₀ with hR₀_def
  set T := (z - z₀.val) • R₀ with hT_def
  have hT_norm : ‖T‖ < 1 := by
    have h_smul_bound : ‖T‖ ≤ ‖z - z₀.val‖ * ‖R₀‖ := by
      simp only [hT_def]
      exact norm_smul_le (z - z₀.val) R₀
    have h_R₀_bound : ‖R₀‖ ≤ 1 / |z₀.val.im| := resolventFun_bound gen hsa z₀
    calc ‖T‖
        ≤ ‖z - z₀.val‖ * ‖R₀‖ := h_smul_bound
      _ ≤ ‖z - z₀.val‖ * (1 / |z₀.val.im|) := by
          apply mul_le_mul_of_nonneg_left h_R₀_bound (norm_nonneg _)
      _ = ‖z - z₀.val‖ / |z₀.val.im| := by ring
      _ < |z₀.val.im| / |z₀.val.im| := by
          apply div_lt_div_of_pos_right hz (abs_pos.mpr z₀.property)
      _ = 1 := div_self (ne_of_gt (abs_pos.mpr z₀.property))
  have h_neumann := neumannSeries_hasSum T hT_norm
  have h_comm : R₀.comp (resolvent gen z hz' hsa) =
              (resolvent gen z hz' hsa).comp R₀ := by
    have hR₀_eq : R₀ = resolvent gen z₀.val z₀.property hsa := rfl
    have h1 := resolvent_identity gen hsa z z₀.val hz' z₀.property
    have h2 := resolvent_identity gen hsa z₀.val z z₀.property hz'
    set Rz := resolvent gen z hz' hsa with hRz_def
    set Rz₀ := resolvent gen z₀.val z₀.property hsa with hRz₀_def
    have h_add : (Rz - Rz₀) + (Rz₀ - Rz) = 0 := by
      simp only [sub_add_sub_cancel, sub_self]
    rw [h1, h2] at h_add
    have h_factor : (z - z₀.val) • (Rz.comp Rz₀ - Rz₀.comp Rz) = 0 := by
      have h_neg : z₀.val - z = -(z - z₀.val) := by ring
      rw [h_neg, neg_smul] at h_add
      rw [← sub_eq_add_neg, ← smul_sub] at h_add
      exact h_add
    by_cases hzeq : z = z₀.val
    · simp only [hRz_def, hzeq]; exact rfl
    · have hz_sub_ne : z - z₀.val ≠ 0 := sub_ne_zero.mpr hzeq
      rw [smul_eq_zero] at h_factor
      cases h_factor with
      | inl h => exact absurd h hz_sub_ne
      | inr h => exact (eq_of_sub_eq_zero h).symm
  have h_resolvent_eq : resolvent gen z hz' hsa =
    R₀.comp (neumannSeries T hT_norm) := by
    set Rz := resolvent gen z hz' hsa with hRz_def
    have h_res_id := resolvent_identity gen hsa z₀.val z z₀.property hz'
    have h1 : Rz = R₀ + (z - z₀.val) • R₀.comp Rz := by
      have hsub : R₀ - Rz = (z₀.val - z) • R₀.comp Rz := h_res_id
      have hneg : (z₀.val - z) = -(z - z₀.val) := by ring
      rw [hneg, neg_smul] at hsub
      calc Rz = R₀ - (R₀ - Rz) := by abel
        _ = R₀ - (-((z - z₀.val) • R₀.comp Rz)) := by rw [hsub]
        _ = R₀ + (z - z₀.val) • R₀.comp Rz := by abel
    rw [h_comm] at h1
    have h2 : (z - z₀.val) • Rz.comp R₀ = Rz.comp T := by
      rw [hT_def, ContinuousLinearMap.comp_smul]
    rw [h2] at h1
    have h3 : Rz.comp (ContinuousLinearMap.id ℂ H - T) = R₀ := by
      have : Rz - Rz.comp T = R₀ := by exact sub_eq_iff_eq_add.mpr h1
      calc Rz.comp (ContinuousLinearMap.id ℂ H - T)
          = Rz.comp (ContinuousLinearMap.id ℂ H) - Rz.comp T := by rw [ContinuousLinearMap.comp_sub]
        _ = Rz - Rz.comp T := by rw [ContinuousLinearMap.comp_id]
        _ = R₀ := by exact this
    calc Rz = Rz.comp (ContinuousLinearMap.id ℂ H) := by rw [ContinuousLinearMap.comp_id]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T) * (neumannSeries T hT_norm)) := by
          rw [neumannSeries_mul_left T hT_norm]
      _ = Rz.comp ((ContinuousLinearMap.id ℂ H - T).comp (neumannSeries T hT_norm)) := rfl
      _ = (Rz.comp (ContinuousLinearMap.id ℂ H - T)).comp (neumannSeries T hT_norm) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = R₀.comp (neumannSeries T hT_norm) := by rw [h3]
  have h_term_eq : ∀ n, R₀.comp (T^n) = (z - z₀.val)^n • R₀^(n+1) := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_smul]
      simp_all only [ne_eq, zero_add, pow_one, R₀, T]
      rfl
    | succ n ih =>
      calc R₀.comp (T^(n+1))
          = R₀.comp (T^n * T) := by rw [pow_succ]
        _ = (R₀.comp (T^n)).comp T := by exact rfl
        _ = ((z - z₀.val)^n • R₀^(n+1)).comp T := by rw [ih]
        _ = (z - z₀.val)^n • (R₀^(n+1)).comp ((z - z₀.val) • R₀) := by
            rw [ContinuousLinearMap.smul_comp]
        _ = (z - z₀.val)^n • ((z - z₀.val) • (R₀^(n+1)).comp R₀) := by
            rw [ContinuousLinearMap.comp_smul]
        _ = (z - z₀.val)^n • ((z - z₀.val) • R₀^(n+2)) := by
            congr 2
        _ = (z - z₀.val)^(n+1) • R₀^(n+2) := by
            rw [smul_smul]
            congr 1
  rw [h_resolvent_eq]
  have h_comp_hasSum : HasSum (fun n => R₀.comp (T^n)) (R₀.comp (neumannSeries T hT_norm)) :=
    ((ContinuousLinearMap.compL ℂ H H H) R₀).hasSum h_neumann
  convert h_comp_hasSum using 1
  · ext n
    exact Eq.symm (DFunLike.congr (h_term_eq n) rfl)

theorem resolvent_at_neg_i_left_inverse {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    resolvent_at_neg_i gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = ψ := by
  set φ := gen.op ⟨ψ, hψ⟩ + I • ψ with hφ_def
  set χ := resolvent_at_neg_i gen hsa φ with hχ_def
  have hχ_mem : χ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
  have hχ_eq : gen.op ⟨χ, hχ_mem⟩ + I • χ = φ := resolvent_solution_eq_plus gen hsa φ
  have hψ_eq : gen.op ⟨ψ, hψ⟩ + I • ψ = φ := rfl
  exact resolvent_at_neg_i_unique gen hsa φ χ ψ hχ_mem hψ hχ_eq hψ_eq

end QuantumMechanics.Resolvent
