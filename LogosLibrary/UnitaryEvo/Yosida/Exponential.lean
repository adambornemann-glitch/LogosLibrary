/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Yosida/Exponential.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Duhamel
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Symmetry
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.ExpBounded
import LogosLibrary.QuantumMechanics.UnitaryEvo.Yosida.Convergence
/-!
# The Exponential Map and Stone's Theorem (Converse)

This file constructs the exponential `exp(itA)` of a self-adjoint operator `A`
as the limit of Yosida approximants, and proves it forms a strongly continuous
one-parameter unitary group whose generator is `iA`.

This completes the converse direction of Stone's theorem: every self-adjoint
operator generates a strongly continuous unitary group.

## Main definitions

* `exponential`: The unitary group `exp(itA)` defined as the limit of `exp(it·Aₙˢʸᵐ)`

## Main results

* `exponential_tendsto`: The Yosida exponentials converge to `exponential`
* `exponential_unitary`: `exp(itA)` preserves inner products
* `exponential_group_law`: `exp(i(s+t)A) = exp(isA) ∘ exp(itA)`
* `exponential_identity`: `exp(i·0·A) = I`
* `exponential_strong_continuous`: `t ↦ exp(itA)ψ` is continuous
* `exponential_generator_eq`: The generator of `exp(itA)` is `iA`
* `exponential_derivative_on_domain`: Differentiability on the domain

## References

* [Kato, *Perturbation Theory*][kato1995], Section IX.1
* [Reed-Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.7

-/

namespace QuantumMechanics.Yosida

open Generators Complex Filter Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Definition of the exponential -/

/-- The exponential `exp(itA)` of a self-adjoint operator, constructed as the
    pointwise limit of Yosida approximant exponentials `exp(it·Aₙˢʸᵐ)`. -/
noncomputable def exponential
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H)) (t : ℝ) : H →L[ℂ] H where
  toFun ψ := limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
  map_add' := fun ψ₁ ψ₂ => by
    have h_add : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂) =
        expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
        expBounded (I • yosidaApproxSym gen hsa n) t ψ₂ :=
      fun n => map_add _ _ _
    have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₁)
    have h2 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₂)
    have h12 := cauchySeq_tendsto_of_complete
      (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (ψ₁ + ψ₂))
    obtain ⟨L1, hL1⟩ := h1
    obtain ⟨L2, hL2⟩ := h2
    obtain ⟨L12, hL12⟩ := h12
    have hLim1 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁) = L1 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L1, hL1⟩) hL1
    have hLim2 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) = L2 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L2, hL2⟩) hL2
    have hLim12 : limUnder atTop
        (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂)) = L12 :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L12, hL12⟩) hL12
    have hSum : Tendsto (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
                                  expBounded (I • yosidaApproxSym gen hsa n) t ψ₂)
                        atTop (𝓝 (L1 + L2)) :=
      hL1.add hL2
    simp_rw [← h_add] at hSum
    have : L12 = L1 + L2 := tendsto_nhds_unique hL12 hSum
    rw [hLim12, hLim1, hLim2, this]
  map_smul' := fun c ψ => by
    have h_smul : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ) =
        c • expBounded (I • yosidaApproxSym gen hsa n) t ψ :=
      fun n => map_smul _ _ _
    have h1 := cauchySeq_tendsto_of_complete (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
    have hc := cauchySeq_tendsto_of_complete
      (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (c • ψ))
    obtain ⟨L, hL⟩ := h1
    obtain ⟨Lc, hLc⟩ := hc
    have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
    have hLimC : limUnder atTop
        (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ)) = Lc :=
      tendsto_nhds_unique (tendsto_nhds_limUnder ⟨Lc, hLc⟩) hLc
    have hSmul : Tendsto (fun n => c • expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                         atTop (𝓝 (c • L)) :=
      tendsto_const_nhds.smul hL
    simp_rw [← h_smul] at hSmul
    have : Lc = c • L := tendsto_nhds_unique hLc hSmul
    rw [hLimC, hLim, this, RingHom.id_apply]
  cont := by
    apply continuous_of_linear_of_bound (𝕜 := ℂ)
    -- Additivity
    · intro ψ₁ ψ₂
      have h_add : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂) =
          expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
          expBounded (I • yosidaApproxSym gen hsa n) t ψ₂ :=
        fun n => map_add _ _ _
      have h1 := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₁)
      have h2 := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ₂)
      have h12 := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (ψ₁ + ψ₂))
      obtain ⟨L1, hL1⟩ := h1
      obtain ⟨L2, hL2⟩ := h2
      obtain ⟨L12, hL12⟩ := h12
      have hLim1 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁) = L1 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L1, hL1⟩) hL1
      have hLim2 : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₂) = L2 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L2, hL2⟩) hL2
      have hLim12 : limUnder atTop
          (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (ψ₁ + ψ₂)) = L12 :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L12, hL12⟩) hL12
      have hSum : Tendsto (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ₁ +
                                    expBounded (I • yosidaApproxSym gen hsa n) t ψ₂)
                          atTop (𝓝 (L1 + L2)) :=
        hL1.add hL2
      simp_rw [← h_add] at hSum
      have : L12 = L1 + L2 := tendsto_nhds_unique hL12 hSum
      rw [hLim12, hLim1, hLim2, this]
    -- Scalar multiplication
    · intro c ψ
      have h_smul : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ) =
          c • expBounded (I • yosidaApproxSym gen hsa n) t ψ :=
        fun n => map_smul _ _ _
      have h1 := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
      have hc := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t (c • ψ))
      obtain ⟨L, hL⟩ := h1
      obtain ⟨Lc, hLc⟩ := hc
      have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
      have hLimC : limUnder atTop
          (fun n => expBounded (I • yosidaApproxSym gen hsa n) t (c • ψ)) = Lc :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨Lc, hLc⟩) hLc
      have hSmul : Tendsto (fun n => c • expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                           atTop (𝓝 (c • L)) :=
        tendsto_const_nhds.smul hL
      simp_rw [← h_smul] at hSmul
      have : Lc = c • L := tendsto_nhds_unique hLc hSmul
      rw [hLimC, hLim, this]
    -- Bound: ‖f ψ‖ ≤ 1 * ‖ψ‖
    · intro ψ
      have h := cauchySeq_tendsto_of_complete
        (expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ)
      obtain ⟨L, hL⟩ := h
      have hLim : limUnder atTop (fun n => expBounded (I • yosidaApproxSym gen hsa n) t ψ) = L :=
        tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
      rw [hLim, one_mul]
      have h_norm : ∀ n : ℕ+, ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ = ‖ψ‖ := fun n => by
        have h_sa : ContinuousLinearMap.adjoint (yosidaApproxSym gen hsa n) =
            yosidaApproxSym gen hsa n :=
          yosidaApproxSym_selfAdjoint gen hsa n
        have h_skew : ContinuousLinearMap.adjoint (I • yosidaApproxSym gen hsa n) =
            -(I • yosidaApproxSym gen hsa n) :=
          smul_I_skewSelfAdjoint (A := yosidaApproxSym gen hsa n) h_sa
        have h_unitary := expBounded_mem_unitary (I • yosidaApproxSym gen hsa n) h_skew t
        exact Unitary.norm_map ⟨_, h_unitary⟩ ψ
      have h_tendsto_norm : Tendsto
          (fun n => ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖) atTop (𝓝 ‖L‖) :=
        tendsto_norm.comp hL
      simp_rw [h_norm] at h_tendsto_norm
      subst hLim
      simp_all only [tendsto_const_nhds_iff, le_refl]

/-! ### Convergence -/

lemma exponential_tendsto
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
            atTop (𝓝 (exponential gen hsa h_dense t ψ)) := by
  have h_cauchy := expBounded_yosidaApproxSym_cauchy gen hsa h_dense t ψ
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have h_eq : exponential gen hsa h_dense t ψ = L :=
    tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL
  rw [h_eq]
  exact hL

/-! ### Unitarity -/

theorem exponential_unitary
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ φ : H) :
    ⟪exponential gen hsa h_dense t ψ, exponential gen hsa h_dense t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_conv_ψ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa h_dense t ψ)) :=
    exponential_tendsto gen hsa h_dense t ψ
  have h_conv_φ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
    exponential_tendsto gen hsa h_dense t φ
  have h_approx_unitary : ∀ n : ℕ+,
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
    fun n => expBounded_yosidaApproxSym_unitary gen hsa n t ψ φ
  have h_inner_cont : Tendsto (fun n : ℕ+ =>
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ)
      atTop (𝓝 ⟪exponential gen hsa h_dense t ψ, exponential gen hsa h_dense t φ⟫_ℂ) :=
    Filter.Tendsto.inner h_conv_ψ h_conv_φ
  have h_const : Tendsto (fun n : ℕ+ => ⟪ψ, φ⟫_ℂ) atTop (𝓝 ⟪ψ, φ⟫_ℂ) := tendsto_const_nhds
  exact tendsto_nhds_unique h_inner_cont (h_const.congr (fun n => (h_approx_unitary n).symm))

/-! ### Group law -/

theorem exponential_group_law
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (s t : ℝ) (ψ : H) :
    exponential gen hsa h_dense (s + t) ψ =
    exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ) := by
  have h_approx_group : ∀ n : ℕ+,
      expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ =
      expBounded (I • yosidaApproxSym gen hsa n) s
        (expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
    intro n
    rw [expBounded_group_law]
    rfl
  have h_conv_lhs : Tendsto
      (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ)
      atTop (𝓝 (exponential gen hsa h_dense (s + t) ψ)) :=
    exponential_tendsto gen hsa h_dense (s + t) ψ
  have h_conv_t : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa h_dense t ψ)) :=
    exponential_tendsto gen hsa h_dense t ψ
  have h_conv_rhs : Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym gen hsa n) s
        (expBounded (I • yosidaApproxSym gen hsa n) t ψ))
      atTop (𝓝 (exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ))) := by
    have h_inner := exponential_tendsto gen hsa h_dense t ψ
    have h_outer : ∀ χ : H, Tendsto
        (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s χ)
        atTop (𝓝 (exponential gen hsa h_dense s χ)) :=
      fun χ => exponential_tendsto gen hsa h_dense s χ
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith
    rw [Metric.tendsto_atTop] at h_inner
    obtain ⟨N₁, hN₁⟩ := h_inner (ε / 2) hε2
    have h_outer_limit := h_outer (exponential gen hsa h_dense t ψ)
    rw [Metric.tendsto_atTop] at h_outer_limit
    obtain ⟨N₂, hN₂⟩ := h_outer_limit (ε / 2) hε2
    use max N₁ N₂
    intro n hn
    rw [dist_eq_norm]
    calc ‖expBounded (I • yosidaApproxSym gen hsa n) s
            (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
          exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖
        = ‖(expBounded (I • yosidaApproxSym gen hsa n) s
              (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
            expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ)) +
           (expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
            exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ))‖ := by
              congr 1; abel
      _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa n) s
              (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
            expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
            exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ :=
          norm_add_le _ _
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) s
              (expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa h_dense t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
            exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ := by
          rw [← map_sub]
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa h_dense t ψ‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa h_dense t ψ) -
            exponential gen hsa h_dense s (exponential gen hsa h_dense t ψ)‖ := by
          rw [expBounded_yosidaApproxSym_isometry gen hsa n s _]
      _ < ε / 2 + ε / 2 := by
          apply add_lt_add
          · rw [← dist_eq_norm]; exact hN₁ n (le_of_max_le_left hn)
          · rw [← dist_eq_norm]; exact hN₂ n (le_of_max_le_right hn)
      _ = ε := by ring
  exact tendsto_nhds_unique h_conv_lhs (h_conv_rhs.congr (fun n => (h_approx_group n).symm))

/-! ### Identity -/

theorem exponential_identity
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    exponential gen hsa h_dense 0 ψ = ψ := by
  have h_approx_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 ψ = ψ :=
    fun n => expBounded_at_zero _ ψ
  have h_const : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                         atTop (𝓝 ψ) := by
    simp_rw [h_approx_zero]
    exact tendsto_const_nhds
  have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                        atTop (𝓝 (exponential gen hsa h_dense 0 ψ)) :=
    exponential_tendsto gen hsa h_dense 0 ψ
  exact tendsto_nhds_unique h_conv h_const

/-! ### Strong continuity -/

theorem exponential_strong_continuous
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Continuous (fun t : ℝ => exponential gen hsa h_dense t ψ) := by
  have h_exp_eq_U : ∀ (φ : H), φ ∈ gen.domain → ∀ t : ℝ,
      exponential gen hsa h_dense t φ = U_grp.U t φ := by
    intro φ hφ t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
      exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto
  have h_cont_domain : ∀ (φ : H), φ ∈ gen.domain →
      Continuous (fun t : ℝ => exponential gen hsa h_dense t φ) := by
    intro φ hφ
    have h_eq : (fun t => exponential gen hsa h_dense t φ) = (fun t => U_grp.U t φ) := by
      ext t
      exact h_exp_eq_U φ hφ t
    rw [h_eq]
    exact U_grp.strong_continuous φ
  have h_isometry : ∀ t : ℝ, ∀ (χ : H), ‖exponential gen hsa h_dense t χ‖ = ‖χ‖ := by
    intro t χ
    have h_inner := exponential_unitary gen hsa h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner
    have h_sq : ‖exponential gen hsa h_dense t χ‖^2 = ‖χ‖^2 := by
      have h_eq : (‖exponential gen hsa h_dense t χ‖ : ℂ)^2 = (‖χ‖ : ℂ)^2 := by
        exact h_inner
      exact_mod_cast h_eq
    rw [← Real.sqrt_sq (norm_nonneg (exponential gen hsa h_dense t χ)),
        ← Real.sqrt_sq (norm_nonneg χ), h_sq]
  rw [Metric.continuous_iff]
  intro t ε hε
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close
  have h_cont_φ := h_cont_domain φ hφ_mem
  rw [Metric.continuous_iff] at h_cont_φ
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_φ t (ε / 3) hε3
  use δ, hδ_pos
  intro s hs
  rw [dist_eq_norm]
  calc ‖exponential gen hsa h_dense s ψ - exponential gen hsa h_dense t ψ‖
      = ‖(exponential gen hsa h_dense s ψ - exponential gen hsa h_dense s φ) +
         (exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ) +
         (exponential gen hsa h_dense t φ - exponential gen hsa h_dense t ψ)‖ := by abel_nf
    _ ≤ ‖exponential gen hsa h_dense s ψ - exponential gen hsa h_dense s φ‖ +
        ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ +
        ‖exponential gen hsa h_dense t φ - exponential gen hsa h_dense t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          gcongr
          exact norm_add_le _ _
    _ = ‖exponential gen hsa h_dense s (ψ - φ)‖ +
        ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ +
        ‖exponential gen hsa h_dense t (φ - ψ)‖ := by
          rw [← map_sub (exponential gen hsa h_dense s),
              ← map_sub (exponential gen hsa h_dense t)]
    _ = ‖ψ - φ‖ + ‖exponential gen hsa h_dense s φ - exponential gen hsa h_dense t φ‖ + ‖φ - ψ‖ := by
          rw [h_isometry s (ψ - φ), h_isometry t (φ - ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hδ s hs
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

/-! ### Generator characterization -/

theorem exponential_generator_eq
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (exponential gen hsa h_dense t φ - φ))
            (𝓝[≠] 0) (𝓝 (I • gen.op ⟨φ, hφ⟩)) := by
  have h_exp_eq_U : ∀ t : ℝ, exponential gen hsa h_dense t φ = U_grp.U t φ := by
    intro t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa h_dense t φ)) :=
      exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto
  have h_eq_seq : ∀ t : ℝ, (t⁻¹ : ℂ) • (exponential gen hsa h_dense t φ - φ) =
                          (t⁻¹ : ℂ) • (U_grp.U t φ - φ) := by
    intro t
    rw [h_exp_eq_U t]
  have h_gen_formula := gen.generator_formula ⟨φ, hφ⟩
  have h_scalar : ∀ t : ℝ, t ≠ 0 → (t⁻¹ : ℂ) = I * (I * (t : ℂ))⁻¹ := by
    intro t ht
    field_simp
  have h_transform : ∀ t : ℝ, t ≠ 0 →
      (t⁻¹ : ℂ) • (U_grp.U t φ - φ) = I • ((I * (t : ℂ))⁻¹ • (U_grp.U t φ - φ)) := by
    intro t ht
    rw [← smul_assoc, h_scalar t ht]
    rfl
  refine Tendsto.congr' ?_ (Filter.Tendsto.const_smul h_gen_formula I)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h_eq_seq t, h_transform t ht]

/-! ### Differentiability on domain -/

theorem exponential_derivative_on_domain
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) (hψ : ψ ∈ gen.domain) :
    HasDerivAt (fun s : ℝ => exponential gen hsa h_dense s ψ)
               (I • gen.op ⟨U_grp.U t ψ, gen.domain_invariant t ψ hψ⟩)
               t := by
  have h_exp_eq_U : ∀ s : ℝ, exponential gen hsa h_dense s ψ = U_grp.U s ψ := by
    intro s
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense s ψ hψ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s ψ)
                          atTop (𝓝 (exponential gen hsa h_dense s ψ)) :=
      exponential_tendsto gen hsa h_dense s ψ
    exact tendsto_nhds_unique h_conv h_tendsto
  have h_fun_eq : (fun s : ℝ => exponential gen hsa h_dense s ψ) = (fun s : ℝ => U_grp.U s ψ) := by
    ext s
    exact h_exp_eq_U s
  rw [h_fun_eq]
  exact unitary_hasDerivAt gen hsa t ψ hψ

end QuantumMechanics.Yosida
