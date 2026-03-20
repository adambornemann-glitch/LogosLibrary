/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/Constructor.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.Bundler

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- Scalar multiplication on the GNS quotient is uniformly continuous.
    (Instance synthesis can't derive this due to the NormedAddCommGroup/Module diamond,
    so we build it from the Lipschitz bound directly.) -/
lemma gnsQuotient_uniformContinuousConstSMul {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  constructor; intro c
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hc : (0 : ℝ) < ‖c‖ + 1 := by linarith [norm_nonneg c]
  refine ⟨ε / (‖c‖ + 1), by positivity, fun {x y} hxy => ?_⟩
  calc dist (c • x) (c • y)
      = ‖c • (x - y)‖ := by rw [dist_eq_norm, smul_sub]
    _ ≤ ‖c‖ * ‖x - y‖ := NormedSpace.norm_smul_le c (x - y)
    _ ≤ (‖c‖ + 1) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    _ = (‖c‖ + 1) * dist x y := by rw [dist_eq_norm]
    _ < (‖c‖ + 1) * (ε / (‖c‖ + 1)) := by exact mul_lt_mul_of_pos_left hxy hc
    _ = ε := by field_simp


/-- **Existence of the GNS Hilbert space.**

Construction outline:
1. `pdInner` is a positive semi-definite Hermitian form on `ℝ →₀ ℂ`.
2. The null space `N = {α : pdInner f α α = 0}` is a ℂ-submodule.
3. The quotient `V = (ℝ →₀ ℂ) / N` inherits a genuine inner product:
   `⟨[α], [β]⟩_V = pdInner f α β` (well-defined by null orthogonality).
4. This makes `V` a pre-Hilbert space.
5. The Cauchy completion `H = V̂` is a Hilbert space.
6. The embedding `ι : (ℝ →₀ ℂ) → H` is `α ↦ [α]` composed with
   the completion embedding. It is ℂ-linear and has dense range.

Mathlib tools:
- `Submodule.Quotient` for V = (ℝ →₀ ℂ) / N
- `InnerProductSpace.Core` to build the inner product on V
- `UniformSpace.Completion` for H = V̂
- `UniformSpace.Completion.denseRange_coe` for density -/
noncomputable def gnsConstruction {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    GNSData f := by
  let core := quotientCore hPD hH
  let V := GNSQuotient hPD hH
  letI nacgV : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  letI ipsV : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  haveI : UniformContinuousConstSMul ℂ V :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  let H := UniformSpace.Completion V
  let mkQ := (pdNullSubmodule hPD hH).mkQ
  let ι : V →ₗᵢ[ℂ] H := UniformSpace.Completion.toComplₗᵢ
  let emb : (ℝ →₀ ℂ) →ₗ[ℂ] H := ι.toLinearMap.comp mkQ
  exact {
    H := H
    instNACG := inferInstance
    instIPS := inferInstance
    instComplete := inferInstance
    embed := emb
    embed_inner := fun α β => by
      show @inner ℂ H _ (↑(mkQ α) : H) (↑(mkQ β) : H) = pdInner f α β
      rw [@UniformSpace.Completion.inner_coe]
      rfl
    embed_dense := by
      have h1 : DenseRange (mkQ : (ℝ →₀ ℂ) → V) :=
        (Submodule.mkQ_surjective _).denseRange
      have h2 : DenseRange (UniformSpace.Completion.coe' : V → H) :=
        UniformSpace.Completion.denseRange_coe
      exact h2.comp h1 (UniformSpace.Completion.continuous_coe V)
    embed_ker := fun α => by
      constructor
      · intro h
        change (↑(mkQ α) : H) = 0 at h
        rw [← UniformSpace.Completion.coe_zero] at h
        have hinj : mkQ α = 0 := by
          have := UniformSpace.Completion.isUniformEmbedding_coe (α := V)
          exact this.injective h
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hinj
      · intro h
        show (↑(mkQ α) : H) = 0
        have : mkQ α = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
        rw [this, UniformSpace.Completion.coe_zero]
  }

end SpectralBridge.Bochner.GNS
