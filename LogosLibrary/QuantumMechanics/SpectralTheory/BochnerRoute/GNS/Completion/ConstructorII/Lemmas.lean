/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/ConstructorII/Lemmas.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.UnitaryGroup

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- `translate t` as a ℂ-linear map on `ℝ →₀ ℂ`. -/
noncomputable def translateLM (t : ℝ) : (ℝ →₀ ℂ) →ₗ[ℂ] (ℝ →₀ ℂ) where
  toFun := translate t
  map_add' := translate_add_right t
  map_smul' := translate_smul t

/-- Translation preserves the null submodule (needed for `Submodule.mapQ`). -/
lemma translateLM_preserves_null {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    pdNullSubmodule hPD hH ≤ (pdNullSubmodule hPD hH).comap (translateLM t) := by
  intro α hα
  exact pdNullSpace_translate_invariant hα t

/-- Translation descended to the GNS quotient via `Submodule.mapQ`. -/
noncomputable def quotientTranslate {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    GNSQuotient hPD hH →ₗ[ℂ] GNSQuotient hPD hH :=
  Submodule.mapQ _ _ (translateLM t) (translateLM_preserves_null hPD hH t)

/-- Computation rule: `quotientTranslate` on a representative. -/
@[simp]
lemma quotientTranslate_mk {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    quotientTranslate hPD hH t (Submodule.Quotient.mk α) =
    Submodule.Quotient.mk (translate t α) := rfl

/-- Isometry: `quotientTranslate t` preserves `quotientInner`. -/
lemma quotientTranslate_inner {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x y : GNSQuotient hPD hH) :
    quotientInner hPD hH (quotientTranslate hPD hH t x)
                         (quotientTranslate hPD hH t y) =
    quotientInner hPD hH x y := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  induction y using Submodule.Quotient.induction_on with | _ b =>
  simp only [quotientTranslate_mk, quotientInner_mk]
  exact pdInner_translate t a b

/-- Group law: `U₀(s) ∘ U₀(t) = U₀(s + t)` on the quotient. -/
lemma quotientTranslate_comp {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (s t : ℝ)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH s (quotientTranslate hPD hH t x) =
    quotientTranslate hPD hH (s + t) x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk]
  congr 1
  exact translate_translate s t a

/-- Identity: `U₀(0) = id` on the quotient. -/
lemma quotientTranslate_zero {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f)
    (x : GNSQuotient hPD hH) :
    quotientTranslate hPD hH 0 x = x := by
  induction x using Submodule.Quotient.induction_on with | _ a =>
  simp only [quotientTranslate_mk, translate_zero]


/-- `quotientTranslate t` preserves the norm. -/
lemma quotientTranslate_norm {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (x : GNSQuotient hPD hH) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    ‖quotientTranslate hPD hH t x‖ = ‖x‖ := by
  letI nacgV := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  have h_inner : @inner ℂ _ ipsV.toInner
      (quotientTranslate hPD hH t x) (quotientTranslate hPD hH t x) =
      @inner ℂ _ ipsV.toInner x x := by
    induction x using Submodule.Quotient.induction_on with | _ a =>
    show quotientInner hPD hH _ _ = quotientInner hPD hH _ _
    simp only [quotientTranslate_mk, quotientInner_mk]
    exact pdInner_translate t a a
  have h_sq : ‖quotientTranslate hPD hH t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ]
    exact congrArg RCLike.re h_inner
  have hfact : (‖quotientTranslate hPD hH t x‖ - ‖x‖) *
               (‖quotientTranslate hPD hH t x‖ + ‖x‖) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfact with h | h
  · linarith
  · linarith [norm_nonneg (quotientTranslate hPD hH t x), norm_nonneg x]


/-- `quotientTranslate t` as a linear isometry on the GNS quotient. -/
noncomputable def quotientTranslateLI {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    GNSQuotient hPD hH →ₗᵢ[ℂ] GNSQuotient hPD hH := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  exact ⟨quotientTranslate hPD hH t, quotientTranslate_norm hPD hH t⟩


/-- Uniform continuity of `quotientTranslate` (isometries are uniformly continuous). -/
lemma quotientTranslate_uniformContinuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    UniformContinuous (quotientTranslate hPD hH t) := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI := InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  exact (quotientTranslateLI hPD hH t).isometry.uniformContinuous



/-- Translation extended to the GNS completion as a ℂ-linear map.
    Linearity proved by density: `Completion.map` preserves add/smul
    because it agrees with the linear `quotientTranslate` on the dense image. -/
noncomputable def completionTranslate {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    UniformSpace.Completion (GNSQuotient hPD hH) →ₗ[ℂ]
    UniformSpace.Completion (GNSQuotient hPD hH) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  have huc : UniformContinuous (quotientTranslate hPD hH t) :=
    quotientTranslate_uniformContinuous hPD hH t
  -- Pre-wire completion-level instances at outer scope so nested by-blocks see them
  letI : AddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  letI : IsUniformAddGroup (UniformSpace.Completion (GNSQuotient hPD hH)) := inferInstance
  haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
    IsTopologicalAddGroup.toContinuousAdd
  exact {
    toFun := UniformSpace.Completion.map (quotientTranslate hPD hH t)
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp continuous_add
        · haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
            IsTopologicalAddGroup.toContinuousAdd
          exact continuous_add.comp
            ((UniformSpace.Completion.continuous_map.comp continuous_fst).prodMk
             (UniformSpace.Completion.continuous_map.comp continuous_snd))
      · intro a b
        simp only [← UniformSpace.Completion.coe_add,
                   UniformSpace.Completion.map_coe huc, map_add]
    map_smul' := fun c x => by
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · apply isClosed_eq
        · exact UniformSpace.Completion.continuous_map.comp (continuous_const_smul c)
        · exact (continuous_const_smul c).comp UniformSpace.Completion.continuous_map
      · intro a
        simp only [← UniformSpace.Completion.coe_smul,
                   UniformSpace.Completion.map_coe huc, map_smul]
        rfl
  }


/-- Computation rule: `completionTranslate` on a coerced quotient element. -/
@[simp]
lemma completionTranslate_coe {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ)
    (a : GNSQuotient hPD hH) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    completionTranslate hPD hH t ↑a =
    ↑(quotientTranslate hPD hH t a) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  show UniformSpace.Completion.map (quotientTranslate hPD hH t) ↑a = _
  exact UniformSpace.Completion.map_coe
    (quotientTranslate_uniformContinuous hPD hH t) a


/-- Group law on the completion: U(s)(U(t)(ψ)) = U(s+t)(ψ). -/
lemma completionTranslate_comp {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH s (completionTranslate hPD hH t ψ) =
    completionTranslate hPD hH (s + t) ψ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map
    · exact UniformSpace.Completion.continuous_map
  · intro a
    rw [completionTranslate_coe, completionTranslate_coe, completionTranslate_coe]
    congr 1
    exact quotientTranslate_comp hPD hH s t a


/-- Identity on the completion: U(0)(ψ) = ψ. -/
lemma completionTranslate_zero' {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    completionTranslate hPD hH 0 ψ = ψ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  refine UniformSpace.Completion.induction_on ψ ?_ ?_
  · apply isClosed_eq
    · exact UniformSpace.Completion.continuous_map
    · exact continuous_id
  · intro a
    rw [completionTranslate_coe]
    simp only [quotientTranslate_zero]


/-- Isometry on the completion: ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ, φ⟩. -/
lemma completionTranslate_inner {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ φ : UniformSpace.Completion (GNSQuotient hPD hH)),
    @inner ℂ _ InnerProductSpace.toInner
      (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t φ) =
    @inner ℂ _ InnerProductSpace.toInner ψ φ := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ φ
  refine UniformSpace.Completion.induction_on₂ ψ φ ?_ ?_
  · apply isClosed_eq
    haveI : ContinuousAdd (UniformSpace.Completion (GNSQuotient hPD hH)) :=
      IsTopologicalAddGroup.toContinuousAdd
    have hcont_map : Continuous (completionTranslate hPD hH t) :=
      UniformSpace.Completion.continuous_map
    have hcont_pair : Continuous (fun (p : UniformSpace.Completion _ × UniformSpace.Completion _) =>
        (completionTranslate hPD hH t p.1, completionTranslate hPD hH t p.2)) :=
      (hcont_map.comp continuous_fst).prodMk (hcont_map.comp continuous_snd)
    · exact (@continuous_inner ℂ _ _ _ _).comp hcont_pair
    · exact @continuous_inner ℂ _ _ _ _
  · intro a b
    rw [completionTranslate_coe, completionTranslate_coe]
    simp only [UniformSpace.Completion.inner_coe]
    exact quotientTranslate_inner hPD hH t a b

/-- Compatibility: U(t) ∘ embed = embed ∘ translate(t) on the completion. -/
lemma completionTranslate_compat {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    let emb := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)).toLinearMap.comp
                 (pdNullSubmodule hPD hH).mkQ
    completionTranslate hPD hH t (emb α) = emb (translate t α) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  show completionTranslate hPD hH t
    (↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) α)) =
    ↑(Submodule.Quotient.mk (p := pdNullSubmodule hPD hH) (translate t α))
  rw [completionTranslate_coe, quotientTranslate_mk]

end SpectralBridge.Bochner.GNS
