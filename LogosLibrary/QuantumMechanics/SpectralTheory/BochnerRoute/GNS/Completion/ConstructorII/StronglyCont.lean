/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/ConstructorII/StronglyCont.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.ConstructorII.Lemmas

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- The inner product `t ↦ ⟨translate t α, β⟩_f` is continuous.
    Each term in the double sum involves `f` at a shifted argument;
    `f` is continuous, the sum is finite. -/
lemma pdInner_translate_left_continuous {f : ℝ → ℂ}
    (hf : IsContinuous f) (α β : ℝ →₀ ℂ) :
    Continuous (fun t => pdInner f (translate t α) β) := by
  -- Rewrite as a double Finset.sum
  have heq : ∀ t, pdInner f (translate t α) β =
      ∑ r ∈ α.support, ∑ s ∈ β.support,
        starRingEnd ℂ (α r) * β s * f (s - (r + t)) := by
    intro t
    simp only [pdInner, translate]
    rw [Finsupp.sum_mapDomain_index
      (fun r => by simp [Finsupp.sum])
      (fun r c₁ c₂ => by
        simp only [Finsupp.sum, map_add, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring)]
    exact Eq.symm (Complex.ext rfl rfl)
  simp_rw [heq]
  apply continuous_finset_sum; intro r _
  apply continuous_finset_sum; intro s _
  exact continuous_const.mul
    (hf.continuity.comp (continuous_const.sub (continuous_const.add continuous_id)))


/-- For Finsupp α, the map t ↦ quotientTranslate t (mkQ α) is continuous ℝ → V. -/
lemma quotientTranslate_continuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    Continuous (fun t => quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) := by
  letI nacgV : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI ipsV : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  set mkQ := (pdNullSubmodule hPD hH).mkQ
  set qα := mkQ α
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- The cross term: t ↦ Re(pdInner f (translate t α) (translate t₀ α))
  set cross := fun t => (pdInner f (translate t α) (translate t₀ α)).re
  have hcross_cont : Continuous cross :=
    Complex.continuous_re.comp (pdInner_translate_left_continuous hf α (translate t₀ α))
  -- At t = t₀, cross = Re(pdInner f α α) = ‖qα‖² (by isometry + inner_self_eq_norm_sq)
  have hcross_eq : cross t₀ = ‖qα‖ ^ 2 := by
    show (pdInner f (translate t₀ α) (translate t₀ α)).re = _
    rw [pdInner_translate]
    rw [← @inner_self_eq_norm_sq ℂ]; rfl
  -- Choose δ from continuity of cross
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, @fun t ht => ?_⟩
  rw [dist_eq_norm]
  -- Expand ‖x - y‖² via norm_sub_sq
  set x := quotientTranslate hPD hH t qα
  set y := quotientTranslate hPD hH t₀ qα
  have hx_norm : ‖x‖ = ‖qα‖ := quotientTranslate_norm hPD hH t qα
  have hy_norm : ‖y‖ = ‖qα‖ := quotientTranslate_norm hPD hH t₀ qα
  have hinner_re : RCLike.re (@inner ℂ _ ipsV.toInner x y) = cross t := by
    change (quotientInner hPD hH _ _).re = _
    rfl
  have hnorm_sq : ‖x - y‖ ^ 2 = 2 * ‖qα‖ ^ 2 - 2 * cross t := by
    rw [@norm_sub_sq ℂ, hx_norm, hy_norm, hinner_re]; ring
  -- From continuity: |cross t - cross t₀| < ε²/2
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by
    rw [← Real.dist_eq]; exact hδ_spec ht
  -- ‖x - y‖² = 2(cross t₀ - cross t) = 2(‖qα‖² - cross t)
  rw [← hcross_eq] at hnorm_sq
  -- ‖x - y‖² < ε²
  have hnn : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
  have hnorm_bound : ‖x - y‖ ^ 2 < ε ^ 2 := by
    grind only [= abs.eq_1, = max_def]
  -- ‖x - y‖ < ε
  nlinarith [sq_nonneg ‖x - y‖, sq_abs ε]


/-- For Finsupp α, t ↦ completionTranslate t (↑(mkQ α)) is continuous in the completion. -/
lemma completionTranslate_continuous_on_dense {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) (α : ℝ →₀ ℂ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    Continuous (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  -- completionTranslate t (↑(mkQ α)) = ↑(quotientTranslate t (mkQ α))
  have heq : (fun t => completionTranslate hPD hH t
      (↑((pdNullSubmodule hPD hH).mkQ α))) =
    (fun t => (↑(quotientTranslate hPD hH t
      ((pdNullSubmodule hPD hH).mkQ α)) :
        UniformSpace.Completion (GNSQuotient hPD hH))) := by
    ext t; exact completionTranslate_coe hPD hH t _
  rw [heq]
  exact (UniformSpace.Completion.continuous_coe _).comp
    (quotientTranslate_continuous hPD hH hf α)


/-- `completionTranslate t` preserves distances (isometry on the completion). -/
lemma completionTranslate_dist {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (x y : UniformSpace.Completion (GNSQuotient hPD hH)),
    dist (completionTranslate hPD hH t x) (completionTranslate hPD hH t y) =
    dist x y := by
  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  -- ‖U(t)(x - y)‖² = ‖x - y‖² from inner product preservation
  have h := completionTranslate_inner hPD hH t (x - y) (x - y)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by exact_mod_cast h)


/-- **Strong continuity**: for every ψ in the completion,
    t ↦ completionTranslate t ψ is continuous. -/
theorem completionTranslate_strong_continuous {f : ℝ → ℂ}
    (hPD : PositiveDefinite f) (hH : IsHermitian f) (hf : IsContinuous f) :
    letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
    letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
      InnerProductSpace.ofCore (quotientCore hPD hH).toCore
    letI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
      gnsQuotient_uniformContinuousConstSMul hPD hH
    ∀ (ψ : UniformSpace.Completion (GNSQuotient hPD hH)),
    Continuous (fun t => completionTranslate hPD hH t ψ) := by

  letI : NormedAddCommGroup (GNSQuotient hPD hH) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (quotientCore hPD hH)
  letI : InnerProductSpace ℂ (GNSQuotient hPD hH) :=
    InnerProductSpace.ofCore (quotientCore hPD hH).toCore
  haveI : UniformContinuousConstSMul ℂ (GNSQuotient hPD hH) :=
    gnsQuotient_uniformContinuousConstSMul hPD hH
  intro ψ
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Step 1: approximate ψ by ↑v
  have hd := UniformSpace.Completion.denseRange_coe (α := GNSQuotient hPD hH)
  obtain ⟨v, hv⟩ := hd.exists_dist_lt ψ (by positivity : (0 : ℝ) < ε / 3)
  obtain ⟨α, rfl⟩ := Submodule.mkQ_surjective (pdNullSubmodule hPD hH) v
  set w : UniformSpace.Completion (GNSQuotient hPD hH) :=
    ↑((pdNullSubmodule hPD hH).mkQ α)
  -- Step 2: from continuity on the dense set, get δ
  have hcont_α := completionTranslate_continuous_on_dense hPD hH hf α
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcont_α.continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, @fun t ht => ?_⟩
  -- Step 3: triangle inequality with isometry
  calc dist (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t₀ ψ)
      ≤ dist (completionTranslate hPD hH t ψ) (completionTranslate hPD hH t w) +
        dist (completionTranslate hPD hH t w) (completionTranslate hPD hH t₀ w) +
        dist (completionTranslate hPD hH t₀ w) (completionTranslate hPD hH t₀ ψ) := by
        have h1 := dist_triangle (completionTranslate hPD hH t ψ)
          (completionTranslate hPD hH t w) (completionTranslate hPD hH t₀ ψ)
        have h2 := dist_triangle (completionTranslate hPD hH t w)
          (completionTranslate hPD hH t₀ w) (completionTranslate hPD hH t₀ ψ)
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by
        -- Term 1: dist(U(t)ψ, U(t)w) = dist(ψ, w) < ε/3 by isometry
        have h1 : dist (completionTranslate hPD hH t ψ)
            (completionTranslate hPD hH t w) < ε / 3 := by
          rw [completionTranslate_dist hPD hH t ψ w]; exact hv
        -- Term 2: dist(U(t)w, U(t₀)w) < ε/3 by continuity on dense set
        have h2 : dist (completionTranslate hPD hH t w)
            (completionTranslate hPD hH t₀ w) < ε / 3 :=
          hδ_spec ht
        -- Term 3: dist(U(t₀)w, U(t₀)ψ) = dist(w, ψ) < ε/3 by isometry
        have h3 : dist (completionTranslate hPD hH t₀ w)
            (completionTranslate hPD hH t₀ ψ) < ε / 3 := by
          rw [completionTranslate_dist hPD hH t₀ w ψ, dist_comm]; exact hv
        linarith
    _ = ε := by ring


end SpectralBridge.Bochner.GNS
