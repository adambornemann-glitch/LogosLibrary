/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/GNS/Completion/StronglyEx.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.GNS.Completion.ConstructorII

namespace SpectralBridge.Bochner.GNS

open Complex Finsupp Filter Topology

/-- **Strong continuity of U(t) on the dense set.**

For any formal sum `α = Σⱼ cⱼ δ_{sⱼ}`, we have
  ‖U(t)(embed α) - embed α‖² = Re⟨U(t)α - α, U(t)α - α⟩_f

Expanding the bilinear form over the finite support:
  = Σⱼ Σₖ c̄ⱼ cₖ [2f(sₖ-sⱼ) - f(sₖ-sⱼ+t) - f(sₖ-sⱼ-t)]

Each term → 0 as t → 0 by continuity of f (proved in IsContinuous.continuity).
Since the sum is finite, the whole expression → 0.

This gives: for each α, ‖U(t)(embed α) - embed α‖ → 0 as t → 0.
By the group law, t ↦ U(t)(embed α) is continuous at every point. -/
lemma strong_continuity_on_dense {f : ℝ → ℂ}
    (hf : IsContinuous f) (gns : GNSData f)
    (U : letI := gns.instNACG; letI := gns.instIPS; ℝ → gns.H →ₗ[ℂ] gns.H)
    (hcompat : ∀ t α, U t (gns.embed α) = gns.embed (translate t α))
    (_hiso : ∀ t ψ φ, @inner ℂ _ gns.instIPS.toInner (U t ψ) (U t φ) =
                      @inner ℂ _ gns.instIPS.toInner ψ φ) :
    ∀ (α : ℝ →₀ ℂ), letI := gns.instNACG;
      Continuous (fun t => U t (gns.embed α)) := by
  letI := gns.instNACG
  letI := gns.instIPS
  intro α
  -- Reduce to continuity of embed ∘ translate via compatibility
  suffices Continuous (fun t => gns.embed (translate t α)) from
    this.congr (fun t => (hcompat t α).symm)
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- The cross term: t ↦ Re(pdInner f (translate t α) (translate t₀ α))
  set cross := fun t => (pdInner f (translate t α) (translate t₀ α)).re
  have hcross_cont : Continuous cross :=
    Complex.continuous_re.comp (pdInner_translate_left_continuous hf α (translate t₀ α))
  -- At t = t₀, cross reduces via translation isometry
  have hcross_t₀ : cross t₀ = (pdInner f α α).re := by
    show (pdInner f (translate t₀ α) (translate t₀ α)).re = _
    rw [pdInner_translate]
  -- Both norms equal the same constant (translation isometry + embed_inner)
  have hF_norm_sq : ∀ s, ‖gns.embed (translate s α)‖ ^ 2 = (pdInner f α α).re := by
    intro s; rw [← @inner_self_eq_norm_sq ℂ, gns.embed_inner, pdInner_translate]; rfl
  -- The H-inner product real part matches cross
  have hinner_re : ∀ s, RCLike.re (@inner ℂ gns.H _
      (gns.embed (translate s α)) (gns.embed (translate t₀ α))) = cross s := by
    intro s; rw [gns.embed_inner]; rfl
  -- ‖F(t) - F(t₀)‖² = 2(cross t₀ - cross t) via norm_sub_sq
  have hnorm_sq : ∀ s, ‖gns.embed (translate s α) - gns.embed (translate t₀ α)‖ ^ 2 =
      2 * (cross t₀ - cross s) := by
    intro s
    rw [@norm_sub_sq ℂ, hF_norm_sq s, hF_norm_sq t₀, hinner_re s, hcross_t₀]; ring
  -- Choose δ from continuity of cross at t₀
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    hcross_cont.continuousAt (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  rw [dist_eq_norm]
  -- |cross t - cross t₀| < ε²/2
  have hcross_near : |cross t - cross t₀| < ε ^ 2 / 2 := by
    rw [← Real.dist_eq]; exact hδ_spec ht
  -- cross t₀ - cross t ≥ 0 (from ‖·‖² ≥ 0)
  have hnn : 0 ≤ cross t₀ - cross t := by
    have := (sq_nonneg ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖).trans_eq
      (hnorm_sq t)
    linarith
  -- ‖F(t) - F(t₀)‖² < ε²
  have hnorm_bound : ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖ ^ 2 < ε ^ 2 := by
    rw [hnorm_sq]
    have : cross t₀ - cross t ≤ |cross t - cross t₀| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  -- ‖F(t) - F(t₀)‖ < ε
  nlinarith [sq_nonneg ‖gns.embed (translate t α) - gns.embed (translate t₀ α)‖, sq_abs ε]

/-- **Strong continuity extends to all of H.**

Given:
- Strong continuity on a dense set D ⊆ H
- Each U(t) is an isometry
Then U(t) is strongly continuous on all of H.

Standard 3ε argument: for ψ ∈ H and ε > 0,
1. Pick φ ∈ D with ‖ψ - φ‖ < ε/3
2. Pick δ so |t| < δ ⟹ ‖U(t)φ - φ‖ < ε/3
3. Then ‖U(t)ψ - ψ‖ ≤ ‖U(t)(ψ-φ)‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖
                       = ‖ψ-φ‖ + ‖U(t)φ - φ‖ + ‖φ - ψ‖ < ε -/
lemma strong_continuity_extends {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →ₗ[ℂ] H)
    (hiso : ∀ t ψ, ‖U t ψ‖ = ‖ψ‖)
    (_hgroup : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (_hid : ∀ ψ, U 0 ψ = ψ)
    (D : Set H) (hD : Dense D)
    (hD_cont : ∀ φ ∈ D, Continuous (fun t => U t φ)) :
    ∀ ψ, Continuous (fun t => U t ψ) := by
  -- Key lemma: U(t) preserves distances (from norm preservation + linearity)
  have hdist_iso : ∀ (s : ℝ) (a b : H), dist (U s a) (U s b) = dist a b := by
    intro s a b; simp only [dist_eq_norm, ← map_sub, hiso]
  intro ψ
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Step 1: Approximate ψ by φ ∈ D with ‖ψ - φ‖ < ε/3
  obtain ⟨φ, hφD, hφ_close⟩ :=
    Metric.mem_closure_iff.mp (hD ψ) (ε / 3) (by positivity)
  -- Step 2: From continuity of t ↦ U(t)φ at t₀, get δ
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.continuousAt_iff.mp
    (hD_cont φ hφD).continuousAt (ε / 3) (by positivity)
  -- Step 3: The 3ε argument
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  calc dist (U t ψ) (U t₀ ψ)
      ≤ dist (U t ψ) (U t φ) +
        dist (U t φ) (U t₀ φ) +
        dist (U t₀ φ) (U t₀ ψ) := by
          linarith [dist_triangle (U t ψ) (U t φ) (U t₀ ψ),
                    dist_triangle (U t φ) (U t₀ φ) (U t₀ ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          -- Term 1: dist(U(t)ψ, U(t)φ) = dist(ψ, φ) < ε/3
          have h1 : dist (U t ψ) (U t φ) < ε / 3 := by
            rw [hdist_iso]; exact hφ_close
          -- Term 2: dist(U(t)φ, U(t₀)φ) < ε/3 by continuity on D
          have h2 : dist (U t φ) (U t₀ φ) < ε / 3 := hδ_spec ht
          -- Term 3: dist(U(t₀)φ, U(t₀)ψ) = dist(φ, ψ) < ε/3
          have h3 : dist (U t₀ φ) (U t₀ ψ) < ε / 3 := by
            rw [hdist_iso, dist_comm]; exact hφ_close
          linarith
    _ = ε := by ring


end SpectralBridge.Bochner.GNS
