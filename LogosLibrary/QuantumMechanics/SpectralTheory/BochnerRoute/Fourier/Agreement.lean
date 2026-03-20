/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerRoute/Fourier/Agreement.lean
-/
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute.Fourier.Distribution

namespace SpectralBridge.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set

/-! ## §6: Putting it together — agreement on `(a, b]` -/

/-- Two finite measures with the same characteristic function agree on `(a, b]`,
    provided `μ({a}) = 0` (i.e., `a` is a continuity point of `F_μ`).

This is the core of the uniqueness proof. The argument:
1. Same char. function → same Poisson integrals (§3)
2. Integrate over (a,b] → same arctan integrals (Fubini, §5)
3. Take ε → 0 → μ(a,b] = ν(a,b] (DCT, §5)  -/
lemma measure_Ioc_eq_of_fourier_eq (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ↑ω * ↑t) ∂μ = ∫ ω, exp (I * ↑ω * ↑t) ∂ν)
    {a b : ℝ} (hab : a < b)
    (ha_μ : μ {a} = 0) (ha_ν : ν {a} = 0)
    (hb_μ : μ {b} = 0) (hb_ν : ν {b} = 0) :
    μ (Ioc a b) = ν (Ioc a b) := by
  -- The arctan integrals are equal for all ε > 0
  have h_arctan_eq : ∀ ε : ℝ, 0 < ε →
      ∫ ω, arctanRecovery ε a b ω ∂μ = ∫ ω, arctanRecovery ε a b ω ∂ν := by
    intro ε hε
    have h_poisson := poisson_integral_eq_of_fourier_eq μ ν h hε
    have h_int_μ := integrated_poisson_eq_arctan μ hε hab
    have h_int_ν := integrated_poisson_eq_arctan ν hε hab
    have h_int_eq : ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂μ) =
                    ∫ s in Ioc a b, (∫ ω, poissonKernel ε (s - ω) ∂ν) := by
      congr 1; ext s; exact h_poisson s
    linarith [h_int_μ, h_int_ν, h_int_eq]
  -- Both sides have the same limit as ε → 0
  have h_lim_μ := arctan_integral_tendsto_measure μ hab ha_μ hb_μ
  have h_lim_ν := arctan_integral_tendsto_measure ν hab ha_ν hb_ν
  -- Transfer: since the ν-sequence equals the μ-sequence eventually, μ's limit = ν's limit
  have h_ee : (fun ε => ∫ ω, arctanRecovery ε a b ω ∂μ) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ ω, arctanRecovery ε a b ω ∂ν) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h_arctan_eq ε (mem_Ioi.mp hε)
  have h_lim_ν' : Tendsto (fun ε => ∫ ω, arctanRecovery ε a b ω ∂μ)
      (𝓝[>] 0) (𝓝 (ν (Ioc a b)).toReal) :=
    h_lim_ν.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
      (h_arctan_eq ε hε).symm)
  have h_toReal_eq : (μ (Ioc a b)).toReal = (ν (Ioc a b)).toReal :=
    tendsto_nhds_unique h_lim_μ h_lim_ν'
  rwa [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)]


lemma finite_of_measure_singleton_ge (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) : Set.Finite {x : ℝ | (1 : ENNReal) / ((n : ENNReal) + 1) ≤ μ {x}} := by
  by_contra h_inf
  rw [Set.not_finite] at h_inf
  have hn_ne : (↑n + 1 : ENNReal) ≠ 0 := by positivity
  have hn_top : (↑n + 1 : ENNReal) ≠ ⊤ := by simp
  -- Injective sequence of points each with μ-mass ≥ 1/(n+1)
  set f := h_inf.natEmbedding
  have hf_inj : Function.Injective (fun i => (f i : ℝ)) :=
    Subtype.val_injective.comp f.injective
  -- K distinct atoms of mass ≥ 1/(n+1) force μ(univ) ≥ K/(n+1)
  have h_lower : ∀ K : ℕ, (K : ENNReal) / (↑n + 1) ≤ μ Set.univ := by
    intro K
    calc (K : ENNReal) / (↑n + 1)
        = ∑ _i ∈ Finset.range K, 1 / (↑n + 1) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rfl
      _ ≤ ∑ i ∈ Finset.range K, μ {(f i : ℝ)} :=
          Finset.sum_le_sum fun i _ => (f i).2
      _ = μ (⋃ i ∈ Finset.range K, {(f i : ℝ)}) :=
          (measure_biUnion_finset
            (fun i _ j _ hij => Set.disjoint_singleton.mpr fun h => hij (hf_inj h))
            fun i _ => measurableSet_singleton _).symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  -- Choose K > μ(univ) * (n+1) — possible since RHS < ⊤
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt
    (ENNReal.mul_ne_top (measure_ne_top μ _) hn_top)
  -- Contradiction: K ≤ μ(univ)*(n+1) < K
  exact absurd
    (calc (K : ENNReal)
        = (K : ENNReal) / (↑n + 1) * (↑n + 1) :=
          (ENNReal.div_mul_cancel hn_ne hn_top).symm
      _ ≤ μ Set.univ * (↑n + 1) := by gcongr; exact h_lower K)
    (not_le.mpr hK)

end SpectralBridge.Bochner.FourierUniqueness
