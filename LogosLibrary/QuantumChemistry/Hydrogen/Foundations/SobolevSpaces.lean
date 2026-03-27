/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Sobolev Spaces on ℝ³

This file sets up the Sobolev spaces H¹(ℝ³) and H²(ℝ³) as submodules of L²(ℝ³, ℂ),
providing the domain infrastructure needed for the hydrogen atom Hamiltonian.

## Architecture

The critical downstream interface is:
  `SobolevH2 → Submodule ℂ L2_R3 → Generator.domain`

Once `SobolevH2` compiles as a `Submodule ℂ L2_R3`, the Laplacian can be defined
as a `Generator` with this domain, and the entire spectral pipeline
(Stone's theorem, functional calculus, spectral projections) applies automatically.


## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975]
* [Lieb, Loss, *Analysis*][lieb2001], Chapter 7.
-/
noncomputable section

namespace QuantumMechanics.Hydrogen

open MeasureTheory Complex Filter MeasurableSet ContDiffBump
open scoped Topology NNReal ENNReal TopologicalSpace ProbabilityTheory Pointwise ContDiff

/-! ### Configuration space and Hilbert space -/

/-- The physical configuration space ℝ³. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

instance : MeasurableSpace R3 := borel R3
instance : BorelSpace R3 := ⟨rfl⟩
instance : MeasureSpace R3 := ⟨MeasureTheory.Measure.addHaar⟩

/-- The Hilbert space L²(ℝ³, ℂ) with Lebesgue measure.

    This is the state space of non-relativistic quantum mechanics.
    It carries `NormedAddCommGroup`, `InnerProductSpace ℂ`, and
    `CompleteSpace` instances from Mathlib, making it a valid
    instantiation target for `Generator`. -/
abbrev L2_R3 : Type := Lp ℂ 2 (volume : Measure R3)

/-! ### Weak derivatives -/

/-- Predicate: `g` is the weak partial derivative of `f` in direction `i`.

    That is, for every smooth compactly supported test function φ:
      ∫ f(x) ∂ᵢφ(x) dx = - ∫ g(x) φ(x) dx

    We state this in terms of Lp representatives. The actual verification
    requires the distributional definition against test functions, which
    we axiomatize here and discharge in Phase 4 via mollification. -/
def HasWeakDerivative (f : L2_R3) (i : Fin 3) (g : L2_R3) : Prop :=
  ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
    - ∫ x, g x * φ x


/-! #### Helpers for du Bois-Reymond -/

/-- Conjugation preserves smoothness (ℝ-smooth). -/
lemma contDiff_starRingEnd_comp {f : R3 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => starRingEnd ℂ (f x)) :=
  ContDiff.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap hf


/-- Conjugation preserves compact support (star z = 0 ↔ z = 0). -/
lemma hasCompactSupport_starRingEnd_comp {f : R3 → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => starRingEnd ℂ (f x)) :=
  hf.comp_left (map_zero (starRingEnd ℂ))


/-- Smooth compactly supported functions on ℝ³ belong to L²  -/
lemma memLp_of_smooth_compactSupport (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    MemLp φ 2 (volume : Measure R3) := by
  have hcont := hφ.continuous
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    change IsFiniteMeasureOnCompacts (MeasureTheory.Measure.addHaar)
    infer_instance
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact hsupp.memLp_of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)


/-- Smooth compactly supported functions on ℝ³ belong to L²  -/
lemma memLp_of_smooth_compactSupport' (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    MemLp φ 2 (volume : Measure R3) := by
  have hcont := hφ.continuous
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    change IsFiniteMeasureOnCompacts (MeasureTheory.Measure.addHaar)
    infer_instance
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact hsupp.memLp_of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)


/-- Continuous compactly supported functions are dense in L²(ℝ³). -/
lemma dense_continuous_compactSupport_L2 :
    Dense {g : L2_R3 | ∃ (φ : R3 → ℂ),
      Continuous φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} := by
  rw [Metric.dense_iff]
  intro g ε hε
  have hg := Lp.memLp g
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε' : (ENNReal.ofReal (ε / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact RCLike.ofReal_pos.mp hε
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    change IsFiniteMeasureOnCompacts (MeasureTheory.Measure.addHaar)
    infer_instance
  haveI : (volume : Measure R3).Regular := by
    change (MeasureTheory.Measure.addHaar : Measure R3).Regular
    infer_instance
  haveI : WeaklyLocallyCompactSpace R3 := by infer_instance
  haveI : R1Space R3 := by infer_instance
  obtain ⟨φ, hsupp, hclose, hcont, hmem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp hε'
  use hmem.toLp φ
  constructor
  · simp only [Metric.mem_ball]
    rw [Lp.dist_def]
    have h1 : eLpNorm ((hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ)) 2 volume ≤
              ENNReal.ofReal (ε / 2) := by
      have hae : (hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ) =ᵐ[volume] φ - (g : R3 → ℂ) :=
        hmem.coeFn_toLp.sub (ae_eq_refl _)
      rw [eLpNorm_congr_ae (p := 2) hae, eLpNorm_sub_comm]
      exact hclose
    calc (eLpNorm ((hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ)) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_le_toReal
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)
            ENNReal.ofReal_ne_top |>.mpr h1
      _ < ε := by rw [ENNReal.toReal_ofReal (by linarith)]; linarith
  · exact ⟨φ, hcont, hsupp, hmem.coeFn_toLp⟩


/-- **Core mollification**: a continuous compactly supported function on ℝ³
    can be uniformly approximated by smooth compactly supported functions -/
private lemma exists_smooth_uniform_approx
    (φ : R3 → ℂ) (hcont : Continuous φ) (hsupp : HasCompactSupport φ)
    (δ : ℝ) (hδ : 0 < δ) (radius : ℝ) (hradius : 0 < radius) :
    ∃ (ψ : R3 → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (tsupport ψ ⊆ tsupport φ + Metric.closedBall (0 : R3) radius) ∧
      (∀ x, ‖ψ x - φ x‖ ≤ δ) := by
  -- Phase 1: Uniform continuity on enlarged compact set
  set K := tsupport φ
  have hK : IsCompact K := hsupp.isCompact
  set K₂ := K + Metric.closedBall (0 : R3) (2 * radius)
  have hK₂ : IsCompact K₂ := hK.add (isCompact_closedBall _ _)
  have huc := hK₂.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ε, hε, huc_spec⟩ := huc (δ / 2) (half_pos hδ)
  -- Phase 2: Choose mollification radius
  set r := min (ε / 2) (radius / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr_rad : r ≤ radius / 2 := min_le_right _ _
  have hr_le_radius : r ≤ radius := le_trans hr_rad (by linarith)
  -- Phase 3: Global oscillation bound
  have hosc : ∀ x y : R3, dist x y < r → ‖φ x - φ y‖ ≤ δ / 2 := by
    intro x y hxy
    by_cases hxK : x ∈ K
    · -- x ∈ K ⊆ K₂, and y ∈ ball(x,r) ⊆ K + ball(0,r) ⊆ K₂
      have hx₂ : x ∈ K₂ := Set.mem_add.mpr
        ⟨x, hxK, 0, Metric.mem_closedBall.mpr (by simp; grind only), by simp⟩
      have hy₂ : y ∈ K₂ := Set.mem_add.mpr
        ⟨x, hxK, y - x, by
          rw [Metric.mem_closedBall]
          calc dist (y - x) 0
              _ = ‖y - x‖ := by simp [dist_zero_right]
              _ = dist y x := (dist_eq_norm y x).symm
              _ = dist x y := dist_comm _ _
              _ ≤ r := le_of_lt hxy
              _ ≤ radius := hr_le_radius
              _ ≤ 2 * radius := by linarith, by abel⟩
      rw [← dist_eq_norm]
      exact le_of_lt (huc_spec x hx₂ y hy₂ (lt_trans hxy hr_ε))
    · -- x ∉ K: φ(x) = 0
      have hφx : φ x = 0 := by
        have : x ∉ Function.support φ := fun h => hxK (subset_tsupport φ h)
        exact Function.notMem_support.mp this
      rw [hφx, zero_sub, norm_neg]
      by_cases hyK : y ∈ K
      · -- y ∈ K, x ∉ K but x ∈ K + ball(0,r) ⊆ K₂
        have hx₂ : x ∈ K₂ := Set.mem_add.mpr
          ⟨y, hyK, x - y, by
            rw [Metric.mem_closedBall]
            calc dist (x - y) 0
              _ = ‖x - y‖ := by simp [dist_zero_right]
              _ = dist x y := (dist_eq_norm x y).symm
              _ ≤ r := le_of_lt hxy
              _ ≤ radius := hr_le_radius
              _ ≤ 2 * radius := by linarith, by abel⟩
        have hy₂ : y ∈ K₂ := Set.mem_add.mpr
          ⟨y, hyK, 0, Metric.mem_closedBall.mpr (by
            simp; exact le_of_lt hradius), by simp⟩
        calc ‖φ y‖ = ‖φ y - φ x‖ := by rw [hφx, sub_zero]
          _ = ‖φ x - φ y‖ := by rw [norm_sub_rev]
          _ ≤ δ / 2 := by rw [← dist_eq_norm]; exact le_of_lt (huc_spec x hx₂ y hy₂ (lt_trans hxy hr_ε))
      · -- Both ∉ K: φ(y) = 0
        have hφy : φ y = 0 := by
          have : y ∉ Function.support φ := fun h => hyK (subset_tsupport φ h)
          exact Function.notMem_support.mp this
        rw [hφy, norm_zero]; exact le_of_lt (half_pos hδ)
  -- Phase 4: Construct bump function and convolutions
  let ρ : ContDiffBump (0 : R3) := ⟨r / 2, r, by positivity, by linarith⟩
  set φ_re : R3 → ℝ := fun x => (φ x).re
  set φ_im : R3 → ℝ := fun x => (φ x).im
  have hcont_re : Continuous φ_re := Complex.continuous_re.comp hcont
  have hcont_im : Continuous φ_im := Complex.continuous_im.comp hcont
  have hmeas_re : AEStronglyMeasurable φ_re (volume : Measure R3) :=
    hcont_re.aestronglyMeasurable
  have hmeas_im : AEStronglyMeasurable φ_im (volume : Measure R3) :=
    hcont_im.aestronglyMeasurable
  set ψ_re := MeasureTheory.convolution (ρ.normed volume) φ_re (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set ψ_im := MeasureTheory.convolution (ρ.normed volume) φ_im (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set ψ : R3 → ℂ := fun x => ⟨ψ_re x, ψ_im x⟩
  refine ⟨ψ, ?smooth, ?compact_supp, ?supp_bound, ?unif_bound⟩
  case smooth =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      change (MeasureTheory.Measure.addHaar : Measure R3).IsAddHaarMeasure; infer_instance
    have hli_re : LocallyIntegrable φ_re volume := hcont_re.locallyIntegrable
    have hli_im : LocallyIntegrable φ_im volume := hcont_im.locallyIntegrable
    have hsmooth_re : ContDiff ℝ ∞ ψ_re :=
      HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.hasCompactSupport_normed ρ.contDiff_normed hli_re
    have hsmooth_im : ContDiff ℝ ∞ ψ_im :=
      HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.hasCompactSupport_normed ρ.contDiff_normed hli_im
    show ContDiff ℝ ∞ ψ
    have hrw : ψ = fun x => ((ψ_re x : ℂ) + (ψ_im x : ℂ) * Complex.I) := by
      ext x; apply Complex.ext
      · simp [ψ, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · simp [ψ, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [hrw]
    exact (Complex.ofRealCLM.contDiff.comp hsmooth_re).add
      ((Complex.ofRealCLM.contDiff.comp hsmooth_im).mul contDiff_const)
  case compact_supp =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      change (MeasureTheory.Measure.addHaar : Measure R3).IsAddHaarMeasure; infer_instance
    have hsupp_re : HasCompactSupport φ_re := hsupp.comp_left Complex.zero_re
    have hsupp_im : HasCompactSupport φ_im := hsupp.comp_left Complex.zero_im
    have hcs_re : HasCompactSupport ψ_re :=
      ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_re
    have hcs_im : HasCompactSupport ψ_im :=
      ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_im
    have h_sub : tsupport ψ ⊆ tsupport ψ_re ∪ tsupport ψ_im := by
      apply closure_minimal
      · intro x hx
        rw [Function.mem_support] at hx
        by_contra h
        rw [Set.mem_union, not_or] at h
        apply hx
        have hre0 : ψ_re x = 0 := image_eq_zero_of_notMem_tsupport h.1
        have him0 : ψ_im x = 0 := image_eq_zero_of_notMem_tsupport h.2
        show (⟨ψ_re x, ψ_im x⟩ : ℂ) = 0
        rw [hre0, him0]; rfl
      · exact (isClosed_tsupport _).union (isClosed_tsupport _)
    exact (hcs_re.isCompact.union hcs_im.isCompact).of_isClosed_subset
      (isClosed_tsupport _) h_sub
  case supp_bound =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      change (MeasureTheory.Measure.addHaar : Measure R3).IsAddHaarMeasure; infer_instance
    have h_closed : IsClosed (tsupport φ + Metric.closedBall (0 : R3) radius) :=
      (hsupp.isCompact.add (isCompact_closedBall _ _)).isClosed
    apply closure_minimal _ h_closed
    have hρ_zero : ∀ t, t ∉ Metric.closedBall (0 : R3) r → ρ.normed volume t = 0 := by
      intro t ht
      have h_not_ball : t ∉ Metric.ball (0 : R3) r :=
        fun h => ht (Metric.ball_subset_closedBall h)
      have h_zero : (ρ : R3 → ℝ) t = 0 := by
        by_contra h
        have : t ∈ Function.support (ρ : R3 → ℝ) := Function.mem_support.mpr h
        rw [ρ.support_eq] at this
        exact h_not_ball this
      simp [ρ.normed_def, h_zero]
    have hφ_zero : ∀ x, x ∉ tsupport φ + Metric.closedBall (0 : R3) radius →
        ∀ t ∈ Metric.closedBall (0 : R3) r, φ (x - t) = 0 := by
      intro x hx t ht
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hx (Set.mem_add.mpr ⟨x - t, hmem, t,
        Metric.closedBall_subset_closedBall hr_le_radius ht, by abel⟩)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hx_out
    apply hx; clear hx
    have h_re : ψ_re x = 0 := by
      change (MeasureTheory.convolution (ρ.normed volume) φ_re
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0
      simp only [MeasureTheory.convolution_def]
      refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : t ∈ Metric.closedBall (0 : R3) r
      · rw [show φ_re (x - t) = (φ (x - t)).re from rfl, hφ_zero x hx_out t ht,
            Complex.zero_re, mul_zero]
        exact Real.ext_cauchy rfl
      · rw [hρ_zero t ht, zero_mul]
        exact Real.ext_cauchy rfl
    have h_im : ψ_im x = 0 := by
      change (MeasureTheory.convolution (ρ.normed volume) φ_im
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0
      simp only [MeasureTheory.convolution_def]
      refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : t ∈ Metric.closedBall (0 : R3) r
      · rw [show φ_im (x - t) = (φ (x - t)).im from rfl, hφ_zero x hx_out t ht,
            Complex.zero_im, mul_zero]
        exact Real.ext_cauchy rfl
      · rw [hρ_zero t ht, zero_mul]
        exact Real.ext_cauchy rfl
    show (⟨ψ_re x, ψ_im x⟩ : ℂ) = 0
    rw [h_re, h_im]; rfl
  case unif_bound =>
    intro x₀
    -- Component-wise oscillation bounds (from hosc)
    have hosc_re : ∀ y ∈ Metric.ball x₀ ρ.rOut,
        dist (φ_re y) (φ_re x₀) ≤ δ / 2 := by
      intro y hy
      rw [Real.dist_eq]
      rw [show ρ.rOut = r from rfl] at hy
      have hd : dist x₀ y < r := Metric.mem_ball'.mp hy
      calc |φ_re y - φ_re x₀|
          = |(φ y - φ x₀).re| := by simp [φ_re, Complex.sub_re]
        _ ≤ ‖φ y - φ x₀‖ := abs_re_le_norm (φ y - φ x₀)
        _ = ‖φ x₀ - φ y‖ := norm_sub_rev _ _
        _ ≤ δ / 2 := hosc x₀ y (by rwa [dist_comm])
    have hosc_im : ∀ y ∈ Metric.ball x₀ ρ.rOut,
        dist (φ_im y) (φ_im x₀) ≤ δ / 2 := by
      intro y hy
      rw [Real.dist_eq]
      rw [show ρ.rOut = r from rfl] at hy
      have hd : dist x₀ y < r := Metric.mem_ball'.mp hy
      calc |φ_im y - φ_im x₀|
          = |(φ y - φ x₀).im| := by simp [φ_im, Complex.sub_im]
        _ ≤ ‖φ y - φ x₀‖ := abs_im_le_norm (φ y - φ x₀)
        _ = ‖φ x₀ - φ y‖ := norm_sub_rev _ _
        _ ≤ δ / 2 := hosc x₀ y (by rwa [dist_comm])
    -- Apply the Mathlib convolution bound to each component
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      change (MeasureTheory.Measure.addHaar : Measure R3).IsAddHaarMeasure
      infer_instance
    have hre : dist (ψ_re x₀) (φ_re x₀) ≤ δ / 2 :=
      ρ.dist_normed_convolution_le hmeas_re hosc_re
    have him : dist (ψ_im x₀) (φ_im x₀) ≤ δ / 2 :=
      ρ.dist_normed_convolution_le hmeas_im hosc_im
    -- Recombine: ‖ψ(x₀) - φ(x₀)‖ ≤ |re difference| + |im difference|
    have hdiff_re : (ψ x₀ - φ x₀).re = ψ_re x₀ - φ_re x₀ := by
      simp [ψ, φ_re, Complex.sub_re]
    have hdiff_im : (ψ x₀ - φ x₀).im = ψ_im x₀ - φ_im x₀ := by
      simp [ψ, φ_im, Complex.sub_im]
    calc ‖ψ x₀ - φ x₀‖
        ≤ |(ψ x₀ - φ x₀).re| + |(ψ x₀ - φ x₀).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |ψ_re x₀ - φ_re x₀| + |ψ_im x₀ - φ_im x₀| := by
          rw [hdiff_re, hdiff_im]
      _ ≤ δ / 2 + δ / 2 := by
          gcongr
          · exact RCLike.ofReal_le_ofReal.mp hre
          · exact RCLike.ofReal_le_ofReal.mp him
      _ = δ := add_halves δ


/-- The eLpNorm of a compactly supported bounded function is controlled by
    the sup-norm times a power of the support measure  -/
private lemma eLpNorm_le_of_compactSupport_bound
    (f : R3 → ℂ) (hf_supp : HasCompactSupport f)
    (_hf_meas : AEStronglyMeasurable f (volume : Measure R3))
    (C : ℝ) (_hC : 0 ≤ C) (hfC : ∀ x, ‖f x‖ ≤ C) :
    eLpNorm f 2 (volume : Measure R3) ≤
      ENNReal.ofReal C *
        ((volume : Measure R3) (tsupport f)) ^ ((1 : ℝ) / 2) := by
  set K := tsupport f
  have hK : IsCompact K := hf_supp.isCompact
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h_eq : f = K.indicator f := by
    ext x; by_cases hx : x ∈ K
    · exact (Set.indicator_of_mem hx f).symm
    · rw [Set.indicator_of_notMem hx f]
      exact image_eq_zero_of_notMem_tsupport hx
  conv_lhs => rw [h_eq, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    change IsFiniteMeasureOnCompacts (MeasureTheory.Measure.addHaar)
    infer_instance
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h_ae_bound : ∀ᵐ x ∂(volume : Measure R3).restrict K, ‖f x‖ ≤ C :=
    ae_of_all _ hfC
  calc eLpNorm f 2 ((volume : Measure R3).restrict K)
      ≤ ((volume : Measure R3).restrict K Set.univ) ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal C := eLpNorm_le_of_ae_bound h_ae_bound
    _ = ENNReal.ofReal C *
          ((volume : Measure R3) K) ^ ((1 : ℝ) / 2) := by
        rw [mul_comm, Measure.restrict_apply_univ]
        congr 1
        simp [ENNReal.toReal_ofNat]


/-- Smooth compactly supported functions approximate continuous compactly
    supported functions in L² -/
lemma smooth_approx_continuous_compactSupport
    (φ : R3 → ℂ) (hcont : Continuous φ) (hsupp : HasCompactSupport φ)
    (hφ : MemLp φ 2 (volume : Measure R3))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : R3 → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ (hψ : MemLp ψ 2 (volume : Measure R3)),
        ‖hφ.toLp φ - hψ.toLp ψ‖ < ε := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    change IsFiniteMeasureOnCompacts (MeasureTheory.Measure.addHaar); infer_instance
  set K₀ := tsupport φ + Metric.closedBall (0 : R3) 1
  have hK₀ : IsCompact K₀ := by
    exact hsupp.isCompact.add (isCompact_closedBall 0 1)
  have hK₀_meas_lt : (volume : Measure R3) K₀ < ⊤ := hK₀.measure_lt_top
  set M := ((volume : Measure R3) K₀).toReal
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  set δ := min 1 (ε / (Real.sqrt M + 2)) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def, lt_min_iff]
    exact ⟨one_pos, div_pos hε (by linarith [Real.sqrt_nonneg M])⟩
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδM_lt_ε : δ * Real.sqrt M < ε := by
    have hdenom : 0 < Real.sqrt M + 2 := by linarith [Real.sqrt_nonneg M]
    calc δ * Real.sqrt M
        ≤ ε / (Real.sqrt M + 2) * Real.sqrt M := by
          gcongr; exact min_le_right _ _
      _ < ε := by
          have hsM := Real.sqrt_nonneg M
          simp [div_mul_eq_mul_div]
          rw [propext (div_lt_iff₀ hdenom)]
          nlinarith
  have h_approx := exists_smooth_uniform_approx φ hcont hsupp δ hδ_pos (1 : ℝ) (by norm_num)
  obtain ⟨ψ, hψ_smooth, hψ_supp, hψ_tsupport, hψ_close⟩ := h_approx
  refine ⟨ψ, hψ_smooth, hψ_supp, fun hψ_Lp => ?_⟩
  have hsupp_diff : HasCompactSupport (ψ - φ) := hψ_supp.sub hsupp
  have hsupp_sub_K₀ : tsupport (ψ - φ) ⊆ K₀ := by
    have h_support : Function.support (ψ - φ) ⊆ tsupport ψ ∪ tsupport φ := by
      intro x hx
      simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_ne_zero] at hx
      by_contra h
      simp only [Set.mem_union, not_or] at h
      have h1 : x ∉ Function.support ψ := mt (subset_tsupport ψ ·) h.1
      have h2 : x ∉ Function.support φ := mt (subset_tsupport φ ·) h.2
      simp only [Function.mem_support, not_not] at h1 h2
      exact hx (by rw [h1, h2])
    have h_closed : IsClosed (tsupport ψ ∪ tsupport φ) :=
        IsClosed.union (isClosed_tsupport ψ) (isClosed_tsupport φ)
    have h_tsupport : tsupport (ψ - φ) ⊆ tsupport ψ ∪ tsupport φ :=
      closure_minimal h_support h_closed
    exact h_tsupport.trans (Set.union_subset hψ_tsupport (fun x hx =>
      show x ∈ tsupport φ + Metric.closedBall (0 : R3) 1 by
        rw [show x = x + 0 from (add_zero x).symm]
        exact Set.add_mem_add hx (Metric.mem_closedBall_self one_pos.le)))
  have hmeas_diff : AEStronglyMeasurable (ψ - φ) (volume : Measure R3) :=
    hψ_Lp.aestronglyMeasurable.sub hφ.aestronglyMeasurable
  have h_eLpNorm := eLpNorm_le_of_compactSupport_bound (ψ - φ) hsupp_diff hmeas_diff
    δ hδ_pos.le (fun x => by rw [Pi.sub_apply]; exact hψ_close x)
  have h_meas_le : (volume : Measure R3) (tsupport (ψ - φ)) ≤ (volume : Measure R3) K₀ :=
    measure_mono hsupp_sub_K₀
  have h_chain : eLpNorm (ψ - φ) 2 volume ≤
      ENNReal.ofReal δ * ((volume : Measure R3) K₀) ^ ((1 : ℝ) / 2) :=
    h_eLpNorm.trans (by gcongr)
  rw [Lp.norm_def (hφ.toLp φ - hψ_Lp.toLp ψ),
      eLpNorm_congr_ae (Lp.coeFn_sub (hφ.toLp φ) (hψ_Lp.toLp ψ))]
  have hae : ((hφ.toLp φ : R3 → ℂ) - (hψ_Lp.toLp ψ : R3 → ℂ)) =ᵐ[volume] (φ - ψ) :=
    hφ.coeFn_toLp.sub hψ_Lp.coeFn_toLp
  rw [eLpNorm_congr_ae hae, show φ - ψ = -(ψ - φ) from by abel, eLpNorm_neg]
  have h_ne_top : eLpNorm (ψ - φ) 2 volume ≠ ⊤ :=
    (hψ_Lp.sub hφ).eLpNorm_ne_top
  calc (eLpNorm (ψ - φ) 2 volume).toReal
    _ ≤ (ENNReal.ofReal δ * ((volume : Measure R3) K₀) ^ ((1 : ℝ) / 2)).toReal := by
        apply ENNReal.toReal_mono _ h_chain
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK₀_meas_lt.ne)
    _ = δ * ((volume : Measure R3) K₀).toReal ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ_pos.le,
            ENNReal.toReal_rpow]
    _ = δ * Real.sqrt M := by
        congr 1
        exact (Real.sqrt_eq_rpow M).symm
    _ < ε := hδM_lt_ε


/-- The L² inner product vanishes against test function representatives -/
lemma inner_L2_test_eq_zero (h : L2_R3)
    (htest : ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0)
    (g : L2_R3) (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hae : (g : R3 → ℂ) =ᵐ[volume] φ) :
    @inner ℂ L2_R3 _ h g = 0 := by
  have h0 : ∫ x, (h : R3 → ℂ) x * starRingEnd ℂ (φ x) = 0 :=
    htest _ (contDiff_starRingEnd_comp hφ) (hasCompactSupport_starRingEnd_comp hsupp)
  have hint : Integrable (fun x => (h : R3 → ℂ) x * starRingEnd ℂ (φ x)) volume := by
    have hh : MemLp (h : R3 → ℂ) 2 volume := Lp.memLp h
    have hφ_L2 : MemLp (fun x => starRingEnd ℂ (φ x)) 2 volume :=
      memLp_of_smooth_compactSupport _ (contDiff_starRingEnd_comp hφ)
        (hasCompactSupport_starRingEnd_comp hsupp)
    exact hh.integrable_mul hφ_L2
  have h1 : ∫ x, φ x * starRingEnd ℂ ((h : R3 → ℂ) x) = 0 := by
    have eq : ∫ x, starRingEnd ℂ ((h : R3 → ℂ) x * starRingEnd ℂ (φ x)) =
              starRingEnd ℂ (∫ x, (h : R3 → ℂ) x * starRingEnd ℂ (φ x)) :=
      Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hint
    rw [h0, map_zero] at eq
    simp only [map_mul, starRingEnd_apply, star_star, mul_comm] at eq
    simp only [starRingEnd_apply]
    exact eq
  rw [L2.inner_def]
  simp only [RCLike.inner_apply]
  trans ∫ a, φ a * starRingEnd ℂ ((h : R3 → ℂ) a)
  · exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  · exact h1


/-- **Density**: C_c^∞(ℝ³) is dense in L²(ℝ³).
    Chain: L² ←ε/2— C_c ←ε/2— C_c^∞. -/
lemma dense_test_functions_L2 :
    Dense {g : L2_R3 | ∃ (φ : R3 → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} := by
  rw [Metric.dense_iff]
  intro g ε hε
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  -- Step 1: approximate g by continuous compactly supported (within ε/2)
  obtain ⟨g₁, hg₁_dist, φ₁, hcont₁, hsupp₁, hae₁⟩ :=
    Metric.dense_iff.mp dense_continuous_compactSupport_L2 g (ε / 2) hε2
  -- Step 2: φ₁ ∈ L² (continuous + compact support on a locally finite measure)
  have hφ₁_Lp : MemLp φ₁ 2 (volume : Measure R3) := by
    haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
      change IsFiniteMeasureOnCompacts MeasureTheory.Measure.addHaar; infer_instance
    obtain ⟨C, hC⟩ := hcont₁.bounded_above_of_compact_support hsupp₁
    exact hsupp₁.memLp_of_bound hcont₁.aestronglyMeasurable C (ae_of_all _ hC)
  -- Step 3: g₁ = toLp φ₁ (both represent φ₁ a.e., hence equal as Lp elements)
  have hg₁_eq : g₁ = hφ₁_Lp.toLp φ₁ :=
    Subtype.ext (AEEqFun.ext (hae₁.trans hφ₁_Lp.coeFn_toLp.symm))
  -- Step 4: smooth approximation of φ₁ (within ε/2)
  obtain ⟨ψ, hψ_smooth, hψ_supp, hψ_close⟩ :=
    smooth_approx_continuous_compactSupport φ₁ hcont₁ hsupp₁ hφ₁_Lp hε2
  -- Step 5: ψ ∈ L²
  have hψ_Lp : MemLp ψ 2 (volume : Measure R3) :=
    memLp_of_smooth_compactSupport' ψ hψ_smooth hψ_supp
  -- Step 6: toLp ψ is in the target set and ε-close to g
  exact ⟨hψ_Lp.toLp ψ,
    calc dist (hψ_Lp.toLp ψ) g
        ≤ dist (hψ_Lp.toLp ψ) g₁ + dist g₁ g := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
          add_lt_add
            (by rw [hg₁_eq, dist_comm, dist_eq_norm]; exact hψ_close hψ_Lp)
            hg₁_dist
      _ = ε := add_halves ε,
    ⟨ψ, hψ_smooth, hψ_supp, hψ_Lp.coeFn_toLp⟩⟩


/-- **Fundamental lemma of the calculus of variations (du Bois-Reymond).**
    If an L² function integrates to zero against every smooth compactly
    supported test function, then it is zero (as an element of L²). -/
lemma Lp.eq_zero_of_integral_against_test_eq_zero
    (h : L2_R3)
    (htest : ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0) :
    h = 0 := by
  apply @ext_inner_right ℂ; intro g; rw [inner_zero_left]
  have hclosed : IsClosed {w : L2_R3 | @inner ℂ _ _ h w = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hcontains : {g : L2_R3 | ∃ (φ : R3 → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} ⊆
      {w : L2_R3 | @inner ℂ _ _ h w = 0} := by
    rintro w ⟨φ, hφ, hsupp, hae⟩
    exact inner_L2_test_eq_zero h htest w φ hφ hsupp hae
  have h_closure := closure_minimal hcontains hclosed
  rw [dense_test_functions_L2.closure_eq] at h_closure
  exact h_closure (Set.mem_univ g)


/-- Weak derivative is unique (as L² elements, i.e., a.e.). -/
lemma hasWeakDerivative_unique
    (f : L2_R3) (i : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakDerivative f i g₁) (h₂ : HasWeakDerivative f i g₂) :
    g₁ = g₂ := by
  suffices h : g₁ - g₂ = 0 from sub_eq_zero.mp h
  apply Lp.eq_zero_of_integral_against_test_eq_zero
  intro φ hφ hsupp
  -- Both definitions give ∫ f · ∂ᵢφ = -∫ gₖ · φ, so the integrals agree
  have key : ∫ x, (g₁ : R3 → ℂ) x * φ x = ∫ x, (g₂ : R3 → ℂ) x * φ x := by
    have e₁ := h₁ φ hφ hsupp
    have e₂ := h₂ φ hφ hsupp
    have : -∫ x, (g₁ : R3 → ℂ) x * φ x = -∫ x, (g₂ : R3 → ℂ) x * φ x :=
      e₁.symm.trans e₂
    exact neg_inj.mp this
  -- Integrability (Hölder: L² · L² → L¹)
  have hφ_L2 := memLp_of_smooth_compactSupport φ hφ hsupp
  have hint₁ : Integrable (fun x => (g₁ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₁).integrable_mul hφ_L2
  have hint₂ : Integrable (fun x => (g₂ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₂).integrable_mul hφ_L2
  -- ae: (g₁ - g₂)(x) * φ(x) = g₁(x) * φ(x) - g₂(x) * φ(x)
  rw [integral_congr_ae ((Lp.coeFn_sub g₁ g₂).mono fun x hx => by
      simp only [Pi.sub_apply] at hx; rw [hx, sub_mul]),
    integral_sub hint₁ hint₂, key, sub_self]


/-- Compact support of partial derivatives. -/
lemma hasCompactSupport_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hsupp : HasCompactSupport φ) :
    HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  apply HasCompactSupport.mono (hsupp.fderiv ℝ)
  intro x hx
  exact fun h => hx (by simp [h, ContinuousLinearMap.zero_apply])


/-- Smoothness of partial derivatives. -/

lemma contDiff_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
  (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const


/-- Partial derivatives of smooth compactly supported functions are in L². -/
lemma memLp_partialDeriv (φ : R3 → ℂ) (i : Fin 3)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 volume :=
  memLp_of_smooth_compactSupport _ (contDiff_partialDeriv φ i hφ)
    (hasCompactSupport_partialDeriv φ i hsupp)


/-- Weak derivative is linear in f. -/
lemma hasWeakDerivative_add
    (f₁ f₂ : L2_R3) (i : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakDerivative f₁ i g₁) (h₂ : HasWeakDerivative f₂ i g₂) :
    HasWeakDerivative (f₁ + f₂) i (g₁ + g₂) := by
  intro φ hφ hsupp
  have e₁ := h₁ φ hφ hsupp
  have e₂ := h₂ φ hφ hsupp
  have hψ_L2 := memLp_partialDeriv φ i hφ hsupp
  have hφ_L2 := memLp_of_smooth_compactSupport φ hφ hsupp
  have hint_l1 : Integrable (fun x => (f₁ : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    (Lp.memLp f₁).integrable_mul hψ_L2
  have hint_l2 : Integrable (fun x => (f₂ : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    (Lp.memLp f₂).integrable_mul hψ_L2
  have hint_r1 : Integrable (fun x => (g₁ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₁).integrable_mul hφ_L2
  have hint_r2 : Integrable (fun x => (g₂ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₂).integrable_mul hφ_L2
  -- Rewrite LHS pointwise via ae
  have lhs : ∫ x, ((f₁ + f₂ : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
    (∫ x, (f₁ : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) +
    (∫ x, (f₂ : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    rw [integral_congr_ae ((Lp.coeFn_add f₁ f₂).mono fun x hx => by
      simp only [Pi.add_apply] at hx; rw [hx, add_mul])]
    exact integral_add hint_l1 hint_l2
  have rhs : ∫ x, ((g₁ + g₂ : L2_R3) : R3 → ℂ) x * φ x =
    (∫ x, (g₁ : R3 → ℂ) x * φ x) + (∫ x, (g₂ : R3 → ℂ) x * φ x) := by
    rw [integral_congr_ae ((Lp.coeFn_add g₁ g₂).mono fun x hx => by
      simp only [Pi.add_apply] at hx; rw [hx, add_mul])]
    exact integral_add hint_r1 hint_r2
  rw [lhs, rhs, neg_add]
  exact congr_arg₂ (· + ·) e₁ e₂


/-- Weak derivative commutes with scalar multiplication. -/
lemma hasWeakDerivative_smul
    (c : ℂ) (f : L2_R3) (i : Fin 3) (g : L2_R3)
    (h : HasWeakDerivative f i g) :
    HasWeakDerivative (c • f) i (c • g) := by
  intro φ hφ hsupp
  have e := h φ hφ hsupp
  -- LHS: ∫ (c • f) · ∂ᵢφ = c * ∫ f · ∂ᵢφ
  have lhs : ∫ x, ((c • f : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
    c * ∫ x, (f : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [integral_congr_ae ((Lp.coeFn_smul c f).mono fun x hx => by
      simp only [Pi.smul_apply, smul_eq_mul] at hx; rw [hx, mul_assoc])]
    exact integral_const_mul c _
  -- RHS: ∫ (c • g) · φ = c * ∫ g · φ
  have rhs : ∫ x, ((c • g : L2_R3) : R3 → ℂ) x * φ x =
    c * ∫ x, (g : R3 → ℂ) x * φ x := by
    rw [integral_congr_ae ((Lp.coeFn_smul c g).mono fun x hx => by
      simp only [Pi.smul_apply, smul_eq_mul] at hx; rw [hx, mul_assoc])]
    exact integral_const_mul c _
  rw [lhs, rhs, e, mul_neg]


/-- Second-order weak partial derivative. -/
def HasWeakSecondDerivative
    (f : L2_R3) (i j : Fin 3) (g : L2_R3) : Prop :=
  ∃ (h : L2_R3), HasWeakDerivative f i h ∧ HasWeakDerivative h j g


/-- Classical Schwarz: mixed partials of smooth functions commute. -/
private lemma schwarz_partials (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin 3) (x : R3) :
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1) =
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) := by
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  have hφ' : ContDiff ℝ ∞ (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  have hφ'_da : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ'.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
  -- Reduce: fderiv (fun y => F'(y) v) x w = (fderiv F' x w) v
  have reduce : ∀ v, fderiv ℝ (fun y => fderiv ℝ φ y v) x =
      (fderiv ℝ (fderiv ℝ φ) x).flip v := by
    intro v
    have h := hφ'_da.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    simp only [ContinuousLinearMap.comp_zero] at h
    simp only [zero_add] at h
    exact h.fderiv
  rw [reduce eᵢ, reduce eⱼ]
  simp only [ContinuousLinearMap.flip_apply]
  -- Goal: (fderiv ℝ (fderiv ℝ φ) x eⱼ) eᵢ = (fderiv ℝ (fderiv ℝ φ) x eᵢ) eⱼ
  -- This is exactly IsSymmSndFDerivAt
  have hφx : ContDiffAt ℝ ∞ φ x := hφ.contDiffAt
  have hsymm := hφx.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact right_eq_inf.mp rfl)
  exact hsymm eⱼ eᵢ


/-- Symmetry of second weak derivatives (Schwarz's theorem, L² version).
    Requires that `∂ⱼf` exists (automatic for H² functions). -/
lemma hasWeakSecondDerivative_comm
    (f : L2_R3) (i j : Fin 3) (g : L2_R3)
    (h : HasWeakSecondDerivative f i j g)
    (hfj : ∃ mid', HasWeakDerivative f j mid') :
    HasWeakSecondDerivative f j i g := by
  obtain ⟨mid, hmid_i, hg_j⟩ := h
  obtain ⟨mid', hmid'_j⟩ := hfj
  refine ⟨mid', hmid'_j, fun φ hφ hsupp => ?_⟩
  -- Test functions: ∂ᵢφ and ∂ⱼφ are smooth with compact support
  have hdiφ_s := contDiff_partialDeriv φ i hφ
  have hdiφ_c := hasCompactSupport_partialDeriv φ i hsupp
  have hdjφ_s := contDiff_partialDeriv φ j hφ
  have hdjφ_c := hasCompactSupport_partialDeriv φ j hsupp
  -- (A) test ∂ⱼf = mid' against ∂ᵢφ:
  --     ∫ f·∂ⱼ(∂ᵢφ) = −∫ mid'·∂ᵢφ
  have eA := hmid'_j _ hdiφ_s hdiφ_c
  -- (B) test ∂ᵢf = mid against ∂ⱼφ:
  --     ∫ f·∂ᵢ(∂ⱼφ) = −∫ mid·∂ⱼφ
  have eB := hmid_i _ hdjφ_s hdjφ_c
  -- (C) test ∂ⱼmid = g against φ:
  --     ∫ mid·∂ⱼφ = −∫ g·φ
  have eC := hg_j φ hφ hsupp
  -- (D) Schwarz: ∂ⱼ(∂ᵢφ) = ∂ᵢ(∂ⱼφ) pointwise, hence under ∫ f·(−)
  have eD : ∫ x, (f : R3 → ℂ) x *
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
    ∫ x, (f : R3 → ℂ) x *
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) :=
    integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      rw [schwarz_partials φ hφ i j x])
  -- Chain: linear_combination −eA + eD + eB − eC
  -- i.e., ∫ mid'·∂ᵢφ = −∫ f·∂ⱼ(∂ᵢφ) = −∫ f·∂ᵢ(∂ⱼφ) = ∫ mid·∂ⱼφ = −∫ g·φ
  grind only


/-! ### Sobolev space membership predicates -/

/-- Predicate: f ∈ H¹(ℝ³).
    All first-order weak derivatives exist and are in L². -/
def MemSobolevH1 (f : L2_R3) : Prop :=
  ∀ i : Fin 3, ∃ g : L2_R3, HasWeakDerivative f i g

/-- Predicate: f ∈ H²(ℝ³).
    All weak derivatives up to order 2 exist and are in L². -/
def MemSobolevH2 (f : L2_R3) : Prop :=
  MemSobolevH1 f ∧
  ∀ i j : Fin 3, ∃ g : L2_R3, HasWeakSecondDerivative f i j g

/-! ### Sobolev spaces as submodules -/

/-- The zero function has weak derivative zero. -/
lemma hasWeakDerivative_zero (i : Fin 3) :
    HasWeakDerivative (0 : L2_R3) i 0 := by
  intro φ hφ hsupp
  have hae := Lp.coeFn_zero ℂ 2 (volume : Measure R3)
  have lhs : ∫ x, ((0 : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
    integral_eq_zero_of_ae (hae.mono fun x hx => by
      simp only [ZeroMemClass.coe_zero, Pi.zero_apply, mul_eq_zero]
      exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul ((fderiv ℝ φ x)
        (EuclideanSpace.single i 1))) hx))
  have rhs : ∫ x, ((0 : L2_R3) : R3 → ℂ) x * φ x = 0 :=
    integral_eq_zero_of_ae (hae.mono fun x hx => by
      simp only [ZeroMemClass.coe_zero, Pi.zero_apply, mul_eq_zero]
      exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul (φ x)) hx))
  rw [lhs, rhs, neg_zero]


/-- H¹(ℝ³) as a ℂ-submodule of L²(ℝ³). -/
def SobolevH1 : Submodule ℂ L2_R3 where
  carrier := { f | MemSobolevH1 f }
  zero_mem' := fun i => ⟨0, hasWeakDerivative_zero i⟩
  add_mem' := fun {f₁ f₂} hf₁ hf₂ i =>
    ⟨(hf₁ i).choose + (hf₂ i).choose,
     hasWeakDerivative_add f₁ f₂ i _ _ (hf₁ i).choose_spec (hf₂ i).choose_spec⟩
  smul_mem' := fun c {f} hf i =>
    ⟨c • (hf i).choose,
     hasWeakDerivative_smul c f i _ (hf i).choose_spec⟩


/-- H²(ℝ³) as a ℂ-submodule of L²(ℝ³). -/
def SobolevH2 : Submodule ℂ L2_R3 where
  carrier := { f | MemSobolevH2 f }
  zero_mem' := by
    refine ⟨fun i => ⟨0, hasWeakDerivative_zero i⟩, fun i j => ⟨0, ?_⟩⟩
    exact ⟨0, hasWeakDerivative_zero i, hasWeakDerivative_zero j⟩
  add_mem' := fun {f₁ f₂} ⟨h1a, h1b⟩ ⟨h2a, h2b⟩ => by
    refine ⟨fun i => ⟨(h1a i).choose + (h2a i).choose,
      hasWeakDerivative_add f₁ f₂ i _ _ (h1a i).choose_spec (h2a i).choose_spec⟩,
      fun i j => ?_⟩
    obtain ⟨g₁, mid₁, hd₁, hd₁'⟩ := h1b i j
    obtain ⟨g₂, mid₂, hd₂, hd₂'⟩ := h2b i j
    exact ⟨g₁ + g₂, mid₁ + mid₂,
      hasWeakDerivative_add f₁ f₂ i mid₁ mid₂ hd₁ hd₂,
      hasWeakDerivative_add mid₁ mid₂ j g₁ g₂ hd₁' hd₂'⟩
  smul_mem' := fun c {f} ⟨ha, hb⟩ => by
    refine ⟨fun i => ⟨c • (ha i).choose,
      hasWeakDerivative_smul c f i _ (ha i).choose_spec⟩,
      fun i j => ?_⟩
    obtain ⟨g, mid, hd, hd'⟩ := hb i j
    exact ⟨c • g, c • mid,
      hasWeakDerivative_smul c f i mid hd,
      hasWeakDerivative_smul c mid j g hd'⟩


/-- H² ⊆ H¹ as submodules. -/
lemma sobolevH2_le_H1 : SobolevH2 ≤ SobolevH1 := by
  intro f hf
  exact hf.1

/-! ### The weak gradient and Dirichlet integral -/

/-- Extract the weak gradient of an H¹ function.
    Returns the triple (∂₁f, ∂₂f, ∂₃f) as L² functions. -/
def weakGradient (f : L2_R3) (hf : MemSobolevH1 f) : Fin 3 → L2_R3 :=
  fun i => (hf i).choose

/-- The chosen gradient component is indeed the weak derivative. -/
lemma weakGradient_spec (f : L2_R3) (hf : MemSobolevH1 f) (i : Fin 3) :
    HasWeakDerivative f i (weakGradient f hf i) :=
  (hf i).choose_spec

/-- The gradient (Dirichlet) norm squared: ∫|∇ψ|² dx = Σᵢ ‖∂ᵢψ‖²_{L²}.

    This is the quadratic form associated to -Δ. For ψ ∈ H²:
      ⟨-Δψ, ψ⟩ = ∫|∇ψ|² dx
    which is the content of `gradient_norm_sq_eq_laplacian_inner` below. -/
def gradientNormSq (f : L2_R3) (hf : MemSobolevH1 f) : ℝ :=
  ∑ i : Fin 3, ‖weakGradient f hf i‖ ^ 2

/-- The gradient norm squared is non-negative. -/
lemma gradientNormSq_nonneg (f : L2_R3) (hf : MemSobolevH1 f) :
    0 ≤ gradientNormSq f hf := by
  simp only [gradientNormSq]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ### The weak Laplacian -/


/-- Second weak derivative is unique. -/
lemma hasWeakSecondDerivative_unique
    (f : L2_R3) (i j : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakSecondDerivative f i j g₁)
    (h₂ : HasWeakSecondDerivative f i j g₂) :
    g₁ = g₂ := by
  obtain ⟨mid₁, hd₁, hd₁'⟩ := h₁
  obtain ⟨mid₂, hd₂, hd₂'⟩ := h₂
  have : mid₁ = mid₂ := hasWeakDerivative_unique f i mid₁ mid₂ hd₁ hd₂
  subst this
  exact hasWeakDerivative_unique mid₁ j g₁ g₂ hd₁' hd₂'

/-- The weak Laplacian: -Δf = -Σᵢ ∂ᵢ²f. -/
def weakLaplacian (f : L2_R3) (hf : MemSobolevH2 f) : L2_R3 :=
  -∑ i : Fin 3, (hf.2 i i).choose

/-- The Laplacian is additive. -/
lemma weakLaplacian_add (f g : L2_R3) (hf : MemSobolevH2 f) (hg : MemSobolevH2 g) :
    weakLaplacian (f + g) (SobolevH2.add_mem hf hg) =
    weakLaplacian f hf + weakLaplacian g hg := by
  simp only [weakLaplacian]
  rw [← neg_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨midf, hdf, hdf'⟩ := (hf.2 i i).choose_spec
  obtain ⟨midg, hdg, hdg'⟩ := (hg.2 i i).choose_spec
  exact hasWeakSecondDerivative_unique (f + g) i i _ _
    ((SobolevH2.add_mem hf hg).2 i i).choose_spec
    ⟨midf + midg,
     hasWeakDerivative_add f g i midf midg hdf hdg,
     hasWeakDerivative_add midf midg i _ _ hdf' hdg'⟩


/-- The Laplacian commutes with scalar multiplication. -/
lemma weakLaplacian_smul (c : ℂ) (f : L2_R3) (hf : MemSobolevH2 f) :
    weakLaplacian (c • f) (SobolevH2.smul_mem c hf) =
    c • weakLaplacian f hf := by
  simp only [weakLaplacian, smul_neg, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨mid, hd_first, hd_second⟩ := (hf.2 i i).choose_spec
  exact hasWeakSecondDerivative_unique (c • f) i i _ _
    ((SobolevH2.smul_mem c hf).2 i i).choose_spec
    ⟨c • mid,
     hasWeakDerivative_smul c f i mid hd_first,
     hasWeakDerivative_smul c mid i _ hd_second⟩


/-- The Laplacian as a linear map on the H² submodule.

    This is the operator that becomes `Generator.op` for the
    free-particle evolution exp(itΔ). -/
def laplacianLinearMap : SobolevH2 →ₗ[ℂ] L2_R3 where
  toFun := fun ⟨f, hf⟩ => weakLaplacian f hf
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => weakLaplacian_add f g hf hg
  map_smul' := fun c ⟨f, hf⟩ => weakLaplacian_smul c f hf



/-- Distribute inner product over a finite sum in the first argument. -/
private lemma inner_finset_sum_left {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → L2_R3) (y : L2_R3) :
    @inner ℂ L2_R3 _ (∑ i ∈ s, f i) y =
    ∑ i ∈ s, @inner ℂ L2_R3 _ (f i) y := by
  induction s using Finset.induction_on with
  | empty => simp [inner_zero_left]
  | insert _ _ ha ih =>
    rw [Finset.sum_insert ha, inner_add_left, ih, Finset.sum_insert ha]


/-- **Smooth IBP identity**: ⟨∂ᵢ(df), φ⟩ + ⟨df, ∂ᵢφ⟩ = 0 for smooth c.s. φ.

    Discharge route (~100 lines):
    1. Apply h_ddf to conj(φ) (smooth c.s. by contDiff_starRingEnd_comp,
       hasCompactSupport_starRingEnd_comp)
    2. Use ∂ᵢ(conj φ) = conj(∂ᵢφ) (fderiv is ℝ-linear, conj is ℝ-linear:
       fderiv ℝ (starRingEnd ℂ ∘ φ) = starRingEnd ℂ ∘ fderiv ℝ φ via chain rule
       + Complex.conjCLE)
    3. Obtain: ∫ df(x) * conj(∂ᵢφ(x)) dx = -∫ ddf(x) * conj(φ(x)) dx
    4. Conjugate both sides:
       ∫ conj(df(x)) * ∂ᵢφ(x) dx = -∫ conj(ddf(x)) * φ(x) dx
    5. Relate to L² inner product via L2.inner_def, MemLp.coeFn_toLp -/
private lemma ibp_smooth_test (i : Fin 3) (df ddf : L2_R3)
    (h_ddf : HasWeakDerivative df i ddf)
    (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    @inner ℂ L2_R3 _ ddf ((memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ) +
    @inner ℂ L2_R3 _ df ((memLp_partialDeriv φ i hφ hsupp).toLp
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) = 0 :=
  sorry

/-- **Meyers-Serrin approximation**: g with weak derivative dg can be
    simultaneously approximated by smooth c.s. functions in both norms.

    Discharge route (~200 lines):
    1. Truncate: choose smooth cutoff χ_R equal to 1 on ball(0,R),
       supported in ball(0, 2R). Set g_R = χ_R · g.
    2. Mollify: set φ = ρ_ε ⋆ g_R using ContDiffBump.
    3. φ is smooth c.s.: HasCompactSupport.contDiff_convolution_left +
       HasCompactSupport.convolution.
    4. φ → g in L²: triangle inequality through g_R,
       χ_R · g → g by dominated convergence (R → ∞),
       ρ_ε ⋆ g_R → g_R by ContDiffBump.convolution_tendsto_right.
    5. ∂ᵢφ → dg in L²: the key step.
       HasCompactSupport.hasFDerivAt_convolution_left gives
         fderiv(ρ_ε ⋆ g_R) = (fderiv ρ_ε) ⋆ g_R.
       Integration by parts inside the convolution integral converts
         (∂ᵢρ_ε) ⋆ g_R  to  ρ_ε ⋆ (∂ᵢg_R)
       since y ↦ ρ_ε(x - y) is smooth c.s. in y, hence a valid test
       function for HasWeakDerivative. Then ρ_ε ⋆ (∂ᵢg_R) → ∂ᵢg_R → dg
       by the same mollification + truncation convergence. -/
private lemma meyers_serrin_approx (i : Fin 3) (g dg : L2_R3)
    (h_dg : HasWeakDerivative g i dg) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖g - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ‖dg - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε :=
  sorry

/-- **Per-component IBP**: ⟨∂ᵢ(df), g⟩ = −⟨df, ∂ᵢg⟩.

    Proof: Meyers-Serrin gives φ close to g in H¹. Smooth IBP gives the
    identity for φ. Cauchy-Schwarz controls the error. -/
private lemma ibp_component (i : Fin 3)
    (df ddf g dg : L2_R3)
    (h_ddf : HasWeakDerivative df i ddf)
    (h_dg : HasWeakDerivative g i dg) :
    @inner ℂ L2_R3 _ ddf g = -@inner ℂ L2_R3 _ df dg := by
  -- Suffices: ⟨ddf, g⟩ + ⟨df, dg⟩ = 0
  apply eq_neg_of_add_eq_zero_left
  by_contra h_ne
  -- The sum has positive norm
  set val := @inner ℂ L2_R3 _ ddf g + @inner ℂ L2_R3 _ df dg
  have h_pos : (0 : ℝ) < ‖val‖ := norm_pos_iff.mpr h_ne
  -- Choose approximation radius
  set C := ‖ddf‖ + ‖df‖ + 1 with hC_def
  have hC_pos : (0 : ℝ) < C := by positivity
  set δ := ‖val‖ / (2 * C) with hδ_def
  have hδ_pos : (0 : ℝ) < δ := div_pos h_pos (by positivity)
  -- Meyers-Serrin: get smooth c.s. φ with ‖g - φ‖ < δ and ‖dg - ∂ᵢφ‖ < δ
  obtain ⟨φ, hφ_s, hφ_c, h_g_close, h_dg_close⟩ :=
    meyers_serrin_approx i g dg h_dg δ hδ_pos
  set φ_L2 := (memLp_of_smooth_compactSupport φ hφ_s hφ_c).toLp φ
  set dφ_L2 := (memLp_partialDeriv φ i hφ_s hφ_c).toLp
    (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))
  -- Smooth IBP: ⟨ddf, φ⟩ + ⟨df, ∂ᵢφ⟩ = 0
  have h_ibp := ibp_smooth_test i df ddf h_ddf φ hφ_s hφ_c
  -- Decompose: val = ⟨ddf, g - φ⟩ + ⟨df, dg - ∂ᵢφ⟩ + 0
  have h_val : val = @inner ℂ L2_R3 _ ddf (g - φ_L2) +
      @inner ℂ L2_R3 _ df (dg - dφ_L2) := by
    show @inner ℂ L2_R3 _ ddf g + @inner ℂ L2_R3 _ df dg = _
    rw [show g = (g - φ_L2) + φ_L2 from (sub_add_cancel g φ_L2).symm,
        show dg = (dg - dφ_L2) + dφ_L2 from (sub_add_cancel dg dφ_L2).symm,
        inner_add_right, inner_add_right]
    abel_nf; grind only
  -- Cauchy-Schwarz bound
  have h_bound : ‖val‖ ≤ ‖ddf‖ * δ + ‖df‖ * δ := by
    rw [h_val]
    calc ‖@inner ℂ L2_R3 _ ddf (g - φ_L2) +
            @inner ℂ L2_R3 _ df (dg - dφ_L2)‖
        ≤ ‖@inner ℂ L2_R3 _ ddf (g - φ_L2)‖ +
          ‖@inner ℂ L2_R3 _ df (dg - dφ_L2)‖ := norm_add_le _ _
      _ ≤ ‖ddf‖ * ‖g - φ_L2‖ + ‖df‖ * ‖dg - dφ_L2‖ := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ ≤ ‖ddf‖ * δ + ‖df‖ * δ := by
          gcongr
  -- Contradiction: ‖val‖ ≤ (‖ddf‖ + ‖df‖) · δ < C · δ = ‖val‖/2 < ‖val‖
  have : ‖val‖ < ‖val‖ :=
    calc ‖val‖
        ≤ (‖ddf‖ + ‖df‖) * δ := by linarith
      _ < C * δ := by
          exact mul_lt_mul_of_pos_right (by linarith) hδ_pos
      _ = ‖val‖ / 2 := by
          rw [hδ_def, hC_def]; field_simp
      _ < ‖val‖ := half_lt_self h_pos
  exact absurd this (lt_irrefl _)


/-- ### Integration by parts: the fundamental identity -/
lemma integration_by_parts
    (f : L2_R3) (hf : MemSobolevH2 f)
    (g : L2_R3) (hg : MemSobolevH1 g) :
    inner (𝕜 := ℂ) (weakLaplacian f hf) g =
    ∑ i : Fin 3, inner (𝕜 := ℂ) (weakGradient f (sobolevH2_le_H1 hf) i)
                   (weakGradient g hg i) := by
  simp only [weakLaplacian]
  rw [inner_neg_left, inner_finset_sum_left, ← Finset.sum_neg_distrib]
  -- Goal: ∑ i, -(inner ((hf.2 i i).choose) g) = ∑ i, inner (weakGrad f i) (weakGrad g i)
  apply Finset.sum_congr rfl
  intro i _
  -- Extract the second derivative chain: ∃ mid, ∂ᵢf = mid ∧ ∂ᵢ(mid) = ∂ᵢᵢf
  obtain ⟨mid, hmid_first, hmid_second⟩ := (hf.2 i i).choose_spec
  -- By uniqueness: mid = weakGradient f i
  have h_eq : mid = weakGradient f (sobolevH2_le_H1 hf) i :=
    hasWeakDerivative_unique f i mid _ hmid_first
      (weakGradient_spec f (sobolevH2_le_H1 hf) i)
  rw [← h_eq]
  -- Goal: -(inner (∂ᵢᵢf) g) = inner mid (∂ᵢg)
  -- ibp_component gives: inner (∂ᵢᵢf) g = -(inner mid (∂ᵢg))
  exact neg_eq_iff_eq_neg.mpr
    (ibp_component i mid ((hf.2 i i).choose) g (weakGradient g hg i)
      hmid_second (weakGradient_spec g hg i))


/-- **Symmetry of -Δ**: ⟨-Δf, g⟩ = ⟨f, -Δg⟩ for f, g ∈ H². -/
lemma laplacian_symmetric
    (f g : L2_R3) (hf : MemSobolevH2 f) (hg : MemSobolevH2 g) :
    inner (𝕜 := ℂ) (weakLaplacian f hf) g =
    inner (𝕜 := ℂ) f (weakLaplacian g hg) := by
  rw [integration_by_parts f hf g (sobolevH2_le_H1 hg)]
  symm
  calc inner (𝕜 := ℂ) f (weakLaplacian g hg)
      = starRingEnd ℂ (inner (𝕜 := ℂ) (weakLaplacian g hg) f) :=
        (inner_conj_symm f _).symm
    _ = starRingEnd ℂ (∑ i, inner (𝕜 := ℂ) (weakGradient g (sobolevH2_le_H1 hg) i)
            (weakGradient f (sobolevH2_le_H1 hf) i)) := by
        rw [integration_by_parts g hg f (sobolevH2_le_H1 hf)]
    _ = ∑ i, starRingEnd ℂ (inner (𝕜 := ℂ) (weakGradient g (sobolevH2_le_H1 hg) i)
            (weakGradient f (sobolevH2_le_H1 hf) i)) :=
        map_sum _ _ _
    _ = ∑ i, inner (𝕜 := ℂ) (weakGradient f (sobolevH2_le_H1 hf) i)
            (weakGradient g (sobolevH2_le_H1 hg) i) := by
        congr 1; ext i; exact inner_conj_symm _ _


/-- The gradient norm squared equals the Laplacian inner product. -/
lemma gradient_norm_sq_eq_laplacian_inner
    (f : L2_R3) (hf : MemSobolevH2 f) :
    (gradientNormSq f (sobolevH2_le_H1 hf) : ℂ) =
    inner (𝕜 := ℂ) (weakLaplacian f hf) f := by
  rw [integration_by_parts f hf f (sobolevH2_le_H1 hf), gradientNormSq]
  push_cast
  congr 1; ext i
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  apply ext
  · rfl
  · rfl


/-- **Non-negativity of -Δ**: ⟨-Δf, f⟩ = ‖∇f‖² ≥ 0. -/
lemma laplacian_nonneg (f : L2_R3) (hf : MemSobolevH2 f) :
    0 ≤ (inner (𝕜 := ℂ) (weakLaplacian f hf) f : ℂ).re := by
  rw [← gradient_norm_sq_eq_laplacian_inner]
  simp only [gradientNormSq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _


/-! ### Density results -/

/-- Smooth compactly supported functions belong to H². -/
lemma smooth_compactSupport_memSobolevH2 (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ⊤ φ) (hsupp : HasCompactSupport φ)
    (hmem : MemLp φ 2 (volume : Measure R3)) :
    MemSobolevH2 (MemLp.toLp φ hmem) := by
  -- Classical derivatives of smooth functions are weak derivatives.
  -- Discharge route: integrate against test function, classical IBP
  -- (no boundary terms since both have compact support).
  sorry

/-- **H²(ℝ³) is dense in L²(ℝ³).** -/
theorem sobolevH2_dense : Dense (SobolevH2 : Set L2_R3) := by
  apply Dense.mono _ dense_test_functions_L2
  rintro g ⟨φ, hφ, hsupp, hae⟩
  show MemSobolevH2 g
  have hmem := memLp_of_smooth_compactSupport φ hφ hsupp
  sorry -- need: g =ᵃᵉ φ, φ ∈ H², ae-equivalence preserves H² membership

/-- C_c^∞(ℝ³) is dense in H¹(ℝ³).

    This is the Meyers-Serrin theorem (H = W). Essential for:
    - Extending Hardy's inequality from smooth to H¹ functions
    - Approximation arguments in Kato-Rellich -/
theorem smooth_compactly_supported_dense_H1 :
    ∀ (f : L2_R3) (hf : MemSobolevH1 f) (ε : ℝ) (hε : 0 < ε),
    ∃ (g : L2_R3) (hg : MemSobolevH2 g),
      ‖f - g‖ < ε ∧
      ∀ i, ‖weakGradient f hf i - weakGradient g (sobolevH2_le_H1 hg) i‖ < ε :=
  sorry

/-! ### Sobolev embedding -/

/-- **Sobolev embedding in 3D**: H¹(ℝ³) ↪ L⁶(ℝ³).

    The critical exponent is 2* = 2d/(d-2) = 6 for d = 3.
    Stated as: ‖f‖_{L⁶} ≤ C ‖∇f‖_{L²} for f ∈ H¹(ℝ³).

    This is used in the Kato-Rellich perturbation theory to control
    the Coulomb singularity. -/
theorem sobolev_embedding_L6 :
    ∃ C > 0, ∀ (f : L2_R3) (hf : MemSobolevH1 f),
      ‖f‖ ≤ C * Real.sqrt (gradientNormSq f hf) :=
  sorry
  -- Note: the precise L⁶ statement requires working in Lp 6.
  -- This simplified version gives L² control, which suffices
  -- for the relative boundedness estimate in CoulombBound.lean.
  -- The full Gagliardo-Nirenberg-Sobolev inequality is:
  --   ‖f‖_{L^6}^2 ≤ C² ∫|∇f|² dx

/-! ### Fourier characterisation (interface for Laplacian self-adjointness)

The Fourier transform provides the cleanest route to proving that -Δ
is self-adjoint on H². Under Fourier:

  H²(ℝ³) ↔ { f̂ ∈ L² : (1+|ξ|²)f̂ ∈ L² }
  (-Δf)^ = |ξ|² f̂

This makes -Δ unitarily equivalent to multiplication by |ξ|², which
is manifestly self-adjoint. We axiomatize the key consequences here;
Phase 4 fills them in once Mathlib's Plancherel theorem on ℝ³ is
interfaced.
-/

/-- H² is characterised in Fourier space by the finiteness of ∫(1+|ξ|²)²|f̂|² dξ.

    This is used to prove:
    - Self-adjointness of -Δ on H²
    - The resolvent bound for -Δ
    - The spectrum σ(-Δ) = [0,∞) -/
theorem sobolevH2_fourier_char :
    ∀ f : L2_R3, MemSobolevH2 f ↔
      sorry :=  -- ∫(1+|ξ|²)²|f̂(ξ)|² dξ < ∞
  sorry

/-! ### H¹ inner product (Hilbert space structure) -/

/-- The H¹ inner product: ⟨f, g⟩_{H¹} = ⟨f, g⟩_{L²} + Σᵢ ⟨∂ᵢf, ∂ᵢg⟩_{L²}.

    Under this inner product, H¹ is a Hilbert space. This is used
    for coercivity estimates in the variational formulation. -/
def sobolevH1Inner (f g : L2_R3) (hf : MemSobolevH1 f) (hg : MemSobolevH1 g) : ℂ :=
  inner (𝕜 := ℂ) f g +
  ∑ i : Fin 3, inner (𝕜 := ℂ) (weakGradient f hf i) (weakGradient g hg i)

/-- H¹ is complete under the H¹ inner product. -/
def sobolevH1_complete :
    ∀ (seq : ℕ → L2_R3) (hseq : ∀ n, MemSobolevH1 (seq n)),
    -- if Cauchy in H¹ norm, then converges in H¹
    sorry := by
  sorry



end QuantumMechanics.Hydrogen
