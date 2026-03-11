/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ResolventRoute/ResolventKernel.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Bochner
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent
import LogosLibrary.QuantumMechanics.SpectralTheory.BochnerRoute

/-!
# Resolvent Kernel Analysis

This file develops the analytical properties of the resolvent kernel `(s - z)⁻¹`
and the associated Lorentzian approximation to the delta function.

## Main definitions

* `offRealPoint`: Helper to construct `t + iε` as an `OffRealAxis` point
* `offRealPointNeg`: Helper to construct `t - iε` as an `OffRealAxis` point
* `resolvent_integrand`: The kernel `(s - z)⁻¹`

## Main statements

### Resolvent kernel
* `resolvent_integrand_bound`: `|(s - z)⁻¹| ≤ 1/|Im(z)|` for all `s ∈ ℝ`
* `resolvent_kernel_im`: `Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)`
* `resolvent_kernel_diff`: `(s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε/((s-t)² + ε²)`

### Lorentzian kernel
* `lorentzian_nonneg`: The Lorentzian is non-negative
* `lorentzian_bound`: The Lorentzian is bounded by `1/ε`
* `lorentzian_total_integral`: `∫ ε/((s-t)² + ε²) ds = π` (axiom)
* `lorentzian_concentration`: Lorentzian concentrates at `t` as `ε → 0` (axiom)
* `lorentzian_approx_delta`: `(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0`

### Arctan integration
* `lorentzian_arctan_integral`: `∫_a^b ε/((s-t)² + ε²) dt = arctan(...) - arctan(...)`
* `arctan_indicator_limit`: The arctan kernel converges to the indicator function
* `arctan_kernel_bound`: The arctan kernel is uniformly bounded by 1

## Physical interpretation

The Lorentzian kernel `ε/((s-t)² + ε²)` is the imaginary part of the resolvent
kernel at `z = t + iε`. As `ε → 0`, it becomes an approximation to the delta
function `δ(s-t)`, which is the key to extracting spectral information from
the resolvent.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* Stone, "Linear Transformations in Hilbert Space" (1932)

## Tags

resolvent, Lorentzian, approximate identity, Poisson kernel
-/

namespace SpectralBridge.Resolvent

open Complex MeasureTheory Filter Topology

/-! ### Off-real axis points -/

/-- A complex number with non-zero imaginary part. -/
structure OffRealAxis where
  val : ℂ
  im_ne_zero : val.im ≠ 0

/-- Construct `t + iε` as an off-real point. -/
def offRealPoint (t : ℝ) (ε : ℝ) (hε : ε > 0) : QuantumMechanics.Resolvent.OffRealAxis :=
  ⟨↑t + ↑ε * I, by simp [Complex.add_im]; exact ne_of_gt hε⟩

/-- Construct `t - iε` as an off-real point. -/
def offRealPointNeg (t : ℝ) (ε : ℝ) (hε : ε > 0) : QuantumMechanics.Resolvent.OffRealAxis :=
  ⟨↑t - ↑ε * I, by simp [Complex.sub_im]; exact ne_of_gt hε⟩

/-! ### Resolvent kernel -/

/-- The resolvent integrand `(s - z)⁻¹`. -/
noncomputable def resolvent_integrand (z : ℂ) : ℝ → ℂ :=
  fun s => ((s : ℂ) - z)⁻¹

/-- The resolvent integrand is bounded by `1/|Im(z)|`.

This is the key estimate: for `z` off the real axis, the kernel `(s - z)⁻¹`
is uniformly bounded in `s ∈ ℝ`, with bound depending only on `|Im(z)|`. -/
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    ‖((s : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have h_im : ((s : ℂ) - z).im = -z.im := by simp
  have h_norm_ge : ‖(s : ℂ) - z‖ ≥ |z.im| := by
    calc ‖(s : ℂ) - z‖
        ≥ |((s : ℂ) - z).im| := Complex.abs_im_le_norm _
      _ = |-z.im| := by rw [h_im]
      _ = |z.im| := abs_neg _
  have h_pos : |z.im| > 0 := abs_pos.mpr hz
  calc ‖((s : ℂ) - z)⁻¹‖
      = 1 / ‖(s : ℂ) - z‖ := by rw [norm_inv]; simp only [one_div]
    _ ≤ 1 / |z.im| := by
        apply div_le_div_of_nonneg_left (by norm_num) h_pos h_norm_ge

/-! ### Lorentzian kernel -/

/-- Imaginary part of resolvent kernel: `Im((s - z)⁻¹) = ε/((s-t)² + ε²)` for `z = t + iε`.

This shows that the imaginary part of the resolvent kernel is exactly the
Lorentzian (Cauchy/Poisson) kernel, which is an approximation to the delta function. -/
lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) :
    (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2) := by
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'

  have h_diff : (s : ℂ) - (↑t + ↑ε * I) = (s - t : ℝ) - ε * I := by
    simp only [Complex.ofReal_sub]
    ring

  rw [h_diff]
  -- ((s-t) - εi)⁻¹ = ((s-t) + εi) / ((s-t)² + ε²)
  have h_conj : ((s - t : ℝ) - ε * I)⁻¹ =
      ((s - t : ℝ) + ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
    have h_mul : ((s - t : ℝ) - ε * I) * ((s - t : ℝ) + ε * I) =
        ((s - t)^2 + ε^2 : ℂ) := by
      push_cast
      have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
      linear_combination (norm := ring) -ε^2 * hI2
    have h_conj_ne : (↑(s - t) : ℂ) + ↑ε * I ≠ 0 := by
      intro h
      have : ε = 0 := by simpa using congrArg Complex.im h
      linarith
    rw [← h_mul]
    field_simp [h_conj_ne]

  rw [h_conj]
  have h_real : ((s - t)^2 + ε^2 : ℂ) = ((s - t)^2 + ε^2 : ℝ) := by push_cast; ring
  rw [h_real, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]

/-- The Lorentzian kernel is non-negative. -/
lemma lorentzian_nonneg (s t ε : ℝ) (hε : ε > 0) :
    0 ≤ ε / ((s - t)^2 + ε^2) := by
  apply div_nonneg (le_of_lt hε)
  positivity

/-- The Lorentzian kernel is bounded by `1/ε`. -/
lemma lorentzian_bound (s t ε : ℝ) (hε : ε > 0) :
    ε / ((s - t)^2 + ε^2) ≤ 1 / ε := by
  have h_denom : ε^2 ≤ (s - t)^2 + ε^2 := by linarith [sq_nonneg (s - t)]
  have h1 : ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 :=
    div_le_div_of_nonneg_left (le_of_lt hε) (sq_pos_of_pos hε) h_denom
  simp only [one_div]
  calc ε / ((s - t)^2 + ε^2) ≤ ε / ε^2 := h1
    _ = ε⁻¹ := by field_simp

/-- The Lorentzian integrates to π over ℝ.

This is equivalent to the residue theorem for `∫ 1/(x² + 1) dx = π`. -/
axiom lorentzian_total_integral (t ε : ℝ) (hε : ε > 0) :
    ∫ s, ε / ((s - t)^2 + ε^2) = Real.pi

/-- The Lorentzian concentrates near `t` as `ε → 0`.

For any `δ > 0`, the integral outside `(t-δ, t+δ)` vanishes as `ε → 0+`. -/
axiom lorentzian_concentration (t δ : ℝ) (hδ : δ > 0) :
    Tendsto (fun ε : ℝ => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
      ε / ((s - t)^2 + ε^2)) (𝓝[>] 0) (𝓝 0)

/-! ### Approximation to identity -/

/-- General approximation to identity theorem.

If `K(ε, s)` is a family of kernels that are non-negative, integrate to 1,
and concentrate at `t` as `ε → 0`, then `∫ K(ε, s) f(s) ds → f(t)`. -/
axiom approx_identity_continuous (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : Integrable f) (t : ℝ)
    (K : ℝ → ℝ → ℝ)  -- kernel K(ε, s)
    (hK_nonneg : ∀ ε > 0, ∀ s, K ε s ≥ 0)
    (hK_total : ∀ ε > 0, ∫ s, K ε s = 1)
    (hK_conc : ∀ δ > 0, Tendsto (fun ε => ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ), K ε s)
                                 (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t))

/-- The Lorentzian is an approximation to the delta function.

`(1/π) · ε/((s-t)² + ε²) → δ(s-t)` as `ε → 0+` in the sense that
`(1/π) ∫ ε/((s-t)² + ε²) f(s) ds → f(t)` for continuous integrable `f`. -/
lemma lorentzian_approx_delta (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_int : Integrable f) (t : ℝ) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s)
            (𝓝[>] 0) (𝓝 (f t)) := by
  -- Define the normalized kernel K(ε, s) = (1/π) * ε/((s-t)² + ε²)
  let K : ℝ → ℝ → ℝ := fun ε s => (1 / Real.pi) * (ε / ((s - t)^2 + ε^2))

  -- Rewrite goal in terms of K
  have h_rewrite : ∀ ε > 0, (1 / Real.pi) • ∫ s, (ε / ((s - t)^2 + ε^2)) • f s =
      ∫ s, (K ε s) • f s := by
    intro ε hε
    simp only [K]
    -- Rewrite integrand: (a * b) • x = a • (b • x)
    have key : (fun s => (1 / Real.pi * (ε / ((s - t) ^ 2 + ε ^ 2))) • f s) =
               (fun s => (1 / Real.pi) • (ε / ((s - t) ^ 2 + ε ^ 2)) • f s) := by
      ext s; exact (smul_smul _ _ _).symm
    rw [key]
    exact Eq.symm (integral_smul (1 / Real.pi) fun a => (ε / ((a - t) ^ 2 + ε ^ 2)) • f a)

  -- Apply the general approximation to identity theorem
  have h_tendsto : Tendsto (fun ε => ∫ s, (K ε s) • f s) (𝓝[>] 0) (𝓝 (f t)) := by
    apply approx_identity_continuous f hf_cont hf_int t K
    -- K is nonnegative
    · intro ε hε s
      simp only [K]
      apply mul_nonneg
      · simp only [one_div, inv_nonneg] ; exact Real.pi_nonneg
      · exact lorentzian_nonneg s t ε hε
    -- K integrates to 1
    · intro ε hε
      simp only [K]
      have key : (fun s => 1 / Real.pi * (ε / ((s - t) ^ 2 + ε ^ 2))) =
                 fun s => (1 / Real.pi) * (ε / ((s - t) ^ 2 + ε ^ 2)) := rfl
      rw [show ∫ s, (1 / Real.pi * (ε / ((s - t) ^ 2 + ε ^ 2))) =
           (1 / Real.pi) * ∫ s, (ε / ((s - t) ^ 2 + ε ^ 2)) from
           MeasureTheory.integral_const_mul _ _,
        lorentzian_total_integral t ε hε]
      field_simp
    -- K concentrates at t
    · intro δ hδ
      simp only [K]
      have h := lorentzian_concentration t δ hδ
      have h_eq : ∀ ε, ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          (1 / Real.pi) * (ε / ((s - t)^2 + ε^2)) =
          (1 / Real.pi) * ∫ s in Set.Iic (t - δ) ∪ Set.Ici (t + δ),
          ε / ((s - t)^2 + ε^2) := fun ε => by
        exact integral_const_mul (1 / Real.pi) fun a => ε / ((a - t) ^ 2 + ε ^ 2)
      simp_rw [h_eq]
      convert h.const_mul (1 / Real.pi) using 2
      exact Eq.symm (CommMonoidWithZero.mul_zero (1 / Real.pi))

  -- Connect back to original formulation
  refine Tendsto.congr' ?_ h_tendsto
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (h_rewrite ε hε).symm

/-! ### Resolvent kernel difference -/

/-- Key identity: difference of resolvent kernels at conjugate points.

`(s - (t + iε))⁻¹ - (s - (t - iε))⁻¹ = 2iε / ((s-t)² + ε²)`

This shows the resolvent difference is purely imaginary and proportional to the Lorentzian.
This identity is the basis for Stone's formula. -/
lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) :
    ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ =
    (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) := by

  have h_z_plus : (↑t + ↑ε * I : ℂ) - (↑t - ↑ε * I) = 2 * ε * I := by ring
  have h_denom : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) =
      ((s - t)^2 + ε^2 : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    linear_combination (norm := ring) -ε^2 * hI2
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_prod_ne : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) ≠ 0 := by
    rw [h_denom]
    push_cast at h_denom_ne ⊢
    exact h_denom_ne
  have h_left_ne : (s : ℂ) - (↑t + ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, zero_mul]
  have h_right_ne : (s : ℂ) - (↑t - ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, mul_zero]
  -- Main calculation
  have h_denom_ne' : (↑s - ↑t : ℂ) ^ 2 + ↑ε ^ 2 ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  field_simp [h_left_ne, h_right_ne, h_denom_ne']
  push_cast [sq]
  ring_nf
  simp only [I_pow_three, mul_neg, neg_mul, sub_neg_eq_add]
  ring_nf; rfl

/-! ### Arctan integration -/

/-- Arctan antiderivative for the Lorentzian kernel.

`∫_a^b ε/((s-t)² + ε²) dt = arctan((b-s)/ε) - arctan((a-s)/ε)`

This is obtained by the substitution `u = (t-s)/ε`. -/
axiom lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in Set.Icc a b, ε / ((s - t)^2 + ε^2) =
      Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)

/-- The arctan kernel converges to the indicator function.

`(1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s)` as `ε → 0+`

This is because `arctan(x) → π/2` as `x → +∞` and `arctan(x) → -π/2` as `x → -∞`. -/
axiom arctan_indicator_limit (a b s : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0)
      (𝓝 (Set.indicator (Set.Ioc a b) 1 s))

/-- The arctan kernel is uniformly bounded by 1.

Since `|arctan(x)| ≤ π/2` for all `x`, the difference is at most `π`. -/
axiom arctan_kernel_bound (a b s ε : ℝ) (hε : ε > 0) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1

end SpectralBridge.Resolvent
