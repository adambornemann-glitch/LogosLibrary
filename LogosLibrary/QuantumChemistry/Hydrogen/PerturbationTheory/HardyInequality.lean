/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumChemistry.Hydrogen.Foundations.SobolevSpaces
import LogosLibrary.QuantumChemistry.Hydrogen.Foundations.Laplacian

/-!
# The Hardy Inequality in Three Dimensions

The three-dimensional Hardy inequality:

  ∫_{ℝ³} |ψ(x)|²/|x|² dx ≤ 4 ∫_{ℝ³} |∇ψ(x)|² dx

for ψ ∈ H¹(ℝ³). The constant 4 = (d−2)⁻² · 4 for d = 3 is sharp.

## Role in the hydrogen atom

This inequality is the *analytic engine* of the Kato-Rellich argument.
It says that the Coulomb potential 1/|x| is controlled by the kinetic
energy −Δ in the sense of quadratic forms. Concretely, it gives:

  ‖(1/r)ψ‖² ≤ 4 ⟨−Δψ, ψ⟩

which, after applying Cauchy's inequality with ε, yields:

  ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖    for any ε > 0

This is the *relative boundedness with bound zero* of 1/r with respect
to −Δ, which is the hypothesis of Kato-Rellich.

## Proof strategy

**Step 1 (Smooth functions):** Prove Hardy for ψ ∈ C_c^∞(ℝ³).
The proof uses integration by parts in spherical coordinates:

  ∫ |ψ|²/r² dx = −2 Re ∫ (ψ̄/r)(r̂ · ∇ψ) dx
                ≤ 2 (∫ |ψ|²/r²)^{1/2} (∫ |∇ψ|²)^{1/2}

Dividing both sides by (∫ |ψ|²/r²)^{1/2} gives the result.

The integration by parts identity comes from:
  div(r̂/r) = (d−2)/r²    in d dimensions (= 1/r² for d = 3)

and the divergence theorem on ℝ³ \ B(0,ε), then ε → 0.

**Step 2 (Density extension):** Extend from C_c^∞ to H¹ via
`smooth_compactly_supported_dense_H1` from SobolevSpaces.lean.
The ∫|ψ|²/|x|² functional is lower semicontinuous with respect to
H¹ convergence, so the bound passes to the closure.

## Main statements

* `hardy_inequality_smooth` — Hardy for smooth compactly supported functions.
* `hardy_inequality` — Hardy for all ψ ∈ H¹(ℝ³).
* `hardy_constant_sharp` — The constant 4 is optimal.
* `inverse_r_sq_integrable` — ∫|ψ|²/|x|² < ∞ for ψ ∈ H¹.

## Sorry strategy

**Every sorry is dischargeable.**
- `hardy_inequality_smooth`: IBP in spherical coordinates + Cauchy-Schwarz.
- `hardy_inequality`: density of C_c^∞ in H¹ + lower semicontinuity.
- `hardy_constant_sharp`: explicit optimising sequence ψ_n(r) = r^{−1/2+ε} χ(r).
- Inverse-r estimates: from Hardy + Cauchy inequality with ε.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Lieb, Loss, *Analysis*][lieb2001], Theorem 7.17.
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], §V.5.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal

/-! ## The inverse-square weight

We need the function x ↦ 1/|x|² as a measurable function on ℝ³,
and its interaction with L² functions.
-/

/-- The Euclidean norm on ℝ³. -/
def euclideanNorm (x : R3) : ℝ := ‖x‖

/-- The inverse-square weight: x ↦ 1/|x|². -/
def inverseRSq (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else 1 / ‖x‖ ^ 2

/-- The inverse weight: x ↦ 1/|x|. -/
def inverseR (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else 1 / ‖x‖

/-- inverseRSq is measurable. -/
lemma inverseRSq_measurable : Measurable inverseRSq := by
  unfold inverseRSq
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div (measurable_norm.pow_const 2))

/-- inverseR is measurable. -/
lemma inverseR_measurable : Measurable inverseR := by
  unfold inverseR
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div measurable_norm)

/-- inverseRSq is non-negative. -/
lemma inverseRSq_nonneg (x : R3) : 0 ≤ inverseRSq x := by
  simp only [inverseRSq]
  split_ifs <;> positivity

/-- inverseR is non-negative. -/
lemma inverseR_nonneg (x : R3) : 0 ≤ inverseR x := by
  simp only [inverseR]
  split_ifs <;> positivity

/-- 1/|x| is locally L² on ℝ³ (integrable on any ball).

    **Discharge route:** In spherical coordinates,
    ∫_{B(0,R)} 1/|x|² dx = ∫_0^R ∫_{S²} (1/r²) r² dr dΩ
                           = 4π ∫_0^R dr = 4πR < ∞.
    The key is that the r² from the volume element cancels the 1/r². -/
def inverseR_memLpLoc :
    sorry :=  -- 1/|x| ∈ L²_loc(ℝ³)
  sorry

/-! ## The Hardy integral

The weighted L² norm ∫|ψ|²/|x|² that Hardy's inequality controls.
-/

/-- The Hardy integral: ∫ |ψ(x)|²/|x|² dx.

    Defined as the Lebesgue integral ∫ inverseRSq(x) · |ψ(x)|² dx.
    May be infinite if ψ is not in the Hardy domain. -/
def hardyIntegral (ψ : L2_R3) : ℝ :=
  ∫ x, inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2

/-- The Hardy integral is non-negative. -/
lemma hardyIntegral_nonneg (ψ : L2_R3) : 0 ≤ hardyIntegral ψ := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (inverseRSq_nonneg x) (sq_nonneg _)

/-! ## Hardy's inequality: smooth case

The core estimate, proved for C_c^∞ functions where integration by parts
is classical.
-/

/-- **Hardy's inequality for smooth functions.**

    For ψ ∈ C_c^∞(ℝ³):
      ∫ |ψ(x)|²/|x|² dx ≤ 4 ∫ |∇ψ(x)|² dx

    **Discharge route (~150 lines):**

    1. **Divergence identity.** For d = 3:
         div(x̂/|x|) = (d−2)/|x|² = 1/|x|²
       More precisely, div(x/|x|²) = (d−2)/|x|² in the distributional sense.

    2. **Integration by parts.** For ψ ∈ C_c^∞, integrate on ℝ³ \ B(0,ε):
         ∫_{|x|>ε} |ψ|²/|x|² dx = ∫_{|x|>ε} |ψ|² div(x̂/|x|) dx
           = −∫_{|x|>ε} ∇(|ψ|²) · (x̂/|x|) dx + boundary term
           = −2 Re ∫_{|x|>ε} (ψ̄/|x|)(x̂ · ∇ψ) dx + boundary term

    3. **Boundary vanishes.** The boundary integral over ∂B(0,ε) is
       bounded by C·ε → 0 as ε → 0 (since ψ is smooth, hence bounded
       near the origin).

    4. **Cauchy-Schwarz.** Apply |⟨f, g⟩| ≤ ‖f‖ · ‖g‖ with
       f(x) = ψ̄(x)/|x| and g(x) = x̂ · ∇ψ(x):
         |2 Re ∫ (ψ̄/|x|)(x̂ · ∇ψ) dx| ≤ 2 (∫ |ψ|²/|x|²)^{1/2} (∫ |∇ψ|²)^{1/2}

    5. **Absorb.** Set A = (∫|ψ|²/|x|²)^{1/2}. From steps 2-4:
         A² ≤ 2A · (∫|∇ψ|²)^{1/2}
       Divide by A (if A = 0, the result is trivial):
         A ≤ 2 (∫|∇ψ|²)^{1/2}
       Square: ∫|ψ|²/|x|² ≤ 4 ∫|∇ψ|². -/
theorem hardy_inequality_smooth
    (ψ : R3 → ℂ) (hψ : ContDiff ℝ ⊤ ψ) (hsupp : HasCompactSupport ψ) :
    ∫ x, inverseRSq x * ‖ψ x‖ ^ 2 ≤
    4 * ∫ x, ∑ i : Fin 3, ‖fderiv ℝ ψ x (EuclideanSpace.single i 1)‖ ^ 2 :=
  sorry

/-! ## Hardy's inequality: H¹ extension

Extension from C_c^∞ to H¹ via density.
-/

/-- **Hardy's inequality for H¹ functions.**

    For ψ ∈ H¹(ℝ³):
      ∫ |ψ(x)|²/|x|² dx ≤ 4 ∫ |∇ψ(x)|² dx = 4 · gradientNormSq ψ

    **Discharge route (~80 lines):**

    1. Approximate ψ by ψ_n ∈ C_c^∞ in H¹ norm
       (from `smooth_compactly_supported_dense_H1`).

    2. Hardy for ψ_n: ∫|ψ_n|²/|x|² ≤ 4 ∫|∇ψ_n|² for each n.

    3. **Lower semicontinuity:** Fatou's lemma gives
         ∫|ψ|²/|x|² ≤ liminf_n ∫|ψ_n|²/|x|²

       (since |ψ_n(x)|² → |ψ(x)|² a.e. along a subsequence,
       by the L² convergence ψ_n → ψ, and inverseRSq ≥ 0).

    4. **Gradient convergence:** ∫|∇ψ_n|² → ∫|∇ψ|² = gradientNormSq ψ
       by the H¹ approximation.

    5. Combine: ∫|ψ|²/|x|² ≤ liminf 4∫|∇ψ_n|² = 4 · gradientNormSq ψ. -/
theorem hardy_inequality
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    hardyIntegral ψ ≤ 4 * gradientNormSq ψ hψ :=
  sorry

/-- The Hardy integral is finite for H¹ functions. -/
lemma hardyIntegral_finite
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    ∃ M : ℝ, hardyIntegral ψ ≤ M :=
  ⟨4 * gradientNormSq ψ hψ, hardy_inequality ψ hψ⟩

/-- ∫|ψ|²/|x|² is integrable for ψ ∈ H¹. -/
lemma inverseRSq_mul_sq_integrable
    (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    Integrable (fun x => inverseRSq x * ‖(ψ : R3 → ℂ) x‖ ^ 2) volume :=
  sorry  -- from hardy_inequality: integral is bounded, integrand is nonneg + measurable

/-! ## Sharpness of the constant -/

/-- **The constant 4 is sharp.**

    There is no C < 4 such that ∫|ψ|²/|x|² ≤ C ∫|∇ψ|² for all ψ ∈ H¹.

    **Discharge route:**
    The optimising sequence is ψ_n(x) = |x|^{−1/2 + 1/n} · χ(|x|)
    where χ is a smooth cutoff. As n → ∞:
      ∫|ψ_n|²/|x|² / ∫|∇ψ_n|² → 4 = (d−2)⁻² · 4 for d = 3.

    The optimizer is |x|^{−1/2} which is in H¹_loc but not H¹,
    hence the infimum is not attained. -/
theorem hardy_constant_sharp :
    ∀ C : ℝ, (∀ (ψ : L2_R3) (hψ : MemSobolevH1 ψ),
      hardyIntegral ψ ≤ C * gradientNormSq ψ hψ) → 4 ≤ C :=
  sorry

/-! ## Operator estimates for 1/r

These are the estimates consumed by `CoulombBound.lean` to establish
relative boundedness of the Coulomb potential.
-/

/-- **‖(1/r)ψ‖² ≤ 4⟨−Δψ, ψ⟩ for ψ ∈ H².**

    This is Hardy rephrased via integration by parts:
    ∫|∇ψ|² = ⟨−Δψ, ψ⟩ for ψ ∈ H² (from `gradient_norm_sq_eq_laplacian_inner`).

    This is the *quadratic form* version of relative boundedness. -/
theorem hardy_quadratic_form
    (ψ : L2_R3) (hψ : MemSobolevH2 ψ) :
    hardyIntegral ψ ≤
    4 * (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re := by
  calc hardyIntegral ψ
      ≤ 4 * gradientNormSq ψ (sobolevH2_le_H1 hψ) :=
        hardy_inequality ψ (sobolevH2_le_H1 hψ)
    _ = 4 * (inner (𝕜 := ℂ) (weakLaplacian ψ hψ) ψ).re := by
        congr 1
        have h := gradient_norm_sq_eq_laplacian_inner ψ hψ
        -- gradientNormSq is real, inner product re part equals it
        sorry  -- extract .re from the Complex equality

/-- **Cauchy inequality with ε**: ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖.

    For any ε > 0, there exists C_ε such that:
      ‖(1/r)ψ‖ ≤ ε ‖−Δψ‖ + C_ε ‖ψ‖

    **Discharge route:**
    From `hardy_quadratic_form`:
      ‖(1/r)ψ‖² ≤ 4 ⟨−Δψ, ψ⟩
                  ≤ 4 ‖−Δψ‖ · ‖ψ‖     (Cauchy-Schwarz)
    Then Young's inequality ab ≤ (ε/2)a² + (1/(2ε))b²:
      ‖(1/r)ψ‖² ≤ 4((ε²/2)‖−Δψ‖² + (1/(2ε²))‖ψ‖²)
                  = 2ε² ‖−Δψ‖² + (2/ε²) ‖ψ‖²
    Taking square roots (and relabelling ε):
      ‖(1/r)ψ‖ ≤ ε ‖−Δψ‖ + C_ε ‖ψ‖

    This is the *operator* version of relative boundedness with bound 0. -/
theorem hardy_operator_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      Real.sqrt (hardyIntegral ψ) ≤
      ε * ‖weakLaplacian ψ hψ‖ + C * ‖ψ‖ :=
  sorry

/-- **Relative bound is zero**: 1/r is (−Δ)-bounded with relative bound 0.

    This means: for any a > 0, there exists b such that
      ‖(1/r)ψ‖ ≤ a ‖−Δψ‖ + b ‖ψ‖

    Equivalently: the infimum of valid a-constants is 0.

    This is the precise hypothesis needed for Kato-Rellich to conclude
    that −Δ − Z/r is self-adjoint on H²(ℝ³) for *any* Z > 0. -/
theorem coulomb_relative_bound_zero :
    ∀ a : ℝ, 0 < a →
    ∃ b : ℝ, 0 ≤ b ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      Real.sqrt (hardyIntegral ψ) ≤
      a * ‖weakLaplacian ψ hψ‖ + b * ‖ψ‖ :=
  fun a ha => hardy_operator_bound a ha


/-! ## Interface summary

### Exports for `CoulombBound.lean`:
- `hardy_inequality` — the core estimate
- `hardy_operator_bound` — the ε-form for Kato-Rellich
- `coulomb_relative_bound_zero` — relative bound is 0
- `inverseRSq_mul_sq_integrable` — integrability of the weighted norm

### Exports for `KatoRellich.lean` (via CoulombBound):
- The relative boundedness of V = −Z/r with respect to A = −Δ
  with any a > 0, which is the hypothesis of the abstract theorem.
-/

end QuantumMechanics.Hydrogen
