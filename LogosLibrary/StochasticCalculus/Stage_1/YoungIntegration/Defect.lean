/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: YoungIntegration/Defect.lean
-/
import LogosLibrary.StochasticCalculus.Stage_1.YoungIntegration.PVarCont
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
/-!
# Young integration — the defect identity

This file contains the **algebraic core** of Young integration:

1. The approximation map `Ξ(s,t) = σ(Y_s, X_t - X_s)`.
2. The defect identity `δΞ(s,u,t) = -σ(Y_u - Y_s, X_t - X_u)`.
3. Verification of `SewingCondition₂` for Hölder paths.

The defect identity is pure algebra — expand `Ξ(s,t) - Ξ(s,u) - Ξ(u,t)` using
bilinearity of `σ`. This is the identity that *makes Young integration work*:
the defect of the left-point Riemann sum factorises into an integrand increment
on `[s, u]` and an integrator increment on `[u, t]`, which is precisely the
product structure that Layer 2 needs.

## Two levels of generality

We provide two versions:

* **Scalar version**: `X : ℝ → ℝ`, `Y : ℝ → E`, with `Ξ(s,t) = (X(t) - X(s)) • Y(s)`.
  This is the version used in `young_integral_holder` and suffices for all scalar-valued
  integrator applications.

* **Bilinear version** (TODO): `X : ℝ → F`, `Y : ℝ → G`, `σ : G →L[ℝ] F →L[ℝ] E`,
  with `Ξ(s,t) = σ (Y s) (X t - X s)`. This is needed for vector-valued rough paths.

## References

* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Chapter 1]
* [Young, L.C., *An inequality of the Hölder type*, Acta Math. **67** (1936)]
-/

noncomputable section

open Real Set Filter Finset

namespace StochCalc

/-! ### The approximation map (scalar version) -/

section ScalarApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Young approximation map** (scalar version):
`Ξ(s, t) = (X(t) - X(s)) • Y(s)`.

This is the left-point Riemann sum approximation to `∫_s^t Y dX`. -/
def youngApprox (X : ℝ → ℝ) (Y : ℝ → E) (s t : ℝ) : E :=
  (X t - X s) • Y s

/-- The Young approximation vanishes on the diagonal. -/
@[simp]
theorem youngApprox_diag (X : ℝ → ℝ) (Y : ℝ → E) (s : ℝ) :
    youngApprox X Y s s = 0 := by
  simp [youngApprox]

/-- **The defect identity** (scalar version):

  `δΞ(s, u, t) = -(Y(u) - Y(s)) • (X(t) - X(u))  [= (X(u) - X(t)) • (Y(u) - Y(s))]`

This is the algebraic heart of Young integration. Expand:
  `Ξ(s,t) - Ξ(s,u) - Ξ(u,t)`
  `= (X(t) - X(s))•Y(s) - (X(u) - X(s))•Y(s) - (X(t) - X(u))•Y(u)`
  `= (X(t) - X(u))•Y(s) - (X(t) - X(u))•Y(u)`
  `= (X(t) - X(u)) • (Y(s) - Y(u))`
  `= -(X(t) - X(u)) • (Y(u) - Y(s))`

The factorisation into an `[s,u]`-dependent term `Y(u) - Y(s)` and a
`[u,t]`-dependent term `X(t) - X(u)` is precisely the product structure
required by `SewingCondition₂`. -/
theorem youngApprox_defect (X : ℝ → ℝ) (Y : ℝ → E) (s u t : ℝ) :
    sewingDefect₁ (youngApprox X Y) s u t =
      (X u - X t) • (Y u - Y s) := by
  simp only [sewingDefect₁, youngApprox]
  -- Expand: (X t - X s)•Y s - (X u - X s)•Y s - (X t - X u)•Y u
  -- = (X t - X u)•Y s - (X t - X u)•Y u
  -- = (X t - X u)•(Y s - Y u)
  -- = -(X t - X u)•(Y u - Y s)
  -- = (X u - X t)•(Y u - Y s)
  rw [show (X t - X s) • Y s - (X u - X s) • Y s - (X t - X u) • Y u =
    (X u - X t) • (Y u - Y s) from by
    simp only [sub_smul, smul_sub]; abel]

/-- **Norm bound on the defect** (scalar version):

  `‖δΞ(s, u, t)‖ ≤ |X(u) - X(t)| · ‖Y(u) - Y(s)‖`

This is immediate from the defect identity + `‖a • v‖ = |a| · ‖v‖`. -/
theorem youngApprox_defect_norm (X : ℝ → ℝ) (Y : ℝ → E) (s u t : ℝ) :
    ‖sewingDefect₁ (youngApprox X Y) s u t‖ =
      |X u - X t| * ‖Y u - Y s‖ := by
  rw [youngApprox_defect, norm_smul, Real.norm_eq_abs]

end ScalarApprox

/-! ### Defect bound from Hölder regularity -/

section HolderDefect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Hölder defect bound**: if `X` is `γ`-Hölder with constant `C_X` and
`Y` is `δ`-Hölder with constant `C_Y`, then the Young defect satisfies

  `‖δΞ(s, u, t)‖ ≤ C_X · C_Y · |t - u|^γ · |u - s|^δ`

Note the **cross structure**: the `X`-factor depends on `[u, t]` and the
`Y`-factor depends on `[s, u]`. This is the product form for Layer 2. -/
theorem youngApprox_defect_holder_bound
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b) (hY : IsHolderOn Y δ C_Y a b)
    {s u t : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (htb : t ≤ b) :
    ‖sewingDefect₁ (youngApprox X Y) s u t‖ ≤
      C_X * C_Y * |t - u| ^ γ * |u - s| ^ δ := by
  rw [youngApprox_defect_norm]
  -- |X(u) - X(t)| ≤ C_X · |t - u|^γ  (note: |X(u) - X(t)| = |X(t) - X(u)|)
  -- ‖Y(u) - Y(s)‖ ≤ C_Y · |u - s|^δ
  -- Product gives the result.
  calc |X u - X t| * ‖Y u - Y s‖
      = ‖X t - X u‖ * ‖Y u - Y s‖ := by
        rw [abs_sub_comm, Real.norm_eq_abs]
    _ ≤ (C_X * |t - u| ^ γ) * (C_Y * |u - s| ^ δ) := by
        apply mul_le_mul
        · exact hX.holder_bound u t (has.trans hsu) hut htb
        · exact hY.holder_bound s u has hsu (hut.trans htb)
        · exact norm_nonneg _
        · exact mul_nonneg hX.C_nonneg (rpow_nonneg (abs_nonneg _) _)
    _ = C_X * C_Y * |t - u| ^ γ * |u - s| ^ δ := by ring

end HolderDefect

/-! ### Verification of SewingCondition₂ -/

section SewingCondition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Young sewing condition**: for `γ`-Hölder `X` and `δ`-Hölder `Y`
with `γ + δ > 1`, the Young approximation map satisfies `SewingCondition₂`.

The controls are `ω₁(s,u) = C_Y^{1/δ} · |u - s|` (integrand variation)
and `ω₂(u,t) = C_X^{1/γ} · |t - u|` (integrator variation), both Lipschitz
with constants `C_Y^{1/δ}` and `C_X^{1/γ}` respectively.

The exponents are `α = δ` and `β = γ`, with `α + β = δ + γ > 1`.

**Alternatively** (and more cleanly for the proof), we can use the raw
absolute-value controls `ω₁(s,u) = |u - s|` and `ω₂(u,t) = |t - u|`,
with `K = C_X · C_Y` absorbing the Hölder constants. The exponents
remain `α = δ`, `β = γ`.

We take the second approach, since `|t - s|` is already shown to be
a `LipControl` in `lipControl_abs_sub`. -/
theorem youngApprox_sewingCondition₂
    {X : ℝ → ℝ} {Y : ℝ → E} {γ δ C_X C_Y a b : ℝ}
    (hX : IsHolderOn X γ C_X a b) (hY : IsHolderOn Y δ C_Y a b)
    (hγδ : 1 < γ + δ) :
    SewingCondition₂ (youngApprox X Y)
      (fun s t => |t - s|) (fun s t => |t - s|)
      δ γ (C_X * C_Y)
      1 1 a b where
  vanish_diag := youngApprox_diag X Y
  one_lt_exp := by linarith
  α_nonneg := le_of_lt hY.γ_pos
  β_nonneg := le_of_lt hX.γ_pos
  K_nonneg := mul_nonneg hX.C_nonneg hY.C_nonneg
  hab := hX.hab
  ω₁_nonneg := fun s t _ _ _ => abs_nonneg _
  ω₁_diag := fun s => by simp
  ω₁_superadd := fun s u t _ hsu hut _ => by
    rw [show t - s = (u - s) + (t - u) from by ring]
    exact le_abs_self _ |>.trans <| by
      rw [abs_of_nonneg (sub_nonneg.mpr hsu), abs_of_nonneg (sub_nonneg.mpr hut),
          abs_of_nonneg (by linarith)]
  ω₁_lip := fun s t _ hst _ => by
    simp [abs_of_nonneg (sub_nonneg.mpr hst)]
  defect_bound := fun s u t has hsu hut htb => by
    -- ‖δΞ(s,u,t)‖ ≤ C_X · C_Y · |t-u|^γ · |u-s|^δ
    -- = (C_X · C_Y) · |u-s|^δ · |t-u|^γ
    -- The sewing condition wants: K · ω₁(s,u)^α · ω₂(u,t)^β
    -- = (C_X · C_Y) · |u-s|^δ · |t-u|^γ  ✓
    calc ‖sewingDefect₁ (youngApprox X Y) s u t‖
        ≤ C_X * C_Y * |t - u| ^ γ * |u - s| ^ δ :=
          youngApprox_defect_holder_bound hX hY has hsu hut htb
      _ = C_X * C_Y * |u - s| ^ δ * |t - u| ^ γ := by ring
  L₁_nonneg := zero_le_one' ℝ
  L₂_nonneg := zero_le_one' ℝ
  ω₂_nonneg := fun s t _ _ _ => abs_nonneg _
  ω₂_diag := fun s => by simp
  ω₂_superadd := fun s u t _ hsu hut _ => by
    rw [show t - s = (u - s) + (t - u) from by ring]
    exact le_abs_self _ |>.trans <| by
      rw [abs_of_nonneg (sub_nonneg.mpr hsu), abs_of_nonneg (sub_nonneg.mpr hut),
          abs_of_nonneg (by linarith)]
  ω₂_lip := fun s t _ hst _ => by
    simp [abs_of_nonneg (sub_nonneg.mpr hst)]

end SewingCondition

/-! ### Bilinear version (sketch) -/

section BilinearApprox

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **Young approximation map** (bilinear version):
`Ξ(s, t) = σ(Y_s, X_t - X_s)`. -/
def youngApproxBilin (σ : G →L[ℝ] F →L[ℝ] E) (X : ℝ → F) (Y : ℝ → G)
    (s t : ℝ) : E :=
  σ (Y s) (X t - X s)

/-- The bilinear Young approximation vanishes on the diagonal. -/
@[simp]
theorem youngApproxBilin_diag (σ : G →L[ℝ] F →L[ℝ] E) (X : ℝ → F) (Y : ℝ → G)
    (s : ℝ) : youngApproxBilin σ X Y s s = 0 := by
  simp [youngApproxBilin]

/-- **The defect identity** (bilinear version):
`δΞ(s, u, t) = σ(Y_s - Y_u, X_t - X_u)`.

Bilinearity of `σ` does all the work:
  `σ(Y_s)(X_t - X_s) - σ(Y_s)(X_u - X_s) - σ(Y_u)(X_t - X_u)`
  `= σ(Y_s)(X_t - X_u) - σ(Y_u)(X_t - X_u)`
  `= (σ(Y_s) - σ(Y_u))(X_t - X_u)`
  `= σ(Y_s - Y_u)(X_t - X_u)` -/
theorem youngApproxBilin_defect (σ : G →L[ℝ] F →L[ℝ] E) (X : ℝ → F) (Y : ℝ → G)
    (s u t : ℝ) :
    sewingDefect₁ (youngApproxBilin σ X Y) s u t =
      σ (Y s - Y u) (X t - X u) := by
  simp only [sewingDefect₁, youngApproxBilin, map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- **Norm bound on the defect** (bilinear version):
`‖δΞ(s, u, t)‖ ≤ ‖σ‖ · ‖Y_u - Y_s‖ · ‖X_t - X_u‖`.

Unlike the scalar version (which is an equality), this is an inequality
because `‖σ(g)(f)‖ ≤ ‖σ‖ · ‖g‖ · ‖f‖` uses the operator norm twice. -/
theorem youngApproxBilin_defect_norm_le (σ : G →L[ℝ] F →L[ℝ] E) (X : ℝ → F)
    (Y : ℝ → G) (s u t : ℝ) :
    ‖sewingDefect₁ (youngApproxBilin σ X Y) s u t‖ ≤
      ‖σ‖ * ‖Y u - Y s‖ * ‖X t - X u‖ := by
  rw [youngApproxBilin_defect]
  calc ‖σ (Y s - Y u) (X t - X u)‖
      ≤ ‖σ (Y s - Y u)‖ * ‖X t - X u‖ :=
        (σ (Y s - Y u)).le_opNorm _
    _ ≤ ‖σ‖ * ‖Y s - Y u‖ * ‖X t - X u‖ :=
        mul_le_mul_of_nonneg_right (σ.le_opNorm _) (norm_nonneg _)
    _ = ‖σ‖ * ‖Y u - Y s‖ * ‖X t - X u‖ := by
        rw [norm_sub_rev]

end BilinearApprox

end StochCalc
