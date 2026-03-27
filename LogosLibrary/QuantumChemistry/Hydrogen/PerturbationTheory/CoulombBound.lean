/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumChemistry.Hydrogen.Foundations.SobolevSpaces
import LogosLibrary.QuantumChemistry.Hydrogen.Foundations.Laplacian
import LogosLibrary.QuantumChemistry.Hydrogen.PerturbationTheory.HardyInequality
import LogosLibrary.QuantumChemistry.Hydrogen.PerturbationTheory.KatoRellich

/-!
# The Coulomb Potential: Relative Boundedness

This file constructs the Coulomb potential V = −Z/r as a linear map
on H²(ℝ³) and verifies the Kato-Rellich hypotheses:
1. V is symmetric on H².
2. V is (−Δ)-bounded with relative bound 0.

Combined with the abstract Kato-Rellich theorem, this immediately
gives self-adjointness of H = −Δ − Z/r on H²(ℝ³) for any Z > 0.

## Architecture

```
  HardyInequality.lean           KatoRellich.lean
  ┌───────────────────┐          ┌────────────────────┐
  │ hardy_operator_   │          │ IsRelativelyBounded│
  │   bound           │──(a)────→│ IsSymmetricOn      │
  │ coulomb_relative_ │          │ kato_rellich       │
  │   bound_zero      │          └────────┬───────────┘
  └───────────────────┘                   │
            ↓                             │
  ┌───────────────────┐                   │
  │ THIS FILE         │                   │
  │ coulombPotential  │───(b)─────────────┘
  │ coulomb_symmetric │
  │ coulomb_relatively│
  │   _bounded        │
  └────────┬──────────┘
           │
  ┌────────▼──────────┐
  │ HydrogenHamilton  │
  │   .lean           │
  │ hydrogenGenerator │
  └───────────────────┘
```

(a) Hardy gives the analytic estimate ‖(1/r)ψ‖ ≤ ε‖Δψ‖ + C_ε‖ψ‖.
(b) This file packages it as `IsRelativelyBounded` + `IsSymmetricOn`.

## Main definitions

* `coulombMultiplier` — the function x ↦ −Z/|x| as a measurable function.
* `coulombPotential` — V = −Z/r as a linear map SobolevH2 →ₗ[ℂ] L2_R3.
* `coulombPotentialOnDomain` — V transported to laplacianGenerator.domain.

## Main statements

* `coulomb_in_L2` — (1/r)ψ ∈ L² for ψ ∈ H¹ (from Hardy).
* `coulomb_symmetric` — ⟨Vψ, φ⟩ = ⟨ψ, Vφ⟩ for ψ, φ ∈ H².
* `coulomb_relatively_bounded` — V is (−Δ)-bounded with bound 0.
* `coulomb_kato_rellich_hypotheses` — all hypotheses of Kato-Rellich verified.

## Sorry strategy

**Every sorry is dischargeable.**
- `coulomb_in_L2`: from `inverseRSq_mul_sq_integrable` (Hardy).
- `coulombPotential` construction: pointwise multiplication + L² membership.
- `coulomb_symmetric`: real-valuedness of 1/r.
- `coulomb_relatively_bounded`: from `hardy_operator_bound`.
- Domain transport: from `laplacianGenerator_domain`.

## References

* [Kato, *Perturbation Theory*][kato1995], §V.5, Example 5.2.
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Example 2, p.167.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen

open MeasureTheory Complex Filter Generators Perturbation InnerProductSpace
open scoped Topology NNReal ENNReal

/-! ## The Coulomb multiplier function -/

/-- The nuclear charge (positive real parameter). -/
structure CoulombParams where
  Z : ℝ
  hZ : 0 < Z

/-- The Coulomb multiplier function: x ↦ −Z/|x|.

    Defined as 0 at the origin (measure-zero, irrelevant for L²).
    This is a real-valued function, which is key for symmetry. -/
def coulombMultiplier (p : CoulombParams) (x : R3) : ℝ :=
  if ‖x‖ = 0 then 0 else -p.Z / ‖x‖

/-- The Coulomb multiplier is measurable. -/
lemma coulombMultiplier_measurable (p : CoulombParams) :
    Measurable (coulombMultiplier p) := by
  unfold coulombMultiplier
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    measurable_const (measurable_const.div measurable_norm)

/-- The Coulomb multiplier is real-valued (trivially, since codomain is ℝ). -/
lemma coulombMultiplier_real (p : CoulombParams) (x : R3) :
    (coulombMultiplier p x : ℂ) = starRingEnd ℂ (coulombMultiplier p x : ℂ) := by
  rw [Complex.conj_ofReal]

/-- Pointwise bound: |coulombMultiplier(x)| = Z/|x| = Z · inverseR(x). -/
lemma coulombMultiplier_abs (p : CoulombParams) (x : R3) :
    |coulombMultiplier p x| = p.Z * inverseR x := by
  simp only [coulombMultiplier, inverseR]
  split_ifs with h
  · simp
  · rw [abs_div, abs_neg, abs_of_pos p.hZ]
    simp only [abs_norm, one_div]
    ring

/-- Pointwise squared bound: |coulombMultiplier(x)|² = Z² · inverseRSq(x). -/
lemma coulombMultiplier_sq (p : CoulombParams) (x : R3) :
    coulombMultiplier p x ^ 2 = p.Z ^ 2 * inverseRSq x := by
  simp only [coulombMultiplier, inverseRSq]
  split_ifs with h
  · simp
  · field_simp

/-! ## (1/r)ψ is in L² for ψ ∈ H¹ -/

/-- **The Coulomb potential applied to an H¹ function is in L².**

    ‖(Z/r)ψ‖² = Z² ∫ |ψ|²/|x|² dx = Z² · hardyIntegral(ψ) < ∞.

    **Discharge route:**
    1. ∫ |V(x)ψ(x)|² dx = Z² ∫ |ψ(x)|²/|x|² dx (pointwise).
    2. The RHS is Z² · hardyIntegral(ψ) ≤ 4Z² · gradientNormSq(ψ) < ∞
       (from `hardy_inequality` and finiteness of gradientNormSq).
    3. Measurability: product of measurable functions. -/
theorem coulomb_mul_memLp
    (p : CoulombParams) (ψ : L2_R3) (hψ : MemSobolevH1 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) :=
  sorry

/-- The Coulomb potential applied to an H² function is in L². -/
theorem coulomb_mul_memLp_H2
    (p : CoulombParams) (ψ : L2_R3) (hψ : MemSobolevH2 ψ) :
    MemLp (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
      2 (volume : Measure R3) :=
  coulomb_mul_memLp p ψ (sobolevH2_le_H1 hψ)

/-! ## The Coulomb potential as a linear map on H² -/

/-- **The Coulomb potential as a linear map on H².**

    V : H²(ℝ³) →ₗ[ℂ] L²(ℝ³) defined by (Vψ)(x) = (−Z/|x|) · ψ(x).

    This is well-defined by `coulomb_mul_memLp_H2`: the product
    (−Z/|x|)ψ(x) is in L² whenever ψ ∈ H² ⊆ H¹.

    **Discharge route for linearity:**
    - add: (−Z/|x|)(ψ₁ + ψ₂) = (−Z/|x|)ψ₁ + (−Z/|x|)ψ₂ pointwise a.e.
    - smul: (−Z/|x|)(cψ) = c(−Z/|x|)ψ pointwise a.e.
    Both lift to L² equalities via ae-extensionality. -/
def coulombPotential (p : CoulombParams) : SobolevH2 →ₗ[ℂ] L2_R3 where
  toFun := fun ⟨ψ, hψ⟩ =>
    (coulomb_mul_memLp_H2 p ψ hψ).toLp
      (fun x => (coulombMultiplier p x : ℂ) * (ψ : R3 → ℂ) x)
  map_add' := fun ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩ => by
    sorry  -- ae: V(ψ₁+ψ₂) = Vψ₁ + Vψ₂, from mul_add + Lp.coeFn_add
  map_smul' := fun c ⟨ψ, hψ⟩ => by
    sorry  -- ae: V(cψ) = cVψ, from mul_comm/mul_assoc + Lp.coeFn_smul

/-! ## Transport to Generator.domain

The Kato-Rellich theorem expects V as a linear map on
`laplacianGenerator.domain`, not on `SobolevH2` directly.
We transport via the domain equality `laplacianGenerator_domain`.
-/

/-- Transport the Coulomb potential to `laplacianGenerator.domain`.

    Since `laplacianGenerator.domain = SobolevH2` (from
    `laplacianGenerator_domain`), this is a definitional transport.

    **Discharge route:** Rewrite along `laplacianGenerator_domain`,
    composing with the submodule equivalence. -/
def coulombOnGeneratorDomain (p : CoulombParams) :
    laplacianGenerator.domain →ₗ[ℂ] L2_R3 :=
  sorry  -- transport coulombPotential along laplacianGenerator_domain

/-! ## Symmetry -/

/-- **The Coulomb potential is symmetric on H².**

    ⟨Vψ, φ⟩ = ⟨ψ, Vφ⟩ for ψ, φ ∈ H².

    **Discharge route:**
    Since V is pointwise multiplication by the *real-valued* function
    −Z/|x|, we have:

      ⟨Vψ, φ⟩ = ∫ (−Z/|x|)ψ(x) · φ̄(x) dx
               = ∫ ψ(x) · (−Z/|x|)φ̄(x) dx    (−Z/|x| is real)
               = ∫ ψ(x) · conj((−Z/|x|)φ(x)) dx   (conj commutes with real mult)
               = ⟨ψ, Vφ⟩

    The key step is that for real-valued f:
      f(x) · conj(g(x)) = conj(f(x) · g(x))
    which holds because conj(f(x)) = f(x) when f is real. -/
theorem coulomb_symmetric (p : CoulombParams) :
    ∀ (ψ φ : SobolevH2),
      ⟪coulombPotential p ψ, (φ : L2_R3)⟫_ℂ =
      ⟪(ψ : L2_R3), coulombPotential p φ⟫_ℂ :=
  sorry

/-- Symmetry transported to the generator domain. -/
theorem coulomb_symmetric_on_domain (p : CoulombParams) :
    IsSymmetricOn laplacianGenerator (coulombOnGeneratorDomain p) :=
  sorry  -- transport of coulomb_symmetric along laplacianGenerator_domain

/-! ## Relative boundedness -/

/-- **The Coulomb potential is (−Δ)-bounded with any a > 0.**

    For any ε > 0, there exists C_ε ≥ 0 such that:
      ‖Vψ‖ ≤ ε ‖(−Δ)ψ‖ + C_ε ‖ψ‖    for all ψ ∈ H²

    **Discharge route:**
    1. ‖Vψ‖² = Z² · hardyIntegral(ψ) (from `coulombMultiplier_sq`).
    2. hardyIntegral(ψ) ≤ 4 ⟨−Δψ, ψ⟩ (from `hardy_quadratic_form`).
    3. ⟨−Δψ, ψ⟩ ≤ ‖−Δψ‖ · ‖ψ‖ (Cauchy-Schwarz).
    4. ‖Vψ‖² ≤ 4Z² ‖−Δψ‖ · ‖ψ‖ (combine 1-3).
    5. Young: ab ≤ (ε²/2)a² + (1/(2ε²))b² gives
       ‖Vψ‖² ≤ 2Z²ε² ‖−Δψ‖² + 2Z²/ε² ‖ψ‖².
    6. √(α² + β²) ≤ α + β for α, β ≥ 0 gives
       ‖Vψ‖ ≤ √(2)Zε ‖−Δψ‖ + √(2)Z/ε ‖ψ‖.
    7. Relabel ε' = √(2)Zε.

    The estimate uses `weakLaplacian` via `laplacianGenerator_op`.
    Transport to generator domain uses `laplacianGenerator_domain`. -/
theorem coulomb_relatively_bounded_H2 (p : CoulombParams)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ψ : L2_R3) (hψ : MemSobolevH2 ψ),
      ‖(coulombPotential p ⟨ψ, hψ⟩ : L2_R3)‖ ≤
      ε * ‖weakLaplacian ψ hψ‖ + C * ‖ψ‖ :=
  sorry

/-- **The Coulomb potential is relatively bounded on the generator domain.**

    Transport of `coulomb_relatively_bounded_H2` to `laplacianGenerator`. -/
theorem coulomb_relatively_bounded (p : CoulombParams)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ ψ : laplacianGenerator.domain,
      ‖coulombOnGeneratorDomain p ψ‖ ≤
      ε * ‖laplacianGenerator.op ψ‖ + C * ‖(ψ : L2_R3)‖ :=
  sorry  -- transport of coulomb_relatively_bounded_H2 along domain equality


/-- **Package as `IsRelativelyBounded` with any a > 0.**

    This is the form consumed by `kato_rellich`. -/
def coulomb_isRelativelyBounded (p : CoulombParams) (a : ℝ) (ha : 0 < a) :
    IsRelativelyBounded laplacianGenerator (coulombOnGeneratorDomain p) :=
  { a := a
    b := (coulomb_relatively_bounded p a ha).choose
    ha := le_of_lt ha
    hb := (coulomb_relatively_bounded p a ha).choose_spec.1
    bound := (coulomb_relatively_bounded p a ha).choose_spec.2 }

/-- **The relative bound is 0.**

    For any a > 0, there exists b such that ‖Vψ‖ ≤ a‖(−Δ)ψ‖ + b‖ψ‖.
    Hence the infimum of valid a-constants is 0. -/
theorem coulomb_relative_bound_is_zero (p : CoulombParams) :
    ∀ a : ℝ, 0 < a →
    ∃ b : ℝ, 0 ≤ b ∧
    ∀ ψ : laplacianGenerator.domain,
      ‖coulombOnGeneratorDomain p ψ‖ ≤
      a * ‖laplacianGenerator.op ψ‖ + b * ‖(ψ : L2_R3)‖ :=
  fun a ha => coulomb_relatively_bounded p a ha

/-! ## All Kato-Rellich hypotheses verified -/

/-- **Complete verification of Kato-Rellich hypotheses for the Coulomb potential.**

    For any nuclear charge Z > 0:
    1. −Δ is self-adjoint (`laplacian_isSelfAdjoint`).
    2. V = −Z/r is symmetric on Dom(−Δ) (`coulomb_symmetric_on_domain`).
    3. V is (−Δ)-bounded with bound 0 (`coulomb_relative_bound_is_zero`).
    4. Hence a < 1 for any chosen a > 0.

    Kato-Rellich then gives: H = −Δ − Z/r is self-adjoint on H²(ℝ³). -/
theorem coulomb_kato_rellich_ready (p : CoulombParams) :
    laplacianGenerator.IsSelfAdjoint ∧
    IsSymmetricOn laplacianGenerator (coulombOnGeneratorDomain p) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ b : ℝ, 0 ≤ b ∧
      ∀ ψ : laplacianGenerator.domain,
        ‖coulombOnGeneratorDomain p ψ‖ ≤
        ε * ‖laplacianGenerator.op ψ‖ + b * ‖(ψ : L2_R3)‖) :=
  ⟨laplacian_isSelfAdjoint,
   coulomb_symmetric_on_domain p,
   coulomb_relative_bound_is_zero p⟩


/-! ## Interface summary

### Exports for `HydrogenHamiltonian.lean`:
- `CoulombParams` — nuclear charge Z
- `coulombOnGeneratorDomain` — V on laplacianGenerator.domain
- `coulomb_kato_rellich_ready` — all hypotheses bundled
- `coulombPotential` — V on SobolevH2 (for explicit computations)

### Usage in HydrogenHamiltonian.lean:
```
  let ⟨hsa, hsym, hbound⟩ := coulomb_kato_rellich_ready p
  -- Choose a = 1/2 < 1
  let ⟨b, hb, hest⟩ := hbound (1/2) (by norm_num)
  let hV_bdd : IsRelativelyBounded laplacianGenerator _ :=
    { a := 1/2, b := b, ha := by norm_num, hb := hb, bound := hest }
  -- Apply Kato-Rellich
  obtain ⟨U_grp', gen', h_dom, h_sa, h_op⟩ :=
    kato_rellich laplacianGenerator hsa _ hsym hV_bdd (by norm_num)
```
-/


end QuantumMechanics.Hydrogen
