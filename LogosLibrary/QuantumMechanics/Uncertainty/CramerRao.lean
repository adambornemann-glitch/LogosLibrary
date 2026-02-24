/-
Copyright (c) 2026 Information Geometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann & co.
-/
import LogosLibrary.InformationGeometry.CramerRao
import LogosLibrary.QuantumMechanics.Uncertainty.Robertson

/-!
# Quantum Uncertainty from Information Geometry

The **Robertson uncertainty relation** `σ_A σ_B ≥ ½|⟨[A,B]⟩|` and its
special case, the **Heisenberg uncertainty principle** `σ_X σ_P ≥ ℏ/2`,
are usually proved by Cauchy–Schwarz in Hilbert space.

This file derives them instead from the **Cramér–Rao bound** of
information geometry, making explicit the deep connection:

  *Quantum uncertainty is a manifestation of the Fisher metric.*

The bridge is a one-parameter statistical model induced by the
**quantum phase shift** `ψ(θ) = e^{−iθA} ψ`.  Measuring observable
`B` on `ψ(θ)` gives a probability distribution over outcomes
parametrised by `θ`.  Three identities connect the two worlds:

1. **Quantum Fisher information:**
   `I(θ₀) = 4 Var_ψ(A)`.

2. **Born rule → estimator variance:**
   `Var_stat(T) = Var_ψ(B)`.

3. **Ehrenfest → derivative:**
   `dτ/dθ|_{θ₀} = Im⟨ψ, [A,B]ψ⟩`.

Substituting into `Var(T) ≥ (dτ/dθ)² / I(θ)` yields Robertson.

## Main definitions

* `QuantumPhaseModel` — bridge structure carrying quantum data,
  a 1-parameter statistical model, and three axioms connecting them.

## Main results

* `fisher_pos` — `I(θ₀) > 0` from `Var(A) > 0`.
* `cramerRao_substituted` — Cramér–Rao with quantum substitutions.
* `variance_product_ge` — `Var(A) · Var(B) ≥ Im⟨ψ,[A,B]ψ⟩² / 4`.
* `robertson_from_fisher` — `σ_A σ_B ≥ ½ ‖⟨ψ,[A,B]ψ⟩‖`.
* `heisenberg_from_fisher` — `σ_X σ_P ≥ ℏ/2`.

## Design notes

**Approach A: axiomatise, then backfill.** The three bridge axioms
are fields of `QuantumPhaseModel`. Future work (Approach B)
constructs a `QuantumPhaseModel` from finite-dimensional data,
discharging all axioms from the Born rule and spectral theory.

## Connection to thermodynamics

Fisher information `I(θ) = ∫ (∂ log p)² p dμ` has the same form as
entropy production rate.  The Cramér–Rao bound is therefore a
**thermodynamic uncertainty relation**: the precision of any
measurement is bounded by the entropy cost of the perturbation
that reveals the quantity being measured.

## References

* S. Braunstein, C. Caves, "Statistical distance and the geometry
  of quantum states", *Phys. Rev. Lett.* **72** (1994), 3439–3443.
* S. Amari, *Information Geometry and Its Applications*, §2–3, 2016.
* H. P. Robertson, "The uncertainty principle",
  *Phys. Rev.* **34** (1929), 163–164.
-/

noncomputable section

open MeasureTheory Real Set Filter
open InnerProductSpace
open scoped Topology ComplexConjugate

namespace QuantumMechanics.CramerRao

open InformationGeometry RegularStatisticalModel
open QuantumMechanics.UnboundedObservable
open QuantumMechanics.Robertson (ShiftedDomainConditions)

variable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The quantum phase model -/

/-- A `QuantumPhaseModel` bridges quantum mechanics and information
geometry.  It bundles quantum data (observables A, B, state ψ),
a 1-parameter statistical model on a sample space Ω (induced by
measuring B on the phase-shifted state e^{−iθA}ψ), and the three
physical axioms connecting the statistical and quantum quantities.

The axioms are satisfied by the Born-rule model for any pair of
observables on any Hilbert space.  They are stated as fields here
(Approach A) to be discharged from finite-dimensional constructions
in future work (Approach B). -/
structure QuantumPhaseModel
    (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- The generator of the phase shift. -/
  A : UnboundedObservable H
  /-- The measured observable. -/
  B : UnboundedObservable H
  /-- The normalised quantum state. -/
  ψ : H
  /-- Domain + normalisation conditions. -/
  h_dom : ShiftedDomainConditions A B ψ
  /-- The 1-parameter statistical model. -/
  model : RegularStatisticalModel 1 Ω
  /-- The base parameter (θ = 0). -/
  θ₀ : ParamSpace 1
  /-- θ₀ ∈ Θ. -/
  hθ₀ : θ₀ ∈ model.paramDomain
  /-- The estimator (B-measurement outcome). -/
  T : Ω → ℝ
  /-- The target function τ(θ) = E_{ψ(θ)}[B]. -/
  τ : ParamSpace 1 → ℝ
  /-- Estimator regularity. -/
  hReg : model.IsRegularEstimator T
  /-- Unbiasedness: E_θ[T] = τ(θ). -/
  hUnbiased : model.IsUnbiasedEstimator T τ
  /-- τ is differentiable at θ₀. -/
  hτ_diff : DifferentiableAt ℝ τ θ₀
  /-- Score square-integrability. -/
  hSq : model.ScoreSqIntegrableModel θ₀
  /-- **Axiom I (Quantum Fisher Information).**
  `I(θ₀) = 4 Var_ψ(A)`. -/
  fisher_eq_four_varA :
    model.fisherMatrix θ₀ 0 0 =
      4 * A.variance ψ h_dom.h_norm h_dom.hψ_A
  /-- **Axiom II (Born Rule → Variance).**
  `Var_stat(T) = Var_ψ(B)`. -/
  stat_variance_eq_quantum_variance :
    model.variance hθ₀ T =
      B.variance ψ h_dom.h_norm h_dom.hψ_B
  /-- **Axiom III (Ehrenfest → Derivative).**
  `dτ/dθ|_{θ₀} = Im⟨ψ, [A,B]ψ⟩`. -/
  derivative_eq_commutator_expect :
    fderiv ℝ τ θ₀ (EuclideanSpace.single 0 1) =
      (⟪ψ, commutatorAt A B ψ
        h_dom.toDomainConditions⟫_ℂ).im
  /-- Nondegeneracy: `Var_ψ(A) > 0`. -/
  varA_pos : 0 < A.variance ψ h_dom.h_norm h_dom.hψ_A


variable {Ω : Type*} [MeasurableSpace Ω]

namespace QuantumPhaseModel

variable (Q : QuantumPhaseModel H Ω)

/-! ### Derived positivity -/

/-- The Fisher information is positive: `I(θ₀) > 0`.
Immediate from `I = 4 Var(A)` and `Var(A) > 0`. -/
theorem fisher_pos :
    0 < Q.model.fisherMatrix Q.θ₀ 0 0 := by
  rw [Q.fisher_eq_four_varA]; linarith [Q.varA_pos]

/-! ### The Cramér–Rao bound with quantum substitutions -/
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (M : RegularStatisticalModel n Ω)
/-- **Cramér–Rao with bridge axioms substituted.**

  `Var_ψ(B) ≥ Im⟨ψ,[A,B]ψ⟩² / (4 Var_ψ(A))` -/
theorem cramerRao_substituted :
    Q.B.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B ≥
      ((⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
        Q.h_dom.toDomainConditions⟫_ℂ).im) ^ 2 /
      (4 * Q.A.variance Q.ψ Q.h_dom.h_norm
        Q.h_dom.hψ_A) := by
  have hCR :=
    RegularStatisticalModel.cramerRao_scalar Q.model
      Q.hθ₀ Q.T Q.τ Q.hReg Q.hUnbiased Q.hτ_diff
      (0 : Fin 1) Q.hSq Q.fisher_pos
  rw [Q.stat_variance_eq_quantum_variance,
      Q.derivative_eq_commutator_expect,
      Q.fisher_eq_four_varA] at hCR
  exact hCR

/-! ### The variance product inequality -/

/-- **Variance product form of quantum uncertainty.**

  `Var_ψ(A) · Var_ψ(B) ≥ Im⟨ψ, [A,B]ψ⟩² / 4`

Obtained by multiplying `cramerRao_substituted` through by
`Var_ψ(A) > 0`. -/
theorem variance_product_ge :
    Q.A.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A *
    Q.B.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B ≥
    ((⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
      Q.h_dom.toDomainConditions⟫_ℂ).im) ^ 2 / 4 := by
  set varA := Q.A.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A
  set varB := Q.B.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B
  set C := (⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
    Q.h_dom.toDomainConditions⟫_ℂ).im
  have hCR := Q.cramerRao_substituted
  have hVA := Q.varA_pos
  -- Clear the denominator: varB ≥ C²/(4·varA)
  -- ⟹ C² ≤ 4·varA·varB  (since 4·varA > 0)
  have h_denom_pos : (0 : ℝ) < 4 * varA := by linarith
  have h_cleared : C ^ 2 ≤ 4 * varA * varB := by
    exact (div_le_iff₀' h_denom_pos).mp hCR
  -- varA · varB ≥ C²/4  ⟺  4·(varA · varB) ≥ C²
  rw [ge_iff_le, div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
  linarith

/-! ### Robertson from Fisher -/

/-- **Robertson uncertainty from information geometry.**

  `σ_A · σ_B ≥ ½ ‖⟨ψ, [A,B]ψ⟩‖`

This is `robertson_uncertainty` from `Robertson.lean`, but derived
via the Cramér–Rao bound instead of direct Cauchy–Schwarz in `H`.

**Proof.** From `variance_product_ge`, take square roots, using
`⟨ψ,[A,B]ψ⟩` purely imaginary (`commutator_re_eq_zero`) to
convert `Im(⟨[A,B]⟩)²` to `‖⟨[A,B]⟩‖²`. -/
theorem robertson_from_fisher :
    Q.A.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A *
    Q.B.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B ≥
    (1 / 2) * ‖⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
      Q.h_dom.toDomainConditions⟫_ℂ‖ := by
  set varA := Q.A.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A
  set varB := Q.B.variance Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B
  set z := ⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
    Q.h_dom.toDomainConditions⟫_ℂ
  -- ⟨ψ,[A,B]ψ⟩ is purely imaginary
  have h_re_zero : z.re = 0 :=
    commutator_re_eq_zero Q.A Q.B Q.ψ
      Q.h_dom.toDomainConditions
  -- ‖z‖ = |z.im|
  have h_norm_eq : ‖z‖ = |z.im| :=
    QuantumMechanics.Robertson.norm_eq_abs_im_of_re_zero
      h_re_zero
  -- variance_product_ge: varA · varB ≥ z.im² / 4
  have hVP := Q.variance_product_ge
  -- Since ‖z‖² = z.im² (as z.re = 0):
  --   varA · varB ≥ ‖z‖² / 4 = (½ ‖z‖)²
  have h_norm_sq : z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [h_norm_eq, sq_abs]
  -- √(varA · varB) ≥ √(‖z‖²/4) = ‖z‖/2
  have h_sqrt_bound :
      Real.sqrt (varA * varB) ≥
      Real.sqrt (‖z‖ ^ 2 / 4) := by
    apply Real.sqrt_le_sqrt
    rw [← h_norm_sq]
    exact hVP.le
  -- LHS: σ_A · σ_B = √(varA · varB)
  have h_lhs :
      Q.A.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A *
      Q.B.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B =
      Real.sqrt (varA * varB) := by
    simp only [UnboundedObservable.stdDev]
    rw [← Real.sqrt_mul
      (UnboundedObservable.variance_nonneg Q.A Q.ψ
        Q.h_dom.h_norm Q.h_dom.hψ_A)]
  -- RHS: √(‖z‖²/4) = ½ · ‖z‖
  have h_rhs :
      Real.sqrt (‖z‖ ^ 2 / 4) = (1 / 2) * ‖z‖ := by
    rw [div_eq_mul_inv, ← mul_comm,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4⁻¹),
        Real.sqrt_sq (norm_nonneg z)]
    have : Real.sqrt (4⁻¹ : ℝ) = 1 / 2 := by
      rw [show (4⁻¹ : ℝ) = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [this]
  rw [h_lhs]; linarith [h_sqrt_bound, h_rhs]

/-! ### Heisenberg from Fisher -/

/-- **Heisenberg uncertainty principle from information geometry.**

For canonically conjugate observables with
`⟨ψ, [X,P]ψ⟩ = iℏ`:

  `σ_X · σ_P ≥ ℏ / 2`

Derived by specialising `robertson_from_fisher` to the canonical
commutation relation and computing `‖iℏ‖ = ℏ`. -/
theorem heisenberg_from_fisher
    (ℏ : ℝ) (hℏ_pos : 0 < ℏ)
    (h_canonical :
      ⟪Q.ψ, commutatorAt Q.A Q.B Q.ψ
        Q.h_dom.toDomainConditions⟫_ℂ =
      Complex.I * (ℏ : ℂ)) :
    Q.A.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_A *
    Q.B.stdDev Q.ψ Q.h_dom.h_norm Q.h_dom.hψ_B ≥
    ℏ / 2 := by
  have hR := Q.robertson_from_fisher
  rw [h_canonical] at hR
  have h_norm : ‖Complex.I * (ℏ : ℂ)‖ = ℏ := by
    rw [norm_mul, Complex.norm_I, one_mul]
    rw [Complex.norm_real, norm_eq_abs, abs_of_pos hℏ_pos]
  linarith

end QuantumPhaseModel

/-! ### Where the physics lives

The three bridge axioms are not arbitrary — they encode the
entire quantum-mechanical measurement theory:

**Axiom I** (Fisher = 4 Var(A)) encodes the Born rule plus
spectral completeness.  The factor of 4 arises because quantum
states live in a *complex* Hilbert space: differentiating
`|⟨b|e^{−iθA}|ψ⟩|²` in θ produces a factor of 2 from the
absolute-value square and another from `|f|² = f f*`.

**Axiom II** (Var_stat = Var_QM) is the Born rule in its
most elementary form: classical and quantum probability agree
on measurement outcomes.

**Axiom III** (dτ/dθ = Im⟨[A,B]⟩) is Ehrenfest's theorem:
`d/dθ ⟨B⟩_θ = i⟨[A,B]⟩`, with Im extracting the real derivative.

These three facts, together with the Cramér–Rao inequality
(pure mathematics), suffice to derive the uncertainty principle.

In this sense, **quantum uncertainty is a corollary of the
second law**: Fisher information is entropy production rate,
and Cramér–Rao says no estimator can beat the entropic cost
of distinguishing nearby distributions.  The second law does
not merely permit quantum uncertainty — it *requires* it. -/

end QuantumMechanics.CramerRao
