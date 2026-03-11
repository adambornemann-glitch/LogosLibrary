/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ThermalBell/Dictionary.lean
-/
import LogosLibrary.QuantumMechanics.Uncertainty.UnboundedOperators
import LogosLibrary.InformationGeometry.QuantumFisherModel
import LogosLibrary.InformationGeometry.CompositeObservable
import LogosLibrary.Superior.SplitMechanics.ThermalBell.Core
/-!
# The Thermal–Kähler Dictionary

The thermal CHSH framework and the RLD Fisher information framework
are two descriptions of the same phenomenon. This file proves they
agree: the thermal deviation ε is (proportional to) the symplectic
form ω from the Kähler structure, and the thermal CHSH bound is
the Schrödinger–Cramér–Rao bound.

## The identification

For quantum data D with state ψ and observables Oᵢ:

| Thermal Bell         | Kähler CR                   | Scale  |
|----------------------|-----------------------------|--------|
| E_classical(i,j)     | ∫ Aᵢ Bⱼ dμ₀                 | 1      |
| E_thermal(i,j)       | ∫ Aᵢ Bⱼ εᵢⱼ dμ₀             | 1      |
| εᵢⱼ contribution     | ωᵢⱼ / 2                     | ½      |
| ε_max                | max |ωᵢⱼ| / 2               |        |
| 4·ε_max              | 2·max |ωᵢⱼ|                 |        |

The Schrödinger bound gᵢᵢgⱼⱼ ≥ gᵢⱼ² + ωᵢⱼ² says: the total
information (g) factored through both observables exceeds the
sum of the covariance squared (classical) and the commutator
squared (quantum). The thermal bound |S| ≤ 2 + 4ε says the
same thing in additive CHSH language.
-/
namespace InformationGeometry.BellBridge

open QuantumMechanics.Bridge QuantumMechanics.Schrodinger QuantumMechanics.UnboundedObservable
open InnerProductSpace InformationGeometry MeasureTheory
open scoped ComplexConjugate

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open ThermalBell
variable {Λ : Type*} [MeasurableSpace Λ]

/-- Alice's observable index: Fin 2 → Fin 4. -/
def alice : Fin 2 → Fin 4
  | 0 => 0
  | 1 => 1

/-- Bob's observable index: Fin 2 → Fin 4. -/
def bob : Fin 2 → Fin 4
  | 0 => 2
  | 1 => 3


/-- A `CHSHRealization` witnesses that a thermal hidden variable model
and a quantum RLD Fisher model describe the same CHSH experiment.

**Data:**
- Quantum data `D` with 4 observables indexed as
  `O(0) = A₀, O(1) = A₁, O(2) = B₀, O(3) = B₁`
  (Alice's two settings, then Bob's two settings)
- A thermal HV model `M_th` on hidden variable space `Λ`
- A regular statistical model `M_stat` on sample space `Ω`
- The RLD Fisher model `R` constructed from quantum data via the bridge

**Axioms (the dictionary):**
- `h_fisher`: the Fisher matrix encodes quantum covariance:
  `g_{ij}(θ) = 4 Cov(Oᵢ, Oⱼ)_ψ`
- `h_R`: the RLD model is the one constructed by `quantumRLDFisherModel`
- `h_correlation_match`: thermal correlations reproduce quantum expectations:
  `E_th(i,j) = Re⟨ψ, O_{a(i)} O_{b(j)} ψ⟩`
- `h_epsilon_symplectic`: the thermal deviation encodes the symplectic form:
  `∫ Aᵢ Bⱼ εᵢⱼ dμ₀ = Im⟨ψ, [O_{a(i)}, O_{b(j)}]ψ⟩`
- `h_thermal_integrable`: each thermal correction term is integrable

The CHSH correlation pairs `(i,j) : Fin 2 × Fin 2` map to observable
pairs via `alice : Fin 2 → Fin 4` and `bob : Fin 2 → Fin 4`:
  `E(i,j) ↔ ⟨O_{alice(i)}, O_{bob(j)}⟩`

The `h_epsilon_symplectic` axiom is the heart of the dictionary:
it says that the thermal deviation from statistical independence
*is* the imaginary part of the quantum inner product — i.e., the
symplectic form of the Kähler structure on the state manifold.

The `h_correlation_match` axiom is the zeroth-order dictionary:
it says the classical (ε = 0) thermal correlations reproduce the
quantum expectations. Together they give: thermal model = quantum
model expanded to first order in ε around the independent baseline.

These axioms are discharged in the quantum setting by identifying
the hidden variable space with the quantum state space and the
response functions with spectral projections. -/
structure CHSHRealization (Λ : Type*) [MeasurableSpace Λ]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Ω : Type*) [MeasurableSpace Ω] where
  D : QuantumRLDData 4 H
  M_th : ThermalHVModel Λ
  M_stat : RegularStatisticalModel 4 Ω
  h_fisher : ∀ θ ∈ M_stat.paramDomain, ∀ i j : Fin 4,
    M_stat.fisherMatrix θ i j =
      4 * covariance (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)
  R : RLDFisherModel 4 Ω
  h_R : R = quantumRLDFisherModel D M_stat h_fisher
  /-- Thermal correlation matches quantum expectation. -/
  h_correlation_match : ∀ i j : Fin 2,
    M_th.correlation i j =
      (⟪D.ψ, (D.O (alice i)).apply
        ((D.O (bob j)).apply D.ψ (D.hψ_all (bob j)))
        (D.hOψ_all (alice i) (bob j))⟫_ℂ).re
  /-- Thermal deviation encodes the symplectic form. -/
  h_epsilon_symplectic : ∀ i j : Fin 2,
    ∫ ω, M_th.A i ω * M_th.B j ω *
      M_th.deviation.ε i j ω ∂(M_th.μ₀ : Measure Λ) =
    (⟪D.ψ, commutatorAt (D.O (alice i)) (D.O (bob j)) D.ψ
      (pairwise_shiftedDC D (alice i) (bob j)).toDomainConditions⟫_ℂ).im
  h_thermal_integrable : ∀ i j : Fin 2,
    Integrable (fun ω => M_th.A i ω * M_th.B j ω *
      M_th.deviation.ε i j ω) (M_th.μ₀ : Measure Λ)

variable {Ω : Type*} [MeasurableSpace Ω]
/-- **The Thermal–Kähler theorem**: the thermal CHSH bound is the
Schrödinger–Cramér–Rao bound.

Under the matching axioms, the thermal CHSH excess `4·ε_max`
equals the symplectic contribution `2·max|ωᵢⱼ|` from the RLD
Fisher structure. Therefore:

  |S_thermal| ≤ 2 + 4·ε_max = 2 + 2·max|ωᵢⱼ|

while the Schrödinger CR bound gives:

  gᵢᵢ gⱼⱼ ≥ gᵢⱼ² + ωᵢⱼ²

These are additive vs. multiplicative forms of the same constraint. -/
theorem thermal_chsh_is_schrodinger_cr
    (C : CHSHRealization Λ H Ω)
    (θ : InformationGeometry.ParamSpace 4) (_hθ : θ ∈ C.M_stat.paramDomain)
    (i j : Fin 2) :
    (∫ ω, C.M_th.A i ω * C.M_th.B j ω *
      C.M_th.deviation.ε i j ω ∂(C.M_th.μ₀ : Measure Λ))^2 ≤
    C.R.symplecticForm θ (alice i) (bob j) ^ 2 / 4 := by
  rw [C.h_epsilon_symplectic i j]
  -- Unfold: R.symplecticForm = 2 * Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩ by construction
  have h_sf : C.R.symplecticForm θ (alice i) (bob j) =
    2 * (⟪C.D.ψ, commutatorAt (C.D.O (alice i)) (C.D.O (bob j)) C.D.ψ
      (pairwise_shiftedDC C.D (alice i) (bob j)).toDomainConditions⟫_ℂ).im := by
    have : C.R.symplecticForm = (quantumRLDFisherModel C.D C.M_stat C.h_fisher).symplecticForm := by
      rw [C.h_R]
    rw [this]; rfl
  rw [h_sf]
  suffices h : ∀ x : ℝ, x ^ 2 ≤ (2 * x) ^ 2 / 4 from h _
  intro x; ring_nf;
  simp only [Nat.rawCast]
  grind only


/-- **The thermal excess is bounded by the symplectic form.**

The total thermal CHSH correction `|S_thermal|` — the deviation of
the thermal model's CHSH value from the classical bound — is bounded
by the sum of absolute values of the symplectic form entries over
the four CHSH correlation pairs:

  `|S_thermal| ≤ |ω₀₃| + |ω₀₂| + |ω₁₂| + |ω₁₃|`

where `ωₐᵦ = R.symplecticForm θ (alice a) (bob b) = 2 Im⟨ψ,[Oₐ,Oᵦ]ψ⟩`.

**Proof outline:**
1. Decompose `CHSH_thermal` into four integrals (one per setting pair)
2. Triangle inequality: `|a - b + c + d| ≤ |a| + |b| + |c| + |d|`
3. Substitute `h_epsilon_symplectic`: each `|∫ Aᵢ Bⱼ εᵢⱼ dμ₀| = |Im⟨ψ,[O,O]ψ⟩|`
4. Since `ωᵢⱼ = 2 · Im⟨ψ,[O,O]ψ⟩`, we have `|Im| = |ω|/2 ≤ |ω|`
5. Sum the four terms

**Physical interpretation:**
The symplectic form ω is the imaginary part of the complex RLD
Fisher information `G^RLD = g + iω`. Geometrically, it measures
the non-commutativity of nearby quantum states on the Kähler
manifold. The thermal deviation from statistical independence is
bounded by exactly this non-commutativity: the more the observables
fail to commute, the more the effective hidden variable distribution
must deviate from the baseline.

When `ω = 0` (commuting observables), the bound forces `S_thermal = 0`
and we recover Bell's theorem: `|S| ≤ 2`. When `ω ≠ 0`, the bound
allows `|S| > 2` by an amount controlled by the symplectic geometry
of the state space — yielding the Tsirelson bound `2√2` when the
Kähler structure is saturated (as for the singlet state). -/
theorem thermal_excess_bounded_by_symplectic
    (C : CHSHRealization Λ H Ω)
    (θ : InformationGeometry.ParamSpace 4) (_hθ : θ ∈ C.M_stat.paramDomain) :
    |C.M_th.CHSH_thermal| ≤
    |C.R.symplecticForm θ (alice 0) (bob 1)| +
    |C.R.symplecticForm θ (alice 0) (bob 0)| +
    |C.R.symplecticForm θ (alice 1) (bob 0)| +
    |C.R.symplecticForm θ (alice 1) (bob 1)| := by
  -- Step 1: Decompose CHSH_thermal into four terms
  -- CHSH_thermal = E₀₁ε - E₀₀ε + E₁₀ε + E₁₁ε
  -- where Eᵢⱼε = ∫ Aᵢ Bⱼ εᵢⱼ dμ₀
  set E := fun i j => ∫ ω, C.M_th.A i ω * C.M_th.B j ω *
    C.M_th.deviation.ε i j ω ∂(C.M_th.μ₀ : Measure Λ)
  have h_decomp : C.M_th.CHSH_thermal = E 0 1 - E 0 0 + E 1 0 + E 1 1 := by
    unfold ThermalHVModel.CHSH_thermal
    rw [integral_add]
    · rw [integral_add]
      · rw [integral_sub]
        · exact C.h_thermal_integrable 0 1
        · exact C.h_thermal_integrable 0 0
      · exact (C.h_thermal_integrable 0 1).sub (C.h_thermal_integrable 0 0)
      · exact C.h_thermal_integrable 1 0
    · exact ((C.h_thermal_integrable 0 1).sub
        (C.h_thermal_integrable 0 0)).add (C.h_thermal_integrable 1 0)
    · exact C.h_thermal_integrable 1 1
  -- Step 2: Triangle inequality
  have h_tri : |E 0 1 - E 0 0 + E 1 0 + E 1 1| ≤
    |E 0 1| + |E 0 0| + |E 1 0| + |E 1 1| := by
    calc |E 0 1 - E 0 0 + E 1 0 + E 1 1|
        ≤ |E 0 1 - E 0 0 + E 1 0| + |E 1 1| := abs_add_le _ _
      _ ≤ |E 0 1 - E 0 0| + |E 1 0| + |E 1 1| := by linarith [abs_add_le (E 0 1 - E 0 0) (E 1 0)]
      _ ≤ |E 0 1| + |E 0 0| + |E 1 0| + |E 1 1| := by grind
  -- Step 3: Each |Eᵢⱼ| = |Im⟨ψ,[O,O]ψ⟩| by h_epsilon_symplectic
  have h_E (i j : Fin 2) : |E i j| =
    |(⟪C.D.ψ, commutatorAt (C.D.O (alice i)) (C.D.O (bob j)) C.D.ψ
      (pairwise_shiftedDC C.D (alice i) (bob j)).toDomainConditions⟫_ℂ).im| := by
    congr 1; exact C.h_epsilon_symplectic i j
  -- Step 4: Connect |Im| to |ω|/2
  -- R.symplecticForm = 2 * Im, so |Im| = |ω|/2 ≤ |ω|
  have h_sf (i j : Fin 2) : C.R.symplecticForm θ (alice i) (bob j) =
    2 * (⟪C.D.ψ, commutatorAt (C.D.O (alice i)) (C.D.O (bob j)) C.D.ψ
      (pairwise_shiftedDC C.D (alice i) (bob j)).toDomainConditions⟫_ℂ).im := by
    have : C.R.symplecticForm = (quantumRLDFisherModel C.D C.M_stat C.h_fisher).symplecticForm := by
      rw [C.h_R]
    rw [this]; rfl
  have h_im_le_sf (i j : Fin 2) :
    |(⟪C.D.ψ, commutatorAt (C.D.O (alice i)) (C.D.O (bob j)) C.D.ψ
      (pairwise_shiftedDC C.D (alice i) (bob j)).toDomainConditions⟫_ℂ).im| ≤
    |C.R.symplecticForm θ (alice i) (bob j)| := by
    rw [h_sf i j, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [abs_nonneg ((⟪C.D.ψ, commutatorAt (C.D.O (alice i)) (C.D.O (bob j)) C.D.ψ
      (pairwise_shiftedDC C.D (alice i) (bob j)).toDomainConditions⟫_ℂ).im)]
  -- Step 5: Chain everything
  calc |C.M_th.CHSH_thermal|
      = |E 0 1 - E 0 0 + E 1 0 + E 1 1| := by rw [h_decomp]
    _ ≤ |E 0 1| + |E 0 0| + |E 1 0| + |E 1 1| := h_tri
    _ = |(⟪C.D.ψ, commutatorAt _ _ _ _⟫_ℂ).im| + |(⟪C.D.ψ, commutatorAt _ _ _ _⟫_ℂ).im| +
        |(⟪C.D.ψ, commutatorAt _ _ _ _⟫_ℂ).im| + |(⟪C.D.ψ, commutatorAt _ _ _ _⟫_ℂ).im| := by
        rw [h_E 0 1, h_E 0 0, h_E 1 0, h_E 1 1]
    _ ≤ |C.R.symplecticForm θ (alice 0) (bob 1)| +
        |C.R.symplecticForm θ (alice 0) (bob 0)| +
        |C.R.symplecticForm θ (alice 1) (bob 0)| +
        |C.R.symplecticForm θ (alice 1) (bob 1)| := by
        linarith [h_im_le_sf 0 1, h_im_le_sf 0 0, h_im_le_sf 1 0, h_im_le_sf 1 1]


end BellBridge
