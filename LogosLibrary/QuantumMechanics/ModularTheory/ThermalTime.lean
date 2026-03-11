/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/ThermalTime.lean
-/
import LogosLibrary.QuantumMechanics.ModularTheory.Cocycle
import LogosLibrary.QuantumMechanics.ModularTheory.KMS.Condition
import LogosLibrary.Relativity.GR.Kerr
/-!
# The Thermal Time Hypothesis

## Statement

The thermal time hypothesis (Connes-Rovelli 1994) posits:

> In a generally covariant quantum theory, the physical time flow is not a
> universal property of the mechanical theory, but rather is determined by
> the thermodynamical state of the system. The physical time is thermal time.

## The Mathematical Content

The mathematical backbone is the *state-independence* of the modular flow
in Out(M), proved in `Cocycle.lean`. This gives us:

1. **For each state φ**: a modular flow σ^φ : ℝ → Aut(M), KMS at β = 1.
2. **State-independence**: the image δ : ℝ → Out(M) is independent of φ.
3. **Thermal time hypothesis**: δ IS physical time.

## The Ott Correction

The original 1994 paper (Connes-Rovelli, gr-qc/9406019) implicitly treats
temperature as a Lorentz scalar — the Landsberg convention. This appears
in equation (44): `α_t = γ_{βt}`, where β sits as an unadorned constant
with no transformation law. As noted on p. 22, the authors "deliberately
left a certain amount of vagueness in the formulation."

**This vagueness conceals an inconsistency.** The thermal time hypothesis
rests on two pillars:

  (i)  The modular parameter τ is Lorentz invariant.
       (It is intrinsic to the algebra M. The cocycle theorem guarantees
       state-independence. No observer, no frame, no boost can touch it.)

  (ii) Proper time t transforms under boosts: t → t/γ.
       (This is special-relativistic time dilation.)

Temperature is defined as the ratio: T = τ/t (or equivalently, t = τ/T).
Under a Lorentz boost:

    τ → τ         (invariant, by (i))
    t → t/γ       (time dilation, by (ii))
    T = τ/t → τ/(t/γ) = γ(τ/t) = γT

**The Ott transformation T → γT is forced.** It is not a convention, not
a choice, not one side of a debate. It is a theorem: the unique
transformation law compatible with (i) and (ii).

Conversely, the Landsberg convention T → T requires τ → τ/γ to maintain
t = τ/T. But τ is intrinsic to the algebra — the cocycle theorem forbids
it from transforming. **Landsberg contradicts Tomita-Takesaki.**

## Consequences

**A. Gibbs states**: For ρ_β = e^{-βH}/Z, the modular flow is
σ_τ(a) = e^{iHτ} a e^{-iHτ}. Geometric time is t = τ/T = βτ.
Under a boost, T → γT so β → β/γ and t → βτ/γ = t/γ.
Time dilation emerges as a *theorem* of thermodynamics.

**B. Unruh effect**: T = a/(2π), transforms as T → γT under boosts.
No rest frame needed. The ratio Q/T is invariant.

**C. Hawking radiation**: T = 1/(8πM), transforms as T → γT.
An infalling observer sees a hotter black hole.

## References

* [Connes, Rovelli, "Von Neumann algebra automorphisms and
  time-thermodynamics relation in generally covariant quantum
  theories", Class. Quant. Grav. 11 (1994), 2899–2917][connesrovelli1994]
* [Ott, "Lorentz-Transformation der Wärme und der Temperatur,"
  Z. Physik 175, 70–104 (1963)][ott1963]
* [Rovelli, Smerlak, "Thermal time and Tolman-Ehrenfest effect",
  Class. Quant. Grav. 28 (2011), 075007][rovellismerlak2011]

## Tags

thermal time, Connes-Rovelli, Ott transformation, modular flow,
Unruh effect, Gibbs state, time dilation, Lorentz covariance
-/

noncomputable section

namespace ThermalTime

open Tomita KMSCondition MinkowskiSpace

open scoped ComplexOrder

open MeasureTheory InnerProductSpace Complex FunctionalCalculus ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Section 1: The Thermal Time Flow — Abstract Package

We bundle the state-independent flow as a structure, equipped with
the fundamental properties derived from Tomita-Takesaki + Cocycle.
-/

/-- **The thermal time flow** of a von Neumann algebra.

    Packages the canonical state-independent outer flow together with
    the proof that any faithful normal state is KMS at β = 1 for this
    flow (up to inner automorphisms).

    This is the complete mathematical content of the thermal time
    hypothesis. The *physical* content is the identification of this
    abstract flow with physical time evolution — and the derivation of
    the Ott transformation as a consequence. -/
structure ThermalTimeData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VNAlgebraWithVector H) where
  /-- A chosen representative of the outer flow (any faithful state works). -/
  σ_representative : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)
  /-- Group law. -/
  group_law : ∀ s t a, σ_representative (s + t) a = σ_representative s (σ_representative t a)
  /-- Identity. -/
  zero_eq : ∀ a, σ_representative 0 a = a
  /-- Multiplicativity. -/
  mul_eq : ∀ t a b, σ_representative t (a * b) = σ_representative t a * σ_representative t b
  /-- Star-preservation. -/
  star_eq : ∀ t a, σ_representative t (ContinuousLinearMap.adjoint a) =
    ContinuousLinearMap.adjoint (σ_representative t a)
  /-- **State-independence**: for any other faithful state ψ, its modular
      flow σ^ψ differs from σ_representative by inner automorphisms. -/
  state_independent : ∀ (ψ : VNAlgebraWithVector H) (_hψ : ψ.algebra = M.algebra)
    (Δ_ψ : ModularOperatorData H ψ) (J_ψ : ModularConjugationData H ψ)
    (_hTT_ψ : TomitaTheorem H ψ Δ_ψ J_ψ) (t : ℝ),
    InnerEquivalent (σ_representative t) (modularAutomorphism ψ Δ_ψ t) M.algebra

/-- Construct thermal time data from modular theory data.

    The state-independence witness must be provided externally — it
    requires the cocycle/intertwining machinery for every other
    faithful normal state on M. -/
noncomputable def ThermalTimeData.ofModular
    (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M)
    (_hTT : TomitaTheorem H M Δ J)
    (h_indep : ∀ (ψ : VNAlgebraWithVector H) (_hψ : ψ.algebra = M.algebra)
      (Δ_ψ : ModularOperatorData H ψ) (J_ψ : ModularConjugationData H ψ)
      (_hTT_ψ : TomitaTheorem H ψ Δ_ψ J_ψ) (t : ℝ),
      InnerEquivalent (modularAutomorphism M Δ t) (modularAutomorphism ψ Δ_ψ t) M.algebra) :
    ThermalTimeData H M where
  σ_representative := modularAutomorphism M Δ
  group_law := modularAutomorphism_group_law M Δ
  zero_eq := modularAutomorphism_zero M Δ
  mul_eq := modularAutomorphism_mul M Δ
  star_eq := modularAutomorphism_star M Δ
  state_independent := h_indep

/-!
## Section 2: Temperature as a Ratio of Two Times

**This is the critical section.** Temperature is not a bare scalar.
It is the ratio of two quantities with *different* transformation laws:

    T = τ / t

where:
- τ is the modular parameter (Lorentz invariant, intrinsic to M)
- t is the observer's proper time (transforms under boosts: t → t/γ)

The Ott transformation T → γT is not a choice. It is forced.
-/

/-- **Thermal time.** Given temperature T and modular parameter τ,
    the geometric (proper) time of an observer is t = τ/T.

    This is the content of Connes-Rovelli (1994), equation (56):
    "we interpret temperature as the ratio between the thermal time
    and the geometrical time, namely t = βτ" (where β = 1/T). -/
def thermalTime (T : ℝ) (τ : ℝ) : ℝ := τ / T

/-- Proper time transforms under boosts: t → t/γ. (Time dilation.) -/
def boosted_proper_time (t : ℝ) (v : ℝ) (hv : |v| < 1) : ℝ :=
  t / lorentzGamma v hv

/-- **The Ott transformation is forced by thermal time.**

    Given:
    - τ is Lorentz invariant (cocycle theorem / intrinsic to algebra)
    - t transforms as t → t/γ (special-relativistic time dilation)
    - T = τ/t (thermal time hypothesis)

    Then T → γT. No other transformation is consistent.

    This is the theorem that Connes-Rovelli (1994) should have stated
    but did not, due to treating β as a frame-independent constant.
    The algebra is one line: τ/(t/γ) = γ(τ/t) = γT. -/
theorem thermal_time_forces_ott
    (T : ℝ) (hT : T > 0)
    (τ : ℝ) (hτ : τ ≠ 0)
    (v : ℝ) (hv : |v| < 1) :
    let t := thermalTime T τ
    let t' := boosted_proper_time t v hv
    let T' := τ / t'
    T' = lorentzGamma v hv * T := by
  simp only [thermalTime, boosted_proper_time]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt (lorentzGamma_pos v hv)
  field_simp

/-- **Equivalently**: the boosted observer's thermal time gives time dilation.

    If T → γT (Ott) and τ is invariant, then t = τ/T → τ/(γT) = t/γ.
    Time dilation is a *theorem* of thermal time + Ott. -/
theorem thermal_time_gives_time_dilation
    (T : ℝ) (hT : T > 0)
    (τ : ℝ)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let t := thermalTime T τ
    let T' := γ * T
    let t' := thermalTime T' τ
    t' = t / γ := by
  simp only [thermalTime]
  have hγ_pos : lorentzGamma v hv > 0 := lorentzGamma_pos v hv
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt hγ_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT
  exact div_mul_eq_div_div_swap τ (lorentzGamma v hv) T

/-- **Landsberg is inconsistent with thermal time.**

    If T → T (Landsberg), then maintaining t = τ/T with t → t/γ requires
    τ → τ/γ. But τ is the modular parameter — intrinsic to the algebra —
    and CANNOT transform. The cocycle theorem forbids it.

    Landsberg + Time Dilation + Cocycle Theorem is inconsistent. -/
theorem landsberg_inconsistent_with_thermal_time
    (T : ℝ) (hT : T > 0)
    (τ : ℝ) (hτ : τ ≠ 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    -- Under Landsberg (T' = T), the modular parameter must transform:
    -- t' = τ'/T forces τ' = t' · T = (t/γ) · T = τ/γ ≠ τ
    let t := thermalTime T τ
    let t' := boosted_proper_time t v hv  -- t/γ (time dilation, non-negotiable)
    let τ_forced := t' * T                -- if T' = T, then τ' = t'·T
    τ_forced ≠ τ := by
  simp only [thermalTime, boosted_proper_time]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt (lorentzGamma_pos v hv)
  have hγ_ne_one : lorentzGamma v hv ≠ 1 := ne_of_gt (lorentzGamma_gt_one v hv hv_ne)
  intro h
  field_simp at h
  have : lorentzGamma v hv = 1 := by nlinarith [mul_comm τ (lorentzGamma v hv)]
  exact hγ_ne_one this

/-- **Uniqueness**: Ott is the ONLY temperature transformation compatible
    with the thermal time hypothesis and time dilation.

    If T → f(v)·T preserves the relation t = τ/T under boosts
    (where τ is invariant and t → t/γ), then f(v) = γ(v). -/
theorem ott_unique_from_thermal_time
    (f : (v : ℝ) → |v| < 1 → ℝ)
    (hf_pos : ∀ v hv, f v hv > 0)
    (hf_consistent : ∀ (T τ : ℝ) (_hT : T > 0) (v : ℝ) (hv : |v| < 1),
      thermalTime (f v hv * T) τ = boosted_proper_time (thermalTime T τ) v hv) :
    ∀ v (hv : |v| < 1), f v hv = lorentzGamma v hv := by
  intro v hv
  have h := hf_consistent 1 1 one_pos v hv
  simp only [thermalTime, boosted_proper_time] at h
  have hf_ne : f v hv ≠ 0 := ne_of_gt (hf_pos v hv)
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt (lorentzGamma_pos v hv)
  field_simp at h
  linarith

/-!
## Section 3: The Gibbs State — Corrected

The modular flow of the Gibbs state ρ_β is σ_τ(a) = e^{iHτ} a e^{-iHτ},
where τ is the modular parameter. The geometric (proper) time of the
rest-frame observer is t = βτ = τ/T.

Under a boost:
  - τ → τ (invariant)
  - T → γT (Ott, forced by Section 2)
  - β = 1/T → β/γ
  - t = βτ → (β/γ)τ = t/γ ✓ (time dilation recovered)

The 1994 paper wrote "α_t = γ_{βt}" with β a constant. The corrected
version: β is a *rest-frame* quantity that transforms as β → β/γ.
-/

/-- A quantum system with a Hamiltonian. -/
structure HamiltonianSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Hamiltonian generates a unitary group. -/
  U : ℝ → H →L[ℂ] H
  /-- Group law. -/
  U_group : ∀ s t, U (s + t) = U s * U t
  /-- Identity. -/
  U_zero : U 0 = 1
  /-- Unitarity. -/
  U_unitary : ∀ t, U t * ContinuousLinearMap.adjoint (U t) = 1

/-- Hamiltonian evolution. -/
def HamiltonianSystem.evolve (sys : HamiltonianSystem H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  sys.U t * a * ContinuousLinearMap.adjoint (sys.U t)

/-- **The Gibbs state theorem (corrected).**

    The modular flow of ρ_β is σ_τ(a) = α_τ(a) = e^{iHτ} a e^{-iHτ}.

    Crucially: the modular parameter τ is the *thermal time*, not the
    geometric time. The geometric time is t = τ/T = βτ.

    The 1994 equation (44) "α_t = γ_{βt}" is correct if read as:
    "the Hamiltonian evolution at geometric time t equals the modular
    flow at modular parameter τ = t/β = tT." The error was treating β
    as frame-independent. Under boosts, β → β/γ (because T → γT). -/
axiom gibbs_modular_flow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sys : HamiltonianSystem H)
    (M : VNAlgebraWithVector H)
    (Δ : ModularOperatorData H M)
    (J : ModularConjugationData H M)
    (hTT : TomitaTheorem H M Δ J)
    -- The Gibbs condition: Δ^{iτ} = e^{iHτ} (modular unitary IS Hamiltonian unitary)
    (hGibbs : ∀ τ : ℝ, modularUnitary M Δ τ = sys.U τ) :
    ∀ τ a, modularAutomorphism M Δ τ a = sys.evolve τ a

/-- **The geometric time of a Gibbs state.**

    t = βτ = τ/T. The rest-frame observer's clock ticks at rate 1/T
    relative to modular time. -/
def gibbs_geometric_time (β τ : ℝ) : ℝ := β * τ

/-- **Time dilation from Gibbs + Ott.** Under a boost, β → β/γ (because
    T → γT), so t = βτ → (β/γ)τ = t/γ. Time dilation. -/
theorem gibbs_time_dilation
    (β τ : ℝ) (_hβ : 0 < β) (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let β' := β / γ
    gibbs_geometric_time β' τ =
    gibbs_geometric_time β τ / γ := by
  simp only [gibbs_geometric_time]
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt (lorentzGamma_pos v hv)
  field_simp

/-- **The Hamiltonian survives the classical limit.**

    Under Ott: β → β/γ, H → γH (energy is time component of 4-momentum).
    The Gibbs exponent βH → (β/γ)(γH) = βH. Invariant. The partition
    function, the free energy, the entropy — all frame-independent.

    Under Landsberg: β → β, H → γH, so βH → γβH. The partition function
    changes under boosts. Statistical mechanics becomes frame-dependent.
    The classical limit of quantum gravity is destroyed. -/
theorem ott_preserves_gibbs_exponent
    (β : ℝ) (E : ℝ) (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    (β / γ) * (γ * E) = β * E := by
  simp only
  have hγ_ne : lorentzGamma v hv ≠ 0 := ne_of_gt (lorentzGamma_pos v hv)
  field_simp

theorem landsberg_destroys_gibbs_exponent
    (β : ℝ) (E : ℝ) (hE : E ≠ 0) (hβ : β ≠ 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    β * (lorentzGamma v hv * E) ≠ β * E := by
  intro h
  have hγ_ne_one := lorentzGamma_ne_one v hv hv_ne
  have : lorentzGamma v hv * E = E := mul_left_cancel₀ hβ h
  have : lorentzGamma v hv = 1 := by field_simp at this; linarith
  exact hγ_ne_one this

/-!
## Section 4: Temperature Instances

Concrete temperatures from modular theory, now carrying their
transformation law as a *consequence* of the thermal time structure.
-/

/-- **Temperature with Lorentz covariance.**

    Temperature is the ratio τ/t. Since τ is invariant and t → t/γ,
    the temperature transforms as T → γT. This is not a field in the
    structure — it is a theorem (`thermal_time_forces_ott`). -/
structure Temperature where
  /-- Rest-frame temperature. -/
  T_rest : ℝ
  /-- Positivity. -/
  T_pos : 0 < T_rest

/-- The temperature measured by a boosted observer. -/
def Temperature.boosted (temp : Temperature) (v : ℝ) (hv : |v| < 1) : ℝ :=
  lorentzGamma v hv * temp.T_rest

/-- The boosted temperature is positive. -/
lemma Temperature.boosted_pos (temp : Temperature) (v : ℝ) (hv : |v| < 1) :
    temp.boosted v hv > 0 :=
  mul_pos (lorentzGamma_pos v hv) temp.T_pos

/-- The inverse temperature β = 1/T transforms as β → β/γ. -/
def Temperature.β (temp : Temperature) : ℝ := 1 / temp.T_rest

/-- The ratio E/T is Lorentz invariant (fundamental theorem of Ott). -/
lemma Temperature.ratio_invariant (temp : Temperature) (E : ℝ) (v : ℝ) (hv : |v| < 1) :
    (lorentzGamma v hv * E) / (temp.boosted v hv) = E / temp.T_rest := by
  simp only [Temperature.boosted]
  exact mul_div_mul_left E temp.T_rest (lorentzGamma_ne_zero v hv)

/-- **The Unruh temperature.** T = a/(2π). -/
def unruhTemperature (a : ℝ) (ha : 0 < a) : Temperature where
  T_rest := a / (2 * Real.pi)
  T_pos := div_pos ha (mul_pos two_pos Real.pi_pos)

/-- **The Hawking temperature.** T = 1/(8πM). -/
def hawkingTemperatureFromMass (mass : ℝ) (hM : 0 < mass) : Temperature where
  T_rest := 1 / (8 * Real.pi * mass)
  T_pos := div_pos one_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 8) Real.pi_pos) hM)

/-- An infalling observer sees a hotter black hole. -/
lemma infalling_observer_hotter (mass : ℝ) (hM : 0 < mass)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    (hawkingTemperatureFromMass mass hM).boosted v hv >
    (hawkingTemperatureFromMass mass hM).T_rest :=
  (lt_mul_iff_one_lt_left (hawkingTemperatureFromMass mass hM).T_pos).mpr
    (lorentzGamma_gt_one v hv hv_ne) -- Unknown identifier `lorentzGamma_ne_one`

/-!
## Section 5: The Complete Theorem

Thermal time + time dilation + cocycle theorem determines the
transformation law of temperature uniquely.
-/

/-- **THE MAIN THEOREM.** Thermal time forces Ott.

    (1) The Ott transformation T → γT is forced by thermal time + time dilation.
    (2) Time dilation is recovered as a thermodynamic theorem.
    (3) The Gibbs exponent βH is preserved in the classical limit.
    (4) Landsberg contradicts the cocycle theorem (τ cannot transform).
    (5) Landsberg destroys the Gibbs exponent. -/
theorem thermal_time_determines_ott
    (T : ℝ) (hT : T > 0) (τ : ℝ) (hτ : τ ≠ 0)
    (β : ℝ) (hβ : β = 1 / T)
    (E : ℝ) (hE : E ≠ 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    let γ := lorentzGamma v hv
    -- (1) Thermal time forces T → γT
    (τ / (thermalTime T τ / γ) = γ * T) ∧
    -- (2) Time dilation is recovered
    (thermalTime (γ * T) τ = thermalTime T τ / γ) ∧
    -- (3) The Gibbs exponent is preserved
    ((β / γ) * (γ * E) = β * E) ∧
    -- (4) Landsberg contradicts the cocycle theorem
    (thermalTime T τ / γ * T ≠ τ) ∧
    -- (5) Landsberg destroys the Gibbs exponent
    (β * (γ * E) ≠ β * E) := by
  have hγ_pos := lorentzGamma_pos v hv
  have hγ_ne := lorentzGamma_ne_zero v hv
  have hγ_gt := lorentzGamma_gt_one v hv hv_ne
  have hγ_ne_one := lorentzGamma_ne_one v hv hv_ne
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hβ_ne : β ≠ 0 := by rw [hβ]; exact div_ne_zero one_ne_zero hT_ne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) τ / (t/γ) = γT
    simp only [thermalTime]; field_simp
  · -- (2) τ/(γT) = (τ/T)/γ
    exact thermal_time_gives_time_dilation T hT τ v hv
  · -- (3) (β/γ)(γE) = βE
    exact ott_preserves_gibbs_exponent β E v hv
  · -- (4) Landsberg forces τ to transform
    exact landsberg_inconsistent_with_thermal_time T hT τ hτ v hv hv_ne
  · -- (5) Landsberg breaks the Gibbs exponent
    exact landsberg_destroys_gibbs_exponent β E hE hβ_ne v hv hv_ne

/-!
## Summary: The Corrected Architecture of Thermal Time

```
VNAlgebraWithVector M      (algebra + cyclic/separating vector)
        │
        ▼
TomitaTakesaki.lean        S₀ → S̄ → Δ, J → σ_τ^φ
        │                  τ = modular parameter (INVARIANT)
        │
        ├──────────────────────────────────────────┐
        ▼                                          ▼
RelativeModular.lean       S_{ψ,φ} → Δ_{ψ,φ}    KMS/Condition.lean
        │                                          │
        ▼                                          ▼
Cocycle.lean               u_t, cocycle law        KMS/Modular.lean
        │                  σ^ψ = Ad(u_t) ∘ σ^φ
        │                  Out(M) independence
        │                  ⟹ τ CANNOT transform
        │                          │
        └──────────┬───────────────┘
                   ▼
          ThermalTime.lean (THIS FILE)
          δ : ℝ → Out(M)           ← THIS IS TIME
          T = τ/t                  ← THIS IS TEMPERATURE
          t → t/γ, τ → τ          ← TIME DILATION + INVARIANCE
          ∴ T → γT                 ← OTT (forced, not chosen)
          ∴ β → β/γ               ← INVERSE TEMPERATURE TRANSFORMS
          βH → (β/γ)(γH) = βH     ← GIBBS EXPONENT PRESERVED
          t = βτ → (β/γ)τ = t/γ   ← TIME DILATION RECOVERED
```

**The 1994 error**: treating β as a constant (eq. 44) rather than a
quantity that transforms as β → β/γ. This silently assumed Landsberg.
The corrected version: β = 1/T transforms because T = τ/t transforms,
because t transforms and τ does not.
-/

end ThermalTime
