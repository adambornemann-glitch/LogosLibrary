/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: NanoThermo/Limits.lean
-/
import LogosLibrary.Superior.HotGravity.NanoThermo.Definition
/-!
=====================================================================
## The Thermodynamic Limit
=====================================================================

As N → ∞, the subdivision potential ε = T·I(A:B)/N → 0.

Classical thermodynamics is recovered in the large-N limit.
The "anomalies" are 1/N effects. Real, but diluted.

**However**: the TOTAL subdivision energy N·ε = T·I(A:B) is
independent of N. The mutual information doesn't dilute.
Only the per-particle share does.

This is the complete story of why nanothermodynamics matters:
- For N ~ 100 (nanoclusters): ε ~ T/100. Measurable.
- For N ~ 10²³ (bulk matter): ε ~ T/10²³. Invisible.

The modular structure is always there. We just can't see it
at macroscopic scales. The "anomalies" in chemistry journals
are it peeking through at the nanoscale.

**Contents:**
1. Total cost is constant: N·ε = T·I (independent of N!)
2. Per-particle cost vanishes: ε → 0 as N → ∞
3. Rate of convergence: ε ≤ 2T·S(A)/N
4. H* ≥ H_bare (always — the cost is never negative)
5. H* ≤ H_bare + 2T·S(A)/N (explicit upper bound)
6. The sandwich: H_bare ≤ H* ≤ H_bare + 2T·S(A)/N
7. Classical thermo emerges: H*(N) → H_bare as N → ∞
-/
namespace NanoThermodynamics.Limits
open NanoThermodynamics.Definition
open MinkowskiSpace
open ThermalTime Basic
/-!
### The Total Cost Is Constant
-/

/-- **THEOREM**: The total subdivision energy is independent of N.

    N · ε = T · I(A:B)

    The total entropic cost of the cut is a property of the cut
    itself — the mutual information, scaled by temperature.
    It does NOT depend on how many particles you divide it among.

    Physical meaning: the correlation across the boundary is fixed.
    More particles means each one bears a smaller share of that
    correlation. But the total doesn't change. -/
theorem total_subdivision_energy
    (T : ℝ) (N : ℝ) (hN : N > 0) (cut : AlgebraicCut) :
    N * subdivisionPotential T N cut = T * mutualInformation cut := by
  unfold subdivisionPotential
  have hN_ne : N ≠ 0 := ne_of_gt hN
  field_simp


/-- **COROLLARY**: The total subdivision energy transforms as energy.

    N · ε → γ · (N · ε) under Lorentz boost.
    Equivalently: the total cost T·I transforms as T does (Ott). -/
theorem total_subdivision_energy_covariant
    (T : ℝ) (_hT : T > 0) (N : ℝ) (hN : N > 0) (cut : AlgebraicCut)
    (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    let T' := γ * T
    N * subdivisionPotential T' N cut = γ * (N * subdivisionPotential T N cut) := by
  simp only
  rw [total_subdivision_energy T N hN cut,
      total_subdivision_energy (lorentzGamma v hv * T) N hN cut]
  ring


/-!
### The Per-Particle Cost Vanishes
-/

/-- **THEOREM**: The thermodynamic limit.

    ε = T · I(A:B) / N → 0  as  N → ∞

    Classical thermodynamics emerges in the large-N limit.
    The per-particle cost of the algebraic cut vanishes.

    This is WHY Hill needed nanothermodynamics: for small N,
    ε is non-negligible. For large N, it vanishes and classical
    thermo suffices.

    The mutual information is still there — but spread over
    10²³ particles, each particle's share is invisible.

    **Proof structure**: ε = C/N where C = T·I is a constant.
    C/N = C · N⁻¹ → C · 0 = 0 as N → ∞.
    This is `tendsto_const_nhds.mul tendsto_inv_atTop_zero`. -/
theorem thermodynamic_limit (T : ℝ) (cut : AlgebraicCut) :
    Filter.Tendsto (fun N => subdivisionPotential T N cut)
                   Filter.atTop (nhds 0) := by
  unfold subdivisionPotential
  set C := T * mutualInformation cut with hC_def
  -- C / N = C · N⁻¹ → C · 0 = 0 as N → ∞
  rw [show (0 : ℝ) = C * 0 by ring]
  exact tendsto_const_nhds.mul tendsto_inv_atTop_zero


/-!
### Rate of Convergence
-/

/-- **THEOREM**: Explicit bound on the subdivision potential.

    ε ≤ 2T · S(A) / N

    The rate of convergence is O(1/N). The constant is
    controlled by the subsystem entropy S(A).

    Proof: uses I(A:B) ≤ 2·S(A) (mutual information bounded
    by twice the subsystem entropy).

    Physical meaning: the per-particle cost is at most
    2T·S(A)/N. For a thermal state at room temperature with
    S(A) ~ 1 nat and N ~ 100, this gives ε ~ 6 K.
    Detectable in nanocluster experiments.
    For N ~ 10²³, invisible. -/
theorem subdivision_potential_bound
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cut : AlgebraicCut) :
    subdivisionPotential T N cut ≤ 2 * T * cut.S_A / N := by
  unfold subdivisionPotential
  have h_mi := mutual_information_le_twice_S_A cut
  have h1 : T * mutualInformation cut ≤ T * (2 * cut.S_A) :=
    mul_le_mul_of_nonneg_left h_mi (le_of_lt hT)
  have h2 : T * (2 * cut.S_A) = 2 * T * cut.S_A := by ring
  rw [h2] at h1
  exact div_le_div_of_nonneg_right h1 (le_of_lt hN)


/-- **THEOREM**: Symmetric bound via S(B).

    ε ≤ 2T · S(B) / N

    The cost is bounded by EITHER subsystem's entropy.
    You can't have more correlation than information. -/
theorem subdivision_potential_bound_B
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cut : AlgebraicCut) :
    subdivisionPotential T N cut ≤ 2 * T * cut.S_B / N := by
  unfold subdivisionPotential
  have h_mi := mutual_information_le_twice_S_B cut
  have h1 : T * mutualInformation cut ≤ T * (2 * cut.S_B) :=
    mul_le_mul_of_nonneg_left h_mi (le_of_lt hT)
  have h2 : T * (2 * cut.S_B) = 2 * T * cut.S_B := by ring
  rw [h2] at h1
  exact div_le_div_of_nonneg_right h1 (le_of_lt hN)


/-!
### Bounds on the Effective Hamiltonian
-/

/-- **THEOREM**: The effective Hamiltonian is always at least the bare one.

    H*_A ≥ H_A.  Always. No exceptions.

    Strong coupling makes the effective Hamiltonian LARGER.
    The cut costs energy (or more precisely: the entropic cost
    of the cut, converted to energy via T, is always non-negative).

    Proof: H* - H_bare = ε ≥ 0 (subdivision potential is non-negative). -/
theorem hmf_ge_bare (sys : NanoSystem) :
    sys.H_star ≥ sys.H_bare := by
  have h_ε := subdivision_potential_nonneg sys.T sys.hT sys.N sys.hN sys.cut
  linarith [sys.h_subdivision]


/-- **THEOREM**: Explicit upper bound on the effective Hamiltonian.

    H*_A ≤ H_A + 2T · S(A) / N

    The effective Hamiltonian exceeds the bare one by at most
    the upper bound on the subdivision potential. -/
theorem hmf_upper_bound (sys : NanoSystem) :
    sys.H_star ≤ sys.H_bare + 2 * sys.T * sys.cut.S_A / sys.N := by
  have h_bound := subdivision_potential_bound sys.T sys.hT sys.N sys.hN sys.cut
  linarith [sys.h_subdivision]


/-- **THE SANDWICH**: The effective Hamiltonian is trapped.

    H_bare ≤ H*_A ≤ H_bare + 2T · S(A) / N

    The lower bound is tight (equality iff I = 0, i.e., weak coupling).
    The upper bound is tight (equality iff I = 2·S(A), i.e., pure total state).

    Physical meaning: the effective Hamiltonian is the bare one
    plus a correction that lives in the interval [0, 2T·S(A)/N].
    As N → ∞, the interval shrinks to a point.
    Classical thermodynamics is the N → ∞ limit of this sandwich. -/
theorem hmf_sandwich (sys : NanoSystem) :
    sys.H_bare ≤ sys.H_star ∧
    sys.H_star ≤ sys.H_bare + 2 * sys.T * sys.cut.S_A / sys.N :=
  ⟨hmf_ge_bare sys, hmf_upper_bound sys⟩


/-!
### Classical Thermodynamics Emerges
-/

/-- **THEOREM**: The effective Hamiltonian approaches the bare one.

    For a family of systems with increasing N (same temperature,
    same algebraic cut, same bare Hamiltonian):

    H*_A(N) = H_bare + T · I(A:B) / N → H_bare  as  N → ∞

    Classical thermodynamics emerges as the large-N limit of
    nanothermodynamics. Not as an approximation — as a theorem.

    The modular structure is always there. It just becomes
    invisible per particle. -/
theorem hmf_approaches_bare
    (H_bare T : ℝ) (_hT : T > 0) (cut : AlgebraicCut) :
    Filter.Tendsto
      (fun N => H_bare + subdivisionPotential T N cut)
      Filter.atTop (nhds H_bare) := by
  have h : Filter.Tendsto
      (fun N => H_bare + subdivisionPotential T N cut)
      Filter.atTop (nhds (H_bare + 0)) :=
    tendsto_const_nhds.add (thermodynamic_limit T cut)
  rwa [add_zero] at h


/-- **COROLLARY**: The modular Hamiltonian approaches H_bare / T.

    K(N) = H*(N) / T → H_bare / T  as  N → ∞

    In the large-N limit, the generator of restricted modular flow
    is just the bare Hamiltonian divided by temperature. The
    "restricted" part becomes trivial. -/
theorem modular_hamiltonian_approaches_bare
    (H_bare T : ℝ) (hT : T > 0) (cut : AlgebraicCut) :
    Filter.Tendsto
      (fun N => modularHamiltonian (H_bare + subdivisionPotential T N cut) T)
      Filter.atTop (nhds (modularHamiltonian H_bare T)) := by
  simp only [modularHamiltonian]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  -- (H_bare + ε) / T → H_bare / T  because  ε → 0
  -- Equivalently: (H_bare + ε) / T = H_bare / T + ε / T → H_bare / T + 0
  have h_eq : (fun N => (H_bare + subdivisionPotential T N cut) / T) =
      (fun N => H_bare / T + subdivisionPotential T N cut / T) := by
    ext N; ring
  rw [h_eq]
  have h_zero : Filter.Tendsto (fun N => subdivisionPotential T N cut / T)
      Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = 0 / T by simp]
    exact Filter.Tendsto.div_const (thermodynamic_limit T cut) T
  have h : Filter.Tendsto
      (fun N => H_bare / T + subdivisionPotential T N cut / T)
      Filter.atTop (nhds (H_bare / T + 0)) :=
    tendsto_const_nhds.add h_zero
  rwa [add_zero] at h


/-!
### Physical Summary

The thermodynamic limit tells us:

1. **Total cost is constant**: N·ε = T·I(A:B), independent of N.
   The correlation is a property of the cut, not the particles.

2. **Per-particle cost vanishes**: ε → 0 as N → ∞.
   Classical thermo emerges because you can't see T·I/10²³.

3. **The rate is 1/N**: ε ≤ 2T·S(A)/N.
   Nanosystems (N ~ 100) feel it. Bulk matter doesn't.

4. **H* is sandwiched**: H_bare ≤ H* ≤ H_bare + 2T·S(A)/N.
   The effective Hamiltonian is always between the bare one
   and the bare one plus the bound. As N → ∞, the sandwich
   collapses to a point.

5. **K → H_bare/T**: The restricted modular generator approaches
   the bare modular generator. The "restricted" becomes trivial.

The experiments that detected the anomalies — nanoclusters,
thermophoresis, molecular motors — were operating at N where
T·I/N was large enough to see. They were measuring the
modular structure of the algebraic cut.

At macroscopic scales, the modular structure is still there.
It's just diluted across 10²³ particles. Invisible.

Until now, nobody knew what "it" was.
Now we know: it's restricted thermal time.
-/
end NanoThermodynamics.Limits
