/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: NanoThermo/Biconditional.lean
-/
import LogosLibrary.Superior.HotGravity.NanoThermo.Definition

namespace NanoThermodynamics.Bijection
open NanoThermodynamics.Definition ThermalTime.Basic
/-!
=====================================================================
## The Weak Coupling Biconditional
=====================================================================

H*_A = H_A  ↔  I(A:B) = 0

The effective Hamiltonian equals the bare Hamiltonian
**if and only if** there are no correlations across the cut.

Forward: already proved as `hmf_equals_bare_weak_coupling`.
Backward: H* = H_bare ⟹ T·I/N = 0 ⟹ I = 0 (since T > 0 and N > 0).

This is the clean characterization: weak coupling is not an
approximation, not a regime, not a limit. It is the exact
condition of zero mutual information. Nothing more. Nothing less.
-/

/-- **THEOREM**: H* = H_bare implies zero mutual information.

    The converse of `hmf_equals_bare_weak_coupling`.
    If the effective Hamiltonian equals the bare one, there are
    no correlations to discard. The cut costs nothing. -/
theorem hmf_bare_implies_zero_MI (sys : NanoSystem)
    (h : sys.H_star = sys.H_bare) :
    mutualInformation sys.cut = 0 := by
  have h_sub := sys.h_subdivision
  -- H* - H_bare = T · I / N, but H* = H_bare, so 0 = T · I / N
  have h_zero : subdivisionPotential sys.T sys.N sys.cut = 0 := by linarith
  unfold subdivisionPotential at h_zero
  -- T · I / N = 0, with T > 0 and N > 0
  have hT_ne : sys.T ≠ 0 := ne_of_gt sys.hT
  have hN_ne : sys.N ≠ 0 := ne_of_gt sys.hN
  have hI := mutual_information_nonneg sys.cut
  -- T · I / N = 0 and T > 0 and N > 0 → I = 0
  by_contra h_ne
  have hI_pos : mutualInformation sys.cut > 0 := lt_of_le_of_ne hI (Ne.symm h_ne)
  have h_pos : subdivisionPotential sys.T sys.N sys.cut > 0 :=
    subdivision_potential_pos_of_correlated sys.T sys.hT sys.N sys.hN sys.cut hI_pos
  linarith


/-- **THE BICONDITIONAL**: H*_A = H_A  ↔  I(A:B) = 0

    The effective Hamiltonian equals the bare Hamiltonian
    if and only if there are no correlations across the cut.

    Weak coupling is not an approximation. It is the exact
    algebraic condition of zero mutual information.

    This is the complete characterization of when classical
    thermodynamics is exact (not approximate — EXACT). -/
theorem weak_coupling_iff (sys : NanoSystem) :
    sys.H_star = sys.H_bare ↔ mutualInformation sys.cut = 0 :=
  ⟨hmf_bare_implies_zero_MI sys, hmf_equals_bare_weak_coupling sys⟩


/-- **COROLLARY**: H*_A ≠ H_A  ↔  I(A:B) > 0

    The effective Hamiltonian differs from the bare one
    if and only if correlations exist.

    "Anomalous" behavior ↔ correlations. That's it. -/
theorem strong_coupling_iff (sys : NanoSystem) :
    sys.H_star ≠ sys.H_bare ↔ mutualInformation sys.cut > 0 := by
  constructor
  · intro h_ne
    have h_not_zero : mutualInformation sys.cut ≠ 0 :=
      fun h_zero => h_ne (hmf_equals_bare_weak_coupling sys h_zero)
    exact lt_of_le_of_ne (mutual_information_nonneg sys.cut) (Ne.symm h_not_zero)
  · intro h_pos h_eq
    have h_zero := hmf_bare_implies_zero_MI sys h_eq
    linarith


/-- **COROLLARY**: The subdivision potential vanishes iff I(A:B) = 0.

    ε = 0 ↔ I = 0. The entropic cost is zero iff there's nothing
    to pay for. -/
theorem subdivision_zero_iff
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cut : AlgebraicCut) :
    subdivisionPotential T N cut = 0 ↔ mutualInformation cut = 0 := by
  constructor
  · intro h
    -- T * I / N = 0 with T > 0, N > 0 → I = 0
    have hI := mutual_information_nonneg cut
    by_contra h_ne
    have hI_pos : mutualInformation cut > 0 := lt_of_le_of_ne hI (Ne.symm h_ne)
    have : subdivisionPotential T N cut > 0 :=
      subdivision_potential_pos_of_correlated T hT N hN cut hI_pos
    linarith
  · intro h
    unfold subdivisionPotential
    rw [h]; simp

end NanoThermodynamics.Bijection
