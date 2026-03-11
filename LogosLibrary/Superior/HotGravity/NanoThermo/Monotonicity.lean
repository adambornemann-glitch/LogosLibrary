/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: NanoThermo/Monotonicity.lean
-/
import LogosLibrary.Superior.HotGravity.NanoThermo.Definition
/-!
=====================================================================
## Monotonicity and the Data Processing Inequality
=====================================================================

More correlation → bigger cost. Coarser descriptions → less correlation.

These are the ordering theorems. They tell you:

1. **Monotonicity in I**: More mutual info across the cut means
   larger subdivision potential. A ranking on cuts.

2. **Monotonicity in T**: Hotter systems pay more per correlation.
   The modular parameter amplifies the entropic cost.

3. **Anti-monotonicity in N**: More particles dilute the per-particle
   cost. (Already proved as thermodynamic limit, but the pointwise
   version is useful.)

4. **Data Processing Inequality**: Coarse-graining (forgetting details)
   can only DECREASE mutual information. You cannot create
   correlations by throwing away information.

   This is the arrow of ignorance. It points one way.

5. **Coarse-graining decreases the subdivision potential**: Immediate
   consequence of DPI + monotonicity. Forgetting structure makes
   the subsystem look MORE independent — never less.
-/
namespace NanoThermodynamics.Monotonicity
open NanoThermodynamics.Definition
open MinkowskiSpace
open ThermalTime Basic
/-!
### Monotonicity in Mutual Information
-/

/-- **THEOREM**: Subdivision potential is monotone in mutual information.

    If cut₁ has more mutual information than cut₂ (same T, N),
    then ε₁ ≥ ε₂.

    More correlation across the cut → larger entropic cost.
    A total ordering on the "strength" of the coupling. -/
theorem subdivision_monotone_in_MI
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cut₁ cut₂ : AlgebraicCut)
    (h : mutualInformation cut₁ ≥ mutualInformation cut₂) :
    subdivisionPotential T N cut₁ ≥ subdivisionPotential T N cut₂ := by
  unfold subdivisionPotential
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (le_of_lt hT)) (le_of_lt hN)


/-- **THEOREM**: Strict monotonicity — strictly more correlation
    means strictly larger cost. -/
theorem subdivision_strict_monotone_in_MI
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cut₁ cut₂ : AlgebraicCut)
    (h : mutualInformation cut₁ > mutualInformation cut₂) :
    subdivisionPotential T N cut₁ > subdivisionPotential T N cut₂ := by
  unfold subdivisionPotential
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h hT) hN


/-!
### Monotonicity in Temperature
-/

/-- **THEOREM**: Subdivision potential is monotone in temperature.

    Hotter systems pay more per correlation. The modular parameter
    amplifies the cost.

    ε(T₁) ≥ ε(T₂) when T₁ ≥ T₂ > 0, for the same cut and N.

    Physical meaning: at higher temperatures, the same mutual
    information across the cut corresponds to more energy. -/
theorem subdivision_monotone_in_T
    (T₁ T₂ : ℝ) (_hT₁ : T₁ > 0) (_hT₂ : T₂ > 0) (hT : T₁ ≥ T₂)
    (N : ℝ) (hN : N > 0) (cut : AlgebraicCut) :
    subdivisionPotential T₁ N cut ≥ subdivisionPotential T₂ N cut := by
  unfold subdivisionPotential
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hT (mutual_information_nonneg cut)) (le_of_lt hN)


/-!
### Anti-Monotonicity in N (Pointwise)
-/

/-- **THEOREM**: Subdivision potential is anti-monotone in N.

    More particles → smaller per-particle cost.

    ε(N₁) ≤ ε(N₂) when N₁ ≥ N₂ > 0, for the same cut and T.

    This is the pointwise version of the thermodynamic limit:
    classical thermo gets better as N increases. -/
theorem subdivision_anti_monotone_in_N
    (T : ℝ) (hT : T > 0)
    (N₁ N₂ : ℝ) (_hN₁ : N₁ > 0) (hN₂ : N₂ > 0) (hN : N₁ ≥ N₂)
    (cut : AlgebraicCut) :
    subdivisionPotential T N₁ cut ≤ subdivisionPotential T N₂ cut := by
  unfold subdivisionPotential
  apply div_le_div₀ ?_ ?_ hN₂ hN
  · exact mul_nonneg (le_of_lt hT) (mutual_information_nonneg cut)
  · exact Preorder.le_refl (T * mutualInformation cut)


/-!
### The Data Processing Inequality
=====================================================================

The DPI is one of the deepest facts in quantum information theory:

  If Φ is a quantum channel (CPTP map), then
  I(A:B) ≥ I(Φ(A):B)

Coarse-graining — forgetting details, tracing out substructure,
applying a noisy channel — can only DECREASE mutual information.

You cannot create correlations by throwing away information.

This is an axiom in our formalization because we don't have the
full quantum information theory machinery (Stinespring dilation,
strong subadditivity, etc.) in the library. But the CONSEQUENCES
are provable from the axiom.

Physically, the DPI says: if you describe a system more coarsely
(choose a smaller subalgebra M_A' ⊂ M_A ⊂ M), you see less
correlation with the complement. The modular structure looks
simpler — but only because you've thrown away the ability to
see its complexity.
-/

/-- A **coarse-graining** is a pair of cuts where one refines the other.

    The coarser cut (cut_coarse) has less or equal mutual information
    than the finer cut (cut_fine). This is the DPI. -/
structure CoarseGraining where
  /-- The finer (more detailed) algebraic cut -/
  cut_fine : AlgebraicCut
  /-- The coarser (less detailed) algebraic cut -/
  cut_coarse : AlgebraicCut
  /-- **Data Processing Inequality**: coarse-graining cannot
      increase mutual information.

      This is the fundamental axiom of information processing:
      you can't create correlations by forgetting. -/
  h_dpi : mutualInformation cut_coarse ≤ mutualInformation cut_fine

/-- **THEOREM**: Coarse-graining decreases the subdivision potential.

    If you describe the system more coarsely, the subdivision
    potential can only decrease (or stay the same).

    The subsystem looks MORE independent — never less.

    Proof: monotonicity of ε in I, plus the DPI.

    Physical meaning: if you zoom out, the "anomalies" get smaller.
    This is why bulk thermodynamics works — it's the maximally
    coarse-grained description. -/
theorem coarse_graining_decreases_subdivision
    (T : ℝ) (hT : T > 0) (N : ℝ) (hN : N > 0)
    (cg : CoarseGraining) :
    subdivisionPotential T N cg.cut_coarse ≤
    subdivisionPotential T N cg.cut_fine :=
  subdivision_monotone_in_MI T hT N hN cg.cut_fine cg.cut_coarse cg.h_dpi


/-- **THEOREM**: Coarse-graining moves H* closer to H_bare.

    For two nano-systems with the same bare Hamiltonian, T, and N,
    but where one is a coarse-graining of the other:

    |H*_coarse - H_bare| ≤ |H*_fine - H_bare|

    Forgetting details makes the effective Hamiltonian closer
    to the bare one. The "anomalies" shrink. -/
theorem coarse_graining_reduces_anomaly
    (sys_fine sys_coarse : NanoSystem)
    (_h_same_bare : sys_fine.H_bare = sys_coarse.H_bare)
    (h_same_T : sys_fine.T = sys_coarse.T)
    (h_same_N : sys_fine.N = sys_coarse.N)
    (cg : CoarseGraining)
    (h_fine : sys_fine.cut = cg.cut_fine)
    (h_coarse : sys_coarse.cut = cg.cut_coarse) :
    sys_coarse.H_star - sys_coarse.H_bare ≤
    sys_fine.H_star - sys_fine.H_bare := by
  rw [sys_fine.h_subdivision, sys_coarse.h_subdivision]
  unfold subdivisionPotential
  rw [h_fine, h_coarse, h_same_T, h_same_N]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left cg.h_dpi (le_of_lt (h_same_T ▸ sys_coarse.hT)))
    (le_of_lt (h_same_N ▸ sys_coarse.hN))


/-!
### Combining Monotonicity: The Complete Ordering
-/

/-- **THEOREM**: The subdivision potential is jointly monotone.

    Increasing T, increasing I, or decreasing N all make ε larger.
    Conversely: cooling, decorrelating, or adding particles all
    make ε smaller.

    This is the complete parameter-space picture:

      ε(T, I, N) = T · I / N

    is increasing in T (for fixed I, N),
    increasing in I (for fixed T, N), and
    decreasing in N (for fixed T, I).

    Every nano-thermodynamic experiment lives somewhere in this
    3D parameter space. The "anomalies" are large in the corner
    where T is high, I is large, and N is small.

    Bulk classical thermo is the opposite corner:
    I → 0 (or N → ∞). Same physics. Different regime. -/
theorem subdivision_joint_bound
    (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (N₁ N₂ : ℝ) (hN₁ : N₁ > 0) (hN₂ : N₂ > 0)
    (cut₁ cut₂ : AlgebraicCut)
    (h_T : T₁ ≥ T₂)
    (h_I : mutualInformation cut₁ ≥ mutualInformation cut₂)
    (h_N : N₂ ≥ N₁) :
    subdivisionPotential T₁ N₁ cut₁ ≥ subdivisionPotential T₂ N₂ cut₂ := by
  calc subdivisionPotential T₁ N₁ cut₁
      ≥ subdivisionPotential T₂ N₁ cut₁ :=
        subdivision_monotone_in_T T₁ T₂ hT₁ hT₂ h_T N₁ hN₁ cut₁
    _ ≥ subdivisionPotential T₂ N₁ cut₂ :=
        subdivision_monotone_in_MI T₂ hT₂ N₁ hN₁ cut₁ cut₂ h_I
    _ ≥ subdivisionPotential T₂ N₂ cut₂ :=
        subdivision_anti_monotone_in_N T₂ hT₂ N₂ N₁ hN₂ hN₁ h_N cut₂

end NanoThermodynamics.Monotonicity
/-!
### Physical Summary

The ordering theorems complete the quantitative picture:

**Monotonicity tells you WHERE anomalies live:**
- High T, large I, small N → big anomalies → nanothermodynamics
- Low T, small I, large N → small anomalies → classical thermo

**The DPI tells you WHY coarse-graining works:**
- Zooming out (larger subalgebra) → less mutual info → smaller ε
- Classical thermo is the maximally coarse-grained limit
- The anomalies are real — you just can't see them when you squint

**The joint bound tells you the SHAPE of the parameter space:**
- ε is monotone in each variable separately
- The three monotonicity directions are independent
- The "classical limit" can be reached by ANY of three routes:
  T → 0, I → 0, or N → ∞

**Connection to experiments:**
- Nanocluster heat capacity anomaly: high I, small N → big ε ✓
- Thermophoresis in colloids: spatially varying I → force ✓
- Bulk matter: N ~ 10²³ → ε ~ 0 → classical thermo ✓
- Molecular motors: moderate N, large I → measurable ε ✓
-/
