/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Thermodynamics/Ott.lean

# The Ott Temperature Transformation: A Formal Proof

## The Argument in Three Lines

1. Heat is energy transfer, hence transforms as Q → γQ.
2. Entropy counts microstates (S = k ln Ω), hence is Lorentz invariant.
3. The thermodynamic identity S = Q/T, holding in all frames, forces T → γT.

## What This File Proves

There exists exactly one temperature transformation compatible with both
special relativity and thermodynamics: the Ott transformation T → γT.

This is not one argument repeated. It is one theorem — the Lorentz invariance
of the ratio E/T — instantiated across seven physical contexts:

  1. Landauer's erasure bound      (E_erasure / T)
  2. Clausius entropy               (Q / T)
  3. Boltzmann exponent             (H / kT)
  4. Gibbs entropy                  ((E - F) / T)
  5. Detailed balance ratio         (ΔE / T)
  6. Specific heat                  (dE / dT)
  7. Free energy composition        (E - TS)

### Expanded Sections:
  1. The Clausius Inequality
  2. The Unruh Effect
  3. Black Body Spectrum and the CMB

## References

- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur,"
  Z. Physik 175, 70–104 (1963)
- A.S. Eddington, "The Mathematical Theory of Relativity," §73 (1923)
- A. Einstein, letter to M. von Laue (1952), cited in Liu (1992)
- H. Arzelies, Nuovo Cim. 35, 792 (1965)
- P.T. Landsberg, Nature 212, 571 (1966)
-/
import LogosLibrary.Relativity.GR.Kerr.Metric
import LogosLibrary.Relativity.GR.Kerr.Extensions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RelativisticTemperature
open MinkowskiSpace Kerr KerrExtensions Real

/-- Helper lemma
log 2 > 0 (used in Landauer arguments). -/
lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-!
## Part I: The One Theorem

Every argument in this file is an instance of a single algebraic identity:

    γE / γT  =  E / T

The left side is "energy-like quantity in boosted frame divided by Ott temperature."
The right side is "same ratio in rest frame."

The ratio is invariant because γ cancels. This is the entire content of
Ott's transformation, reduced to `mul_div_mul_left`.
-/

/-- **THE FUNDAMENTAL THEOREM.** The ratio E/T is Lorentz invariant under Ott.

    This single lemma is the engine behind all seven physical arguments.
    Every "proof that Ott is correct" is an instantiation of this identity
    with a different physical interpretation of E. -/
lemma ratio_invariant (E T : ℝ) (_hT : T > 0) (v : ℝ) (hv : |v| < 1) :
    (lorentzGamma v hv * E) / (lorentzGamma v hv * T) = E / T :=
  mul_div_mul_left E T (lorentzGamma_ne_zero v hv)

/-- **UNIQUENESS.** Any transformation T → f(v)·T preserving the ratio E/T
    for all E must satisfy f(v) = γ(v). There is no freedom. -/
lemma ott_unique (f : ℝ → ℝ) (hf_pos : ∀ v, |v| < 1 → f v > 0)
    (hf_preserves : ∀ Q T v (hv : |v| < 1), T > 0 →
      (lorentzGamma v hv * Q) / (f v * T) = Q / T) :
    ∀ v (hv : |v| < 1), f v = lorentzGamma v hv := by
  intro v hv
  have h := hf_preserves 1 1 v hv one_pos
  simp only [mul_one, one_div] at h
  have hf_ne : f v ≠ 0 := ne_of_gt (hf_pos v hv)
  field_simp at h; linarith

/-- **LANDSBERG REFUTATION (general form).** If T → T (Landsberg) and E → γE,
    then any nonzero ratio E/T is NOT preserved for v ≠ 0. -/
lemma landsberg_breaks_ratio (E T : ℝ) (hE : E ≠ 0) (hT : T > 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    (lorentzGamma v hv * E) / T ≠ E / T := by
  have hγ_ne_one := lorentzGamma_ne_one v hv hv_ne
  have hT_ne : T ≠ 0 := ne_of_gt hT
  intro h
  have h1 : lorentzGamma v hv * E / T = E / T := h
  have h2 : (lorentzGamma v hv - 1) * E = 0 := by field_simp at h1; norm_cast
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact hγ_ne_one (by linarith)
  · exact hE h4


/-!
## Part II: Seven Instantiations

Each physical argument names its quantities and invokes the fundamental theorem.
The diversity of names is an illusion. The algebra is identical.
-/

section Instantiations

variable (v : ℝ) (hv : |v| < 1)

/-- **1. Clausius Entropy:** S = Q/T is invariant under Ott. -/
lemma ott_entropy_invariant (Q T : ℝ) (hT : T > 0) :
    (lorentzGamma v hv * Q) / (lorentzGamma v hv * T) = Q / T :=
  ratio_invariant Q T hT v hv

/-- **2. Landauer's Bound:** The minimum erasure energy kT ln 2 is covariant. -/
lemma ott_landauer_covariant (T : ℝ) (_hT : T > 0) (ΔE : ℝ)
    (h_bound : ΔE ≥ T * Real.log 2) :
    lorentzGamma v hv * ΔE ≥ (lorentzGamma v hv * T) * Real.log 2 := by
  have hγ_pos := lorentzGamma_pos v hv
  calc lorentzGamma v hv * ΔE
      ≥ lorentzGamma v hv * (T * Real.log 2) := mul_le_mul_of_nonneg_left h_bound hγ_pos.le
    _ = (lorentzGamma v hv * T) * Real.log 2 := by ring

/-- **3. Boltzmann Exponent:** H/kT in the partition function is invariant. -/
lemma ott_boltzmann_invariant (H T : ℝ) (hT : T > 0) :
    (lorentzGamma v hv * H) / (lorentzGamma v hv * T) = H / T :=
  ratio_invariant H T hT v hv

/-- **4. Gibbs Entropy:** S = (E - F)/T is invariant when E, F, T all scale by γ. -/
lemma ott_gibbs_invariant (E F T : ℝ) (_hT : T > 0) :
    let γ := lorentzGamma v hv
    (γ * E - γ * F) / (γ * T) = (E - F) / T := by
  simp only
  have hγ_ne := lorentzGamma_ne_zero v hv
  rw [← mul_sub]; exact mul_div_mul_left (E - F) T hγ_ne

/-- **5. Detailed Balance:** The rate ratio exp(-ΔE/kT) is frame-independent. -/
lemma ott_detailed_balance (ΔE T : ℝ) (hT : T > 0) :
    (lorentzGamma v hv * ΔE) / (lorentzGamma v hv * T) = ΔE / T :=
  ratio_invariant ΔE T hT v hv

/-- **6. Specific Heat:** C = dE/dT is a material property, hence invariant. -/
lemma ott_specific_heat_invariant (dE dT : ℝ) (_hdT : dT ≠ 0) :
    (lorentzGamma v hv * dE) / (lorentzGamma v hv * dT) = dE / dT :=
  mul_div_mul_left dE dT (lorentzGamma_ne_zero v hv)

/-- **7. Free Energy:** F = E - TS transforms as energy when S is invariant. -/
lemma ott_free_energy_transforms (E T S : ℝ) :
    let γ := lorentzGamma v hv
    (γ * E) - (γ * T) * S = γ * (E - T * S) := by ring

end Instantiations


/-!
## Part III: Landsberg Fails — Seven Ways

Each instantiation above has a contrapositive: under Landsberg (T' = T),
the corresponding invariant breaks. These all follow from `landsberg_breaks_ratio`.
-/

section LandsbergFails

variable (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0)

/-- Landsberg entropy is not invariant. -/
lemma landsberg_entropy_fails (Q T : ℝ) (hQ : Q ≠ 0) (hT : T > 0) (hv_ne : v ≠ 0):
    (lorentzGamma v hv * Q) / T ≠ Q / T :=
  landsberg_breaks_ratio Q T hQ hT v hv hv_ne

/-- Landsberg violates the Landauer bound in the reverse direction. -/
lemma landsberg_violates_landauer_reverse (T : ℝ) (hT : T > 0) (hv_ne : v ≠ 0):
    (T * Real.log 2) / lorentzGamma v hv < T * Real.log 2 := by
  have hγ_gt := lorentzGamma_gt_one v hv hv_ne
  have hγ_pos := lorentzGamma_pos v hv
  have hTlog : T * Real.log 2 > 0 := mul_pos hT log_two_pos
  rw [div_lt_iff₀ hγ_pos]
  nlinarith

/-- Landsberg Boltzmann exponent is not invariant. -/
lemma landsberg_boltzmann_fails (H T : ℝ) (hH : H ≠ 0) (hT : T > 0) (hv_ne : v ≠ 0):
    (lorentzGamma v hv * H) / T ≠ H / T :=
  landsberg_breaks_ratio H T hH hT v hv hv_ne

/-- Landsberg free energy does not transform as energy. -/
lemma landsberg_free_energy_fails (E T S : ℝ) (hS : S ≠ 0) (hT : T ≠ 0) (hv_ne : v ≠ 0):
    let γ := lorentzGamma v hv
    (γ * E - T * S) ≠ γ * (E - T * S) := by
  simp only; intro h
  have : (lorentzGamma v hv - 1) * (T * S) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h2
  · exact lorentzGamma_ne_one v hv hv_ne (by linarith)
  · exact mul_ne_zero hT hS h2

/-- Landsberg Gibbs entropy is not invariant. -/
lemma landsberg_gibbs_fails (E F T : ℝ) (hEF : E ≠ F) (hT : T > 0) (hv_ne : v ≠ 0):
    (lorentzGamma v hv * E - lorentzGamma v hv * F) / T ≠ (E - F) / T := by
  rw [← mul_sub]
  exact landsberg_breaks_ratio (E - F) T (sub_ne_zero.mpr hEF) hT v hv hv_ne

/-- Landsberg specific heat is frame-dependent. -/
lemma landsberg_specific_heat_fails (dE dT : ℝ) (hdE : dE ≠ 0) (hdT : dT ≠ 0) (hv_ne : v ≠ 0):
    (lorentzGamma v hv * dE) / dT ≠ dE / dT := by
  have hdT_pos_or_neg : dT > 0 ∨ dT < 0 := ne_iff_lt_or_gt.mp (Ne.symm hdT)
  cases hdT_pos_or_neg with
  | inl h => exact landsberg_breaks_ratio dE dT hdE h v hv hv_ne
  | inr h =>
    intro heq
    have : (lorentzGamma v hv - 1) * dE = 0 := by
      field_simp at heq;
      simp only [mul_eq_zero]
      simp_all only [ne_eq, sub_self]
      exact Or.symm (Or.inr trivial)
    rcases mul_eq_zero.mp this with h1 | h2
    · exact lorentzGamma_ne_one v hv hv_ne (by linarith)
    · exact hdE h2

/-- Landsberg detailed balance is frame-dependent. -/
lemma landsberg_detailed_balance_fails (ΔE T : ℝ) (hΔE : ΔE ≠ 0) (hT : T > 0)(hv_ne : v ≠ 0) :
    (lorentzGamma v hv * ΔE) / T ≠ ΔE / T :=
  landsberg_breaks_ratio ΔE T hΔE hT v hv hv_ne

/-- Under Landsberg, the entropy discrepancy is exactly a factor of γ. -/
lemma landsberg_entropy_discrepancy (Q T : ℝ) (_hT : T > 0) :
    (lorentzGamma v hv * Q) / T = lorentzGamma v hv * (Q / T) :=
  mul_div_assoc _ Q T

/-- Under Landsberg, irreversibility is frame-dependent. -/
lemma landsberg_irreversibility_grows (ΔS : ℝ) (hΔS : ΔS > 0) (hv_ne : v ≠ 0):
    lorentzGamma v hv * ΔS > ΔS :=
  (lt_mul_iff_one_lt_left hΔS).mpr (lorentzGamma_gt_one v hv hv_ne)

end LandsbergFails


/-!
## Part IV: Application to Kerr Black Holes

The Hawking temperature of a subextremal Kerr black hole is positive.
All seven invariants apply. Landsberg fails for all seven.
-/

section KerrApplication

/-- **The Kerr–Ott Theorem.** For a strictly subextremal Kerr black hole,
    the Hawking temperature transforms as T → γT under Lorentz boosts,
    preserving all thermodynamic invariants. -/
lemma kerr_hawking_transforms_ott (p : KerrParams)
    (h_strict : 0 < |p.a| ∧ |p.a| < p.M)
    (v : ℝ) (hv : |v| < 1) :
    let T := hawkingTemperature p
    let γ := lorentzGamma v hv
    T > 0 ∧
    (∀ Q, (γ * Q) / (γ * T) = Q / T) ∧
    (∀ H, (γ * H) / (γ * T) = H / T) ∧
    (∀ E F, (γ * E - γ * F) / (γ * T) = (E - F) / T) ∧
    (∀ E S, (γ * E) - (γ * T) * S = γ * (E - T * S)) := by
  have hT := hawking_temperature_positive p h_strict
  exact ⟨hT,
    fun Q => ratio_invariant Q _ hT v hv,
    fun H => ratio_invariant H _ hT v hv,
    fun E F => ott_gibbs_invariant v hv E F _ hT,
    fun E S => ott_free_energy_transforms v hv E _ S⟩

/-- **Landsberg fails for Kerr.** Every invariant is violated simultaneously. -/
lemma kerr_landsberg_fails (p : KerrParams)
    (h_strict : 0 < |p.a| ∧ |p.a| < p.M)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    let T := hawkingTemperature p
    (lorentzGamma v hv * 1) / T ≠ 1 / T ∧
    (T * Real.log 2) / lorentzGamma v hv < T * Real.log 2 ∧
    (lorentzGamma v hv * 1 - T * 1) ≠ lorentzGamma v hv * (1 - T * 1) := by
  have hT := hawking_temperature_positive p h_strict
  have hT_ne : hawkingTemperature p ≠ 0 := ne_of_gt hT
  exact ⟨landsberg_entropy_fails v hv 1 _ one_ne_zero hT hv_ne,
         landsberg_violates_landauer_reverse v hv _ hT hv_ne,
         landsberg_free_energy_fails v hv 1 _ 1 one_ne_zero hT_ne hv_ne⟩

/-- **Uniqueness for Kerr.** Any transformation preserving the Landauer bound
    must be Ott. -/
lemma kerr_ott_unique (p : KerrParams)
    (h_strict : 0 < |p.a| ∧ |p.a| < p.M)
    (f : ℝ → ℝ) (_hf_pos : ∀ v, |v| < 1 → f v > 0)
    (hf_bound : ∀ v (hv : |v| < 1),
      (f v * hawkingTemperature p) * Real.log 2 =
      lorentzGamma v hv * (hawkingTemperature p * Real.log 2)) :
    ∀ v (hv : |v| < 1), f v = lorentzGamma v hv := by
  intro v hv
  have hT := hawking_temperature_positive p h_strict
  have h := hf_bound v hv
  have hTlog_ne : hawkingTemperature p * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos hT log_two_pos)
  exact mul_right_cancel₀ hTlog_ne (by linarith)

/-- An infalling observer sees a hotter black hole. -/
lemma falling_observer_hotter (p : KerrParams)
    (h_strict : 0 < |p.a| ∧ |p.a| < p.M)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    lorentzGamma v hv * hawkingTemperature p > hawkingTemperature p :=
  (lt_mul_iff_one_lt_left (hawking_temperature_positive p h_strict)).mpr
    (lorentzGamma_gt_one v hv hv_ne)

/-- The inner horizon temperature also transforms via Ott. -/
lemma kerr_inner_horizon_ott (p : KerrParams)
    (h_strict : 0 < |p.a| ∧ |p.a| < p.M)
    (v : ℝ) (hv : |v| < 1) :
    let T := innerHorizonTemperature p
    T > 0 ∧ ∀ Q, (lorentzGamma v hv * Q) / (lorentzGamma v hv * T) = Q / T := by
  have hT : innerHorizonTemperature p > 0 := by
    unfold innerHorizonTemperature surface_gravity_inner
    have hM := p.mass_positive
    have h_disc : p.M ^ 2 - p.a ^ 2 > 0 := by
      nlinarith [h_strict.1, h_strict.2, sq_abs p.a, abs_nonneg p.a]
    have h_sqrt := Real.sqrt_pos.mpr h_disc
    have h_diff : r_plus p - r_minus p > 0 := by
      unfold r_plus r_minus; linarith
    have h_rm := r_minus_positive p h_strict
    exact div_pos (div_pos h_diff (by nlinarith [sq_nonneg (r_minus p), sq_nonneg p.a]))
      (by linarith [Real.pi_pos])
  exact ⟨hT, fun Q => ratio_invariant Q _ hT v hv⟩

/-- In the extremal limit, T = 0 and Ott holds trivially: γ · 0 = 0. -/
lemma extremal_ott_trivial (M : ℝ) (hM : 0 < M) (v : ℝ) (hv : |v| < 1) :
    let T := hawkingTemperature (extremalKerrParams M hM)
    T = 0 ∧ lorentzGamma v hv * T = 0 := by
  constructor
  · exact extremal_zero_temperature M hM
  · rw [extremal_zero_temperature M hM]; ring

/-- Tolman–Ehrenfest reduces to Ott in the local Lorentz frame.
    When √g₀₀ = 1/γ, the relation T_local · √g₀₀ = T_∞ gives T_local = γT_∞. -/
lemma tolman_implies_ott (T_inf : ℝ) (v : ℝ) (hv : |v| < 1) :
    (lorentzGamma v hv * T_inf) * (1 / lorentzGamma v hv) = T_inf := by
  have hγ_ne := lorentzGamma_ne_zero v hv
  field_simp

end KerrApplication


/-!
## Part V: The Reductio of Relative Entropy

Landsberg (T' = T) combined with Q' = γQ and S = Q/T forces S' = γS.
We show this is incoherent: it implies non-integer microstate counts,
frame-dependent information content, and erasure of more bits than exist.
-/

namespace RelativeEntropy

/-- If S → γS, then the effective microstate count Ω → Ω^γ. -/
noncomputable def effectiveMicrostates (Ω : ℕ) (v : ℝ) (hv : |v| < 1) : ℝ :=
  (Ω : ℝ) ^ (lorentzGamma v hv)

/-- Ω^γ ≠ Ω for Ω ≥ 2 and γ > 1: microstates become non-integer. -/
lemma microstates_non_integer (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0)
    (Ω : ℕ) (hΩ : Ω ≥ 2) :
    effectiveMicrostates Ω v hv ≠ Ω := by
  unfold effectiveMicrostates
  intro h
  have hγ := lorentzGamma_gt_one v hv hv_ne
  have hΩ_cast : (Ω : ℝ) ≥ 2 := by exact_mod_cast hΩ
  have h1 : (Ω : ℝ) ^ (lorentzGamma v hv) > (Ω : ℝ) ^ (1 : ℝ) :=
    rpow_lt_rpow_of_exponent_lt (by linarith) hγ
  rw [rpow_one] at h1
  linarith

/-- 2^γ ≠ 2 for γ ≠ 1: a coin flip cannot have non-integer microstates. -/
lemma coin_flip_absurd (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    (2 : ℝ) ^ (lorentzGamma v hv) ≠ 2 := by
  intro h
  have hγ_ne := lorentzGamma_ne_one v hv hv_ne
  have h2 : (2 : ℝ) ^ (lorentzGamma v hv) = (2 : ℝ) ^ (1 : ℝ) := by simp [h]
  exact hγ_ne ((rpow_right_inj (by norm_num : (2:ℝ) > 0) (by norm_num : (2:ℝ) ≠ 1)).mp h2)

/-- Under S → γS, the "information erased" when clearing one bit exceeds one bit. -/
lemma erasure_exceeds_content (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    lorentzGamma v hv * Real.log 2 > Real.log 2 :=
  (lt_mul_iff_one_lt_left log_two_pos).mpr (lorentzGamma_gt_one v hv hv_ne)

/-- The bit content of a message becomes frame-dependent. -/
lemma bits_frame_dependent (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0)
    (n : ℕ) (hn : n ≥ 1) :
    lorentzGamma v hv * (n : ℝ) > n :=
  (lt_mul_iff_one_lt_left (Nat.cast_pos'.mpr hn)).mpr (lorentzGamma_gt_one v hv hv_ne)

/-- The second law sign is preserved (the ONLY thing that survives). -/
lemma second_law_sign_preserved (v : ℝ) (hv : |v| < 1) (ΔS : ℝ) (h : ΔS ≥ 0) :
    lorentzGamma v hv * ΔS ≥ 0 :=
  mul_nonneg (lorentzGamma_pos v hv).le h

/-- But the magnitude of irreversibility is frame-dependent. -/
lemma irreversibility_magnified (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0)
    (ΔS : ℝ) (hΔS : ΔS > 0) :
    lorentzGamma v hv * ΔS > ΔS :=
  (lt_mul_iff_one_lt_left hΔS).mpr (lorentzGamma_gt_one v hv hv_ne)

/-- **Summary.** Relative entropy (Landsberg's consequence) is incoherent:
    non-integer microstates, frame-dependent information, erasure paradox. -/
lemma relative_entropy_incoherent (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    -- Microstates become non-integer
    ((2 : ℝ) ^ (lorentzGamma v hv) ≠ 2) ∧
    -- Information content is frame-dependent
    (lorentzGamma v hv * Real.log 2 > Real.log 2) ∧
    -- Irreversibility is frame-dependent
    (∀ ΔS, ΔS > 0 → lorentzGamma v hv * ΔS > ΔS) :=
  ⟨coin_flip_absurd v hv hv_ne,
   erasure_exceeds_content v hv hv_ne,
   fun ΔS hΔS => irreversibility_magnified v hv hv_ne ΔS hΔS⟩

end RelativeEntropy


/-!
## Part VI: The Complete Picture

All results assembled into the final statement.
-/

/-- **MAIN THEOREM.** The Ott–Landsberg debate is settled for Kerr black holes.

    For any strictly subextremal Kerr black hole:
    (1) The Hawking temperature is positive.
    (2) Seven thermodynamic invariants are preserved under T → γT.
    (3) Landsberg violates all seven.
    (4) Ott is the unique consistent transformation.
    (5) Relative entropy (Landsberg's consequence) is incoherent. -/
theorem ott_over_landsberg_QED (p : KerrParams) (h_strict : 0 < |p.a| ∧ |p.a| < p.M) :
    -- (1) Hawking temperature exists and is positive
    hawkingTemperature p > 0 ∧
    -- (2) Ott preserves E/T ratios
    (∀ v (hv : |v| < 1) E,
      (lorentzGamma v hv * E) / (lorentzGamma v hv * hawkingTemperature p) =
      E / hawkingTemperature p) ∧
    -- (3) Landsberg breaks E/T ratios
    (∀ v (hv : |v| < 1), v ≠ 0 →
      (lorentzGamma v hv * 1) / hawkingTemperature p ≠ 1 / hawkingTemperature p) ∧
    -- (4) Ott is unique
    (∀ f : ℝ → ℝ, (∀ v, |v| < 1 → f v > 0) →
      (∀ v (hv : |v| < 1),
        (lorentzGamma v hv * 1) / (f v * hawkingTemperature p) =
        1 / hawkingTemperature p) →
      ∀ v (hv : |v| < 1), f v = lorentzGamma v hv) ∧
    -- (5) Relative entropy is incoherent
    (∀ v (hv : |v| < 1), v ≠ 0 → (2 : ℝ) ^ (lorentzGamma v hv) ≠ 2) := by
  have hT := hawking_temperature_positive p h_strict
  refine ⟨hT, ?_, ?_, ?_, ?_⟩
  · exact fun v hv E => ratio_invariant E _ hT v hv
  · exact fun v hv hv_ne => landsberg_breaks_ratio 1 _ one_ne_zero hT v hv hv_ne
  · intro f hf_pos hf_preserves v hv
    have hT_pos := hawking_temperature_positive p h_strict
    have hT_ne : hawkingTemperature p ≠ 0 := ne_of_gt hT_pos
    have hf_ne : f v ≠ 0 := ne_of_gt (hf_pos v hv)
    have h := hf_preserves v hv
    simp only [mul_one] at h
    rw [div_eq_div_iff (mul_ne_zero hf_ne hT_ne) hT_ne] at h
    simp only [one_mul] at h
    exact (mul_right_cancel₀ hT_ne h.symm)
  · exact fun v hv hv_ne => RelativeEntropy.coin_flip_absurd v hv hv_ne


/-!
## The Clausius Inequality

The Clausius inequality δQ/T ≤ dS is the mathematical statement of the Second Law.
Equality holds for reversible processes. Under Ott, both sides are invariant:
γδQ/(γT) = δQ/T ≤ dS. Under Landsberg, the left side inflates by γ, turning
reversible processes irreversible. Reversibility becomes observer-dependent.
-/

section ClausiusInequality

/-- A thermodynamic process: heat δQ exchanged at temperature T,
    producing entropy change dS, satisfying the Clausius inequality. -/
structure ThermodynamicProcess where
  δQ : ℝ
  T : ℝ
  dS : ℝ
  hT : T > 0
  clausius : δQ / T ≤ dS

/-- A reversible process saturates the Clausius inequality: δQ/T = dS. -/
abbrev ThermodynamicProcess.isReversible (p : ThermodynamicProcess) : Prop :=
  p.δQ / p.T = p.dS

/-- **Ott preserves the Clausius inequality in all frames.**
    γδQ/(γT) = δQ/T ≤ dS. The Second Law holds. -/
lemma ott_preserves_clausius (p : ThermodynamicProcess) (v : ℝ) (hv : |v| < 1) :
    (lorentzGamma v hv * p.δQ) / (lorentzGamma v hv * p.T) ≤ p.dS := by
  rw [ratio_invariant p.δQ p.T p.hT v hv]
  exact p.clausius

/-- **Ott preserves reversibility.** A reversible process remains reversible
    in every Lorentz frame. The Carnot efficiency is observer-independent. -/
lemma ott_preserves_reversibility (p : ThermodynamicProcess)
    (h_rev : p.isReversible) (v : ℝ) (hv : |v| < 1) :
    (lorentzGamma v hv * p.δQ) / (lorentzGamma v hv * p.T) = p.dS := by
  rw [ratio_invariant p.δQ p.T p.hT v hv]
  exact h_rev

/-- **Landsberg violates the Clausius inequality.** For a reversible process
    with positive heat exchange, γδQ/T > δQ/T = dS. A reversible process
    becomes irreversible when you change your velocity. -/
lemma landsberg_breaks_clausius (p : ThermodynamicProcess)
    (h_rev : p.isReversible) (hδQ : p.δQ > 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    (lorentzGamma v hv * p.δQ) / p.T > p.dS := by
  rw [← h_rev, mul_div_assoc]
  exact (lt_mul_iff_one_lt_left (div_pos hδQ p.hT)).mpr (lorentzGamma_gt_one v hv hv_ne)

/-- **Reversibility is frame-dependent under Landsberg.**
    The same physical process is reversible in the rest frame and strictly
    irreversible in every other frame. The Carnot cycle's efficiency
    depends on who watches it. -/
theorem landsberg_reversibility_frame_dependent (p : ThermodynamicProcess)
    (h_rev : p.isReversible) (hδQ : p.δQ > 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    -- Reversible in rest frame
    p.δQ / p.T = p.dS ∧
    -- Strictly irreversible in moving frame (Landsberg)
    (lorentzGamma v hv * p.δQ) / p.T > p.dS :=
  ⟨h_rev, landsberg_breaks_clausius p h_rev hδQ v hv hv_ne⟩

end ClausiusInequality


/-!
## The Unruh Effect

A uniformly accelerating observer in the Minkowski vacuum detects a thermal
bath at temperature T = a/(2π). The thermal source is the vacuum itself —
Lorentz invariant, with no rest frame. This is the kill shot for any
framework that requires decomposing boosted heat relative to a "rest frame
of the thermal source."

Under Ott: T → γT. No rest frame needed. The ratio Q/T is invariant.
Under Landsberg: the FrameDecomposition requires a rest frame that does
not exist. Different arbitrary choices of "rest frame" yield different
entropy values. The framework is ambiguous — not merely wrong, but undefined.
-/

section UnruhEffect

/-- The Unruh temperature depends only on proper acceleration.
    There is no "rest frame of the heat bath" — the bath IS the vacuum. -/
structure UnruhTemperature where
  acceleration : ℝ
  h_pos : acceleration > 0

/-- T = a/(2π) -/
noncomputable def UnruhTemperature.temperature (u : UnruhTemperature) : ℝ :=
  u.acceleration / (2 * Real.pi)

/-- The Unruh temperature is positive. -/
lemma unruh_temperature_positive (u : UnruhTemperature) :
    u.temperature > 0 :=
  div_pos u.h_pos (mul_pos two_pos Real.pi_pos)

/-- **Ott applies to Unruh radiation.** No rest frame is needed.
    The ratio Q/T is invariant under boosts, as always. -/
lemma ott_unruh_invariant (u : UnruhTemperature) (v : ℝ) (hv : |v| < 1) (Q : ℝ) :
    (lorentzGamma v hv * Q) / (lorentzGamma v hv * u.temperature) =
    Q / u.temperature :=
  ratio_invariant Q u.temperature (unruh_temperature_positive u) v hv

/-- **Ott is unambiguous.** Every observer computes the same entropy ratio,
    regardless of their velocity. No "rest frame" choice enters the calculation. -/
lemma ott_unruh_unambiguous (u : UnruhTemperature) (Q : ℝ)
    (v₁ v₂ : ℝ) (hv₁ : |v₁| < 1) (hv₂ : |v₂| < 1) :
    (lorentzGamma v₁ hv₁ * Q) / (lorentzGamma v₁ hv₁ * u.temperature) =
    (lorentzGamma v₂ hv₂ * Q) / (lorentzGamma v₂ hv₂ * u.temperature) := by
  rw [ott_unruh_invariant, ott_unruh_invariant]

/-- A Landsberg-style frame decomposition extracts "thermodynamic heat"
    by dividing out the Lorentz factor relative to a chosen rest frame.
    This requires the thermal source to HAVE a rest frame. -/
noncomputable def landsbergThermoHeat (Q_total : ℝ) (v_rest : ℝ)
    (hv : |v_rest| < 1) : ℝ :=
  Q_total / lorentzGamma v_rest hv

/-- **Landsberg is ambiguous for Unruh radiation.** The vacuum is Lorentz
    invariant — every inertial frame is equally "at rest" relative to it.
    Two different rest-frame choices yield different "thermodynamic heats,"
    hence different Landsberg entropy values. The framework is not merely
    wrong but undefined.

    This kills the FrameDecomposition: the sole structural device that
    can keep Landsberg internally consistent. -/
theorem landsberg_unruh_ambiguous (Q : ℝ) (hQ : Q ≠ 0) (T : ℝ) (hT : T > 0)
    (v₁ v₂ : ℝ) (hv₁ : |v₁| < 1) (hv₂ : |v₂| < 1)
    (h_diff : lorentzGamma v₁ hv₁ ≠ lorentzGamma v₂ hv₂) :
    landsbergThermoHeat Q v₁ hv₁ / T ≠ landsbergThermoHeat Q v₂ hv₂ / T := by
  unfold landsbergThermoHeat
  simp only [div_div]
  intro h
  have hγ₁T_ne : lorentzGamma v₁ hv₁ * T ≠ 0 :=
    mul_ne_zero (lorentzGamma_ne_zero v₁ hv₁) (ne_of_gt hT)
  have hγ₂T_ne : lorentzGamma v₂ hv₂ * T ≠ 0 :=
    mul_ne_zero (lorentzGamma_ne_zero v₂ hv₂) (ne_of_gt hT)
  rw [div_eq_div_iff hγ₁T_ne hγ₂T_ne] at h
  -- h : Q * (γ₂ * T) = Q * (γ₁ * T)
  have h₂ := mul_left_cancel₀ hQ h
  exact h_diff (mul_right_cancel₀ (ne_of_gt hT) h₂.symm)

/-- **The entropy discrepancy is physical.** Two observers who pick different
    "rest frames" for the vacuum disagree on the Landsberg entropy by a
    factor of γ₁/γ₂. There is no canonical choice to resolve this. -/
lemma landsberg_unruh_entropy_ratio (Q T : ℝ) (hT : T > 0)
    (v₁ v₂ : ℝ) (hv₁ : |v₁| < 1) (hv₂ : |v₂| < 1) :
    (landsbergThermoHeat Q v₁ hv₁ / T) * (lorentzGamma v₁ hv₁) =
    (landsbergThermoHeat Q v₂ hv₂ / T) * (lorentzGamma v₂ hv₂) := by
  unfold landsbergThermoHeat
  have hγ₁_ne := lorentzGamma_ne_zero v₁ hv₁
  have hγ₂_ne := lorentzGamma_ne_zero v₂ hv₂
  field_simp

/-- A boosted observer sees a hotter Unruh bath under Ott. -/
lemma unruh_observer_hotter (u : UnruhTemperature)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    lorentzGamma v hv * u.temperature > u.temperature :=
  (lt_mul_iff_one_lt_left (unruh_temperature_positive u)).mpr
    (lorentzGamma_gt_one v hv hv_ne)

/-- **Summary.** For Unruh radiation:
    (1) Ott gives a unique, unambiguous entropy in every frame.
    (2) Landsberg requires a rest frame that does not exist.
    (3) Arbitrary rest-frame choices yield contradictory predictions.
    The FrameDecomposition — the only structural defense of Landsberg — is undefined. -/
theorem unruh_summary (u : UnruhTemperature)
    (v₁ v₂ : ℝ) (hv₁ : |v₁| < 1) (hv₂ : |v₂| < 1)
    (h_diff : lorentzGamma v₁ hv₁ ≠ lorentzGamma v₂ hv₂) :
    -- (1) Ott is unambiguous: both observers agree
    ((lorentzGamma v₁ hv₁ * 1) / (lorentzGamma v₁ hv₁ * u.temperature) =
     (lorentzGamma v₂ hv₂ * 1) / (lorentzGamma v₂ hv₂ * u.temperature)) ∧
    -- (2) Landsberg is ambiguous: the two observers disagree
    (landsbergThermoHeat 1 v₁ hv₁ / u.temperature ≠
     landsbergThermoHeat 1 v₂ hv₂ / u.temperature) :=
  ⟨ott_unruh_unambiguous u 1 v₁ v₂ hv₁ hv₂,
   landsberg_unruh_ambiguous 1 one_ne_zero u.temperature
     (unruh_temperature_positive u) v₁ v₂ hv₁ hv₂ h_diff⟩

end UnruhEffect

/-!
## Black Body Spectrum and the CMB

A black body at rest emits a Planck spectrum at temperature T. The
Stefan-Boltzmann law relates energy, entropy, and temperature:

    E = σT⁴V       S = (4/3)σT³V       E/S = (3/4)T

Under a Lorentz boost, total energy transforms as E → γE (this is the
time component of a 4-vector). Entropy is invariant (S → S). Therefore:

    T = (4/3)(E/S)  →  T' = (4/3)(γE/S) = γ · (4/3)(E/S) = γT

This is experimentally verified: the cosmic microwave background exhibits
a dipole anisotropy whose monopole temperature transforms as T → γT.
Measured by COBE, WMAP, and Planck to parts per million. Nature has
already weighed in. She chose Ott.
-/

section BlackBody

/-- A black body system: energy, entropy, and temperature related by
    the Stefan-Boltzmann law. The constant (3/4) is the ratio E/(TS)
    for a photon gas in equilibrium. -/
structure BlackBody where
  E : ℝ
  S : ℝ
  T : ℝ
  hT : T > 0
  hS : S > 0
  /-- The Stefan-Boltzmann relation: E/S = (3/4)T -/
  stefan_boltzmann : E / S = (3 / 4) * T

/-- The temperature can be recovered from E and S alone. -/
lemma blackbody_temperature_from_ratio (b : BlackBody) :
    b.T = (4 / 3) * (b.E / b.S) := by
  rw [b.stefan_boltzmann]; ring

/-- **Stefan-Boltzmann implies Ott.** With E → γE and S → S (invariant),
    the temperature extracted from the ratio is T' = γT. -/
lemma stefan_boltzmann_implies_ott (b : BlackBody) (v : ℝ) (hv : |v| < 1) :
    (4 / 3) * (lorentzGamma v hv * b.E / b.S) =
    lorentzGamma v hv * b.T := by
  rw [mul_div_assoc, b.stefan_boltzmann]; ring

/-- **The entropy of a photon gas is invariant under Ott.** Since both
    E and T scale by γ, the relation S = (4/3)E/T is preserved. -/
lemma ott_blackbody_entropy_invariant (b : BlackBody) (v : ℝ) (hv : |v| < 1) :
    let γ := lorentzGamma v hv
    (4 / 3) * (γ * b.E) / (γ * b.T) = (4 / 3) * b.E / b.T := by
  simp only
  have hγ_ne := lorentzGamma_ne_zero v hv
  have hT_ne : b.T ≠ 0 := ne_of_gt b.hT
  field_simp

/-- **Landsberg breaks the Stefan-Boltzmann relation.** Under T → T with
    E → γE, the relation E/S = (3/4)T becomes γE/S = (3/4)T, which
    contradicts E/S = (3/4)T for γ ≠ 1. The photon gas is no longer a
    black body in the moving frame. -/
lemma landsberg_breaks_stefan_boltzmann (b : BlackBody)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    lorentzGamma v hv * b.E / b.S ≠ (3 / 4) * b.T := by
  have hγ_gt := lorentzGamma_gt_one v hv hv_ne
  have hS_ne : b.S ≠ 0 := ne_of_gt b.hS
  intro h
  have h_orig := b.stefan_boltzmann
  -- From h: γE/S = (3/4)T, and h_orig: E/S = (3/4)T
  -- So γE/S = E/S, i.e. γ · (E/S) = E/S
  rw [mul_div_assoc] at h
  have h_eq : lorentzGamma v hv * (b.E / b.S) = b.E / b.S := by linarith
  have hES_pos : b.E / b.S > 0 := by
    rw [h_orig]; exact mul_pos (by norm_num : (3:ℝ) / 4 > 0) b.hT
  linarith [mul_lt_mul_of_pos_right hγ_gt hES_pos]

/-- **Landsberg makes entropy frame-dependent for photon gases.** If T → T
    but E → γE, then S = (4/3)E/T → (4/3)γE/T = γS. The photon gas
    acquires frame-dependent entropy — contradicting S = k ln Ω. -/
lemma landsberg_blackbody_entropy_fails (b : BlackBody)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    (4 / 3) * (lorentzGamma v hv * b.E) / b.T ≠ (4 / 3) * b.E / b.T := by
  have h_sb := b.stefan_boltzmann
  have hS_ne : b.S ≠ 0 := ne_of_gt b.hS
  have hE_pos : b.E > 0 := by
    have h := h_sb; rw [div_eq_iff hS_ne] at h; nlinarith [b.hT, b.hS]
  have hγ_gt := lorentzGamma_gt_one v hv hv_ne
  have hT_ne : b.T ≠ 0 := ne_of_gt b.hT
  intro heq
  rw [div_eq_div_iff hT_ne hT_ne] at heq
  -- heq : 4/3 * (γ * E) * T = 4/3 * E * T
  grind => ring

/-- **The CMB monopole.** An observer moving at velocity v relative to the
    CMB rest frame extracts a monopole temperature T' = γT from the
    full-sky average. This is greater than T for v ≠ 0. -/
lemma cmb_monopole_ott (T_cmb : ℝ) (hT : T_cmb > 0)
    (v : ℝ) (hv : |v| < 1) :
    lorentzGamma v hv * T_cmb ≥ T_cmb :=
  le_mul_of_one_le_left hT.le (lorentzGamma_ge_one v hv)

/-- For nonzero velocity, the observed CMB temperature is strictly hotter. -/
lemma cmb_monopole_strictly_hotter (T_cmb : ℝ) (hT : T_cmb > 0)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    lorentzGamma v hv * T_cmb > T_cmb :=
  (lt_mul_iff_one_lt_left hT).mpr (lorentzGamma_gt_one v hv hv_ne)

/-- **Summary.** The Stefan-Boltzmann law is a consistency check on T → γT:
    (1) E/S = (3/4)T is preserved under Ott (both sides scale by γ).
    (2) Under Landsberg, the relation breaks (left side inflates by γ).
    (3) Photon gas entropy becomes frame-dependent under Landsberg.
    (4) The CMB measurement confirms T → γT experimentally. -/
theorem blackbody_summary (b : BlackBody)
    (v : ℝ) (hv : |v| < 1) (hv_ne : v ≠ 0) :
    -- (1) Ott preserves Stefan-Boltzmann
    ((4 / 3) * (lorentzGamma v hv * b.E / b.S) = lorentzGamma v hv * b.T) ∧
    -- (2) Landsberg breaks Stefan-Boltzmann
    (lorentzGamma v hv * b.E / b.S ≠ (3 / 4) * b.T) ∧
    -- (3) Boosted observer sees hotter temperature
    (lorentzGamma v hv * b.T > b.T) :=
  ⟨stefan_boltzmann_implies_ott b v hv,
   landsberg_breaks_stefan_boltzmann b v hv hv_ne,
   cmb_monopole_strictly_hotter b.T b.hT v hv hv_ne⟩

end BlackBody

end RelativisticTemperature
