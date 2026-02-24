/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.Superior.ThermalTime.Basic
import LogosLibrary.Superior.ThermalTime.Measurement

namespace ThermalTime.InformationTheory
open Basic Measure

/-- Conversion factor: 1 bit = ln(2) nats -/
noncomputable def natsPerBit : ℝ := Real.log 2

lemma natsPerBit_pos : natsPerBit > 0 := Real.log_pos (by exact one_lt_two )

/-- Convert entropy from nats to bits -/
noncomputable def natsToBits (S_nats : ℝ) : ℝ := S_nats / natsPerBit

/-- Convert entropy from bits to nats -/
noncomputable def bitsToNats (S_bits : ℝ) : ℝ := S_bits * natsPerBit

theorem bits_nats_inverse (S : ℝ) : natsToBits (bitsToNats S) = S := by
  unfold natsToBits bitsToNats
  have h : natsPerBit ≠ 0 := ne_of_gt natsPerBit_pos
  field_simp

theorem nats_bits_inverse (S : ℝ) : bitsToNats (natsToBits S) = S := by
  unfold natsToBits bitsToNats
  have h : natsPerBit ≠ 0 := ne_of_gt natsPerBit_pos
  field_simp

/-! ### Landauer's Principle -/

/-- Landauer's principle: minimum energy to erase one bit at temperature T

    E = k_B T ln(2)

    In natural units (k_B = 1): E = T ln(2) -/
noncomputable def landauerCost (T : ℝ) : ℝ := T * natsPerBit

theorem landauerCost_pos (T : ℝ) (hT : T > 0) : landauerCost T > 0 := by
  unfold landauerCost
  exact mul_pos hT natsPerBit_pos

/-- Energy cost to produce ΔS nats of entropy -/
noncomputable def entropyCost (T : ℝ) (ΔS_nats : ℝ) : ℝ := T * ΔS_nats

/-- Landauer cost is entropy cost for ln(2) nats (= 1 bit) -/
theorem landauer_is_one_bit_entropy (T : ℝ) :
    landauerCost T = entropyCost T natsPerBit := by
  unfold landauerCost entropyCost
  ring

/-! ### Measurement as Information -/

/-- Bits of correlation established by a measurement -/
noncomputable def Measurement.bits (m : Measurement) : ℝ :=
  natsToBits m.ΔS

/-- One modular cycle in bits: 2π / ln(2) ≈ 9.064 bits -/
noncomputable def bitsPerModularCycle : ℝ := natsToBits entropyQuantum

/-- The fundamental measurement establishes ~9 bits of correlation -/
theorem bitsPerModularCycle_eq : bitsPerModularCycle = 2 * Real.pi / Real.log 2 := by
  unfold bitsPerModularCycle natsToBits entropyQuantum natsPerBit
  ring

/-- Bits of correlation established by a measurement -/
noncomputable def measurementBits (m : Measurement) : ℝ :=
  natsToBits m.ΔS

/-- A measurement establishes at least one modular cycle worth of bits -/
theorem measurement_bits_lower_bound (m : Measurement) :
    measurementBits m ≥ bitsPerModularCycle := by
  unfold measurementBits bitsPerModularCycle natsToBits
  apply div_le_div_of_nonneg_right m.h_minimal (le_of_lt natsPerBit_pos)

/-- ln(2) < 1 (since 2 < e) -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
  have h := Real.add_one_lt_exp (one_ne_zero' ℝ)
  norm_num at h
  exact h


/-! ### Physical Interpretation -/

/-- Energy cost of a measurement -/
noncomputable def Measurement.energyCost (m : Measurement) (T : ℝ) : ℝ :=
  entropyCost T m.ΔS

/-- Minimum energy cost of any measurement at temperature T -/
noncomputable def minMeasurementEnergy (T : ℝ) : ℝ :=
  entropyCost T entropyQuantum

theorem minMeasurementEnergy_eq (T : ℝ) :
    minMeasurementEnergy T = 2 * Real.pi * T := by
  unfold minMeasurementEnergy entropyCost entropyQuantum
  ring

/-- Energy cost of a measurement -/
noncomputable def measurementEnergyCost (m : Measurement) (T : ℝ) : ℝ :=
  entropyCost T m.ΔS

/-- A measurement costs at least ~9 Landauer erasures worth of energy -/
theorem measurement_energy_bound (m : Measurement) (T : ℝ) (hT : T > 0) :
    measurementEnergyCost m T ≥ minMeasurementEnergy T := by
  unfold measurementEnergyCost minMeasurementEnergy entropyCost
  exact mul_le_mul_of_nonneg_left m.h_minimal (le_of_lt hT)

/-- Minimum measurement energy in terms of Landauer cost -/
theorem minMeasurementEnergy_in_landauer' (T : ℝ) :
    minMeasurementEnergy T = bitsPerModularCycle * landauerCost T := by
  unfold minMeasurementEnergy bitsPerModularCycle landauerCost
  unfold entropyCost natsToBits entropyQuantum natsPerBit
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1:ℝ) < 2))
  field_simp

/-- A measurement record is the correlation established between system and apparatus.

    Before measurement: System and apparatus uncorrelated
    After measurement: ~9 bits of mutual information

    This IS what "having a measurement result" means. -/
structure MeasurementRecord where
  /-- The measurement that was performed -/
  measurement : Measurement
  /-- Mutual information between system and apparatus (in bits) -/
  mutualInformation : ℝ
  /-- The correlation equals the entropy produced -/
  correlation_eq_entropy : mutualInformation = measurementBits measurement

/-- The "collapse" is just the establishment of correlation -/
theorem collapse_is_correlation (r : MeasurementRecord) :
    r.mutualInformation ≥ bitsPerModularCycle := by
  rw [r.correlation_eq_entropy]
  exact measurement_bits_lower_bound r.measurement

/-- No correlation without entropy production -/
theorem no_free_information (m : Measurement) :
    measurementBits m > 0 := by
  calc measurementBits m
      ≥ bitsPerModularCycle := measurement_bits_lower_bound m
    _ = 2 * Real.pi / Real.log 2 := bitsPerModularCycle_eq
    _ > 0 := by positivity

/-- The Holevo bound: accessible classical information ≤ von Neumann entropy.

    A measurement that extracts n bits of information must produce
    at least n bits worth of entropy. Our bound says n ≥ 2π/ln(2) ≈ 9 bits
    for any complete measurement. -/
theorem holevo_consistency (m : Measurement)
    (accessible_info : ℝ)
    (h_holevo : accessible_info ≤ measurementBits m) :
    accessible_info ≤ m.ΔS / natsPerBit := by
  calc accessible_info
      ≤ measurementBits m := h_holevo
    _ = m.ΔS / natsPerBit := rfl

end ThermalTime.InformationTheory
