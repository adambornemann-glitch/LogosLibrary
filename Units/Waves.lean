-- Waves.lean          -- Frequency, wavelength, acoustic quantities
import LogosLibrary.Units.Core
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

open Units.SI

namespace Units.Waves

/-
================================================================================
WAVE PHYSICS UNITS LIBRARY
================================================================================

This module provides type-safe units for wave physics, acoustics, and
related phenomena. Following the triple-type architecture for maximum
flexibility without type conversion friction.

## COVERAGE
- Frequency units (Hz to THz and beyond)
- Wavelength units (meters to angstroms)
- Wavenumber and angular frequency
- Acoustic pressure and intensity
- Acoustic perception units (dB, phon, sone)
- Wave velocities and impedances
- Spectral densities
- Coherence and correlation functions

## USAGE PATTERNS
Float: Experimental measurements, signal processing, real-time acoustics
ℚ: Exact frequency ratios, musical intervals, digital signal processing
ℝ: Theoretical wave mechanics, continuous Fourier analysis
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Float Calculations
================================================================================================
-/
def pi_F : Float := 3.14159265358979323846
def e_F : Float := 2.71828182845904523536
def sqrt2_F : Float := 1.41421356237309504880
def sqrt3_F : Float := 1.73205080756887729352
def phi_F : Float := 1.61803398874989484820  -- golden ratio

/--
================================================================================================
   Frequency Units
================================================================================================
-/
-- structure Hertz_F        where val : Float deriving Repr, BEq, Inhabited  -- Hz
-- structure Hertz_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
-- structure Hertz_R        where val : ℝ     deriving Inhabited

structure Kilohertz_F    where val : Float deriving Repr, BEq, Inhabited  -- kHz
structure Kilohertz_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilohertz_R    where val : ℝ     deriving Inhabited

structure Megahertz_F    where val : Float deriving Repr, BEq, Inhabited  -- MHz
structure Megahertz_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megahertz_R    where val : ℝ     deriving Inhabited

structure Gigahertz_F    where val : Float deriving Repr, BEq, Inhabited  -- GHz
structure Gigahertz_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigahertz_R    where val : ℝ     deriving Inhabited

structure Terahertz_F    where val : Float deriving Repr, BEq, Inhabited  -- THz
structure Terahertz_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Terahertz_R    where val : ℝ     deriving Inhabited

structure AngularFrequency_F  where val : Float deriving Repr, BEq, Inhabited  -- rad/s
structure AngularFrequency_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AngularFrequency_R  where val : ℝ     deriving Inhabited

structure BeatsPerMinute_F    where val : Float deriving Repr, BEq, Inhabited  -- BPM
structure BeatsPerMinute_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BeatsPerMinute_R    where val : ℝ     deriving Inhabited

structure RevolutionsPerMinute_F where val : Float deriving Repr, BEq, Inhabited  -- RPM
structure RevolutionsPerMinute_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RevolutionsPerMinute_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Wavelength Units
================================================================================================
-/
structure WavelengthM_F   where val : Float deriving Repr, BEq, Inhabited  -- meters
structure WavelengthM_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthM_R   where val : ℝ     deriving Inhabited

structure WavelengthCM_F  where val : Float deriving Repr, BEq, Inhabited  -- centimeters
structure WavelengthCM_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthCM_R  where val : ℝ     deriving Inhabited

structure WavelengthMM_F  where val : Float deriving Repr, BEq, Inhabited  -- millimeters
structure WavelengthMM_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthMM_R  where val : ℝ     deriving Inhabited

structure WavelengthUM_F  where val : Float deriving Repr, BEq, Inhabited  -- micrometers
structure WavelengthUM_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WavelengthUM_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Wave Properties
================================================================================================
-/
structure WaveNumber_F     where val : Float deriving Repr, BEq, Inhabited  -- m⁻¹
structure WaveNumber_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaveNumber_R     where val : ℝ     deriving Inhabited

structure WaveVector_F     where val : Float deriving Repr, BEq, Inhabited  -- m⁻¹ (magnitude)
structure WaveVector_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaveVector_R     where val : ℝ     deriving Inhabited

structure Phase_F          where val : Float deriving Repr, BEq, Inhabited  -- radians
structure Phase_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Phase_R          where val : ℝ     deriving Inhabited

structure PhaseDeg_F       where val : Float deriving Repr, BEq, Inhabited  -- degrees
structure PhaseDeg_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhaseDeg_R       where val : ℝ     deriving Inhabited

structure PhaseVelocity_F  where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure PhaseVelocity_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PhaseVelocity_R  where val : ℝ     deriving Inhabited

structure GroupVelocity_F  where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure GroupVelocity_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GroupVelocity_R  where val : ℝ     deriving Inhabited

structure WaveAmplitude_F  where val : Float deriving Repr, BEq, Inhabited  -- context dependent units
structure WaveAmplitude_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure WaveAmplitude_R  where val : ℝ     deriving Inhabited

structure Period_F         where val : Float deriving Repr, BEq, Inhabited  -- seconds
structure Period_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Period_R         where val : ℝ     deriving Inhabited

/--
================================================================================================
   Acoustic Pressure & Intensity
================================================================================================
-/
structure SoundPressure_F       where val : Float deriving Repr, BEq, Inhabited  -- Pa
structure SoundPressure_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundPressure_R       where val : ℝ     deriving Inhabited

structure SoundPressureLevel_F  where val : Float deriving Repr, BEq, Inhabited  -- dB SPL
structure SoundPressureLevel_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundPressureLevel_R  where val : ℝ     deriving Inhabited

structure SoundIntensity_F      where val : Float deriving Repr, BEq, Inhabited  -- W/m²
structure SoundIntensity_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundIntensity_R      where val : ℝ     deriving Inhabited

structure SoundIntensityLevel_F where val : Float deriving Repr, BEq, Inhabited  -- dB SIL
structure SoundIntensityLevel_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundIntensityLevel_R where val : ℝ     deriving Inhabited

structure SoundPower_F          where val : Float deriving Repr, BEq, Inhabited  -- W
structure SoundPower_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundPower_R          where val : ℝ     deriving Inhabited

structure SoundPowerLevel_F     where val : Float deriving Repr, BEq, Inhabited  -- dB PWL
structure SoundPowerLevel_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SoundPowerLevel_R     where val : ℝ     deriving Inhabited

structure ParticleVelocity_F    where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure ParticleVelocity_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ParticleVelocity_R    where val : ℝ     deriving Inhabited

structure ParticleDisplacement_F where val : Float deriving Repr, BEq, Inhabited  -- m
structure ParticleDisplacement_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ParticleDisplacement_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Decibel Scales
================================================================================================
-/
structure Decibel_F       where val : Float deriving Repr, BEq, Inhabited  -- dB (generic)
structure Decibel_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Decibel_R       where val : ℝ     deriving Inhabited

structure DecibelA_F      where val : Float deriving Repr, BEq, Inhabited  -- dBA (A-weighted)
structure DecibelA_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DecibelA_R      where val : ℝ     deriving Inhabited

structure DecibelC_F      where val : Float deriving Repr, BEq, Inhabited  -- dBC (C-weighted)
structure DecibelC_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DecibelC_R      where val : ℝ     deriving Inhabited

structure Neper_F         where val : Float deriving Repr, BEq, Inhabited  -- Np (natural log ratio)
structure Neper_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Neper_R         where val : ℝ     deriving Inhabited

structure Bel_F           where val : Float deriving Repr, BEq, Inhabited  -- B (10 dB)
structure Bel_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Bel_R           where val : ℝ     deriving Inhabited

/--
================================================================================================
   Acoustic Impedance & Properties
================================================================================================
-/
structure AcousticImpedance_F   where val : Float deriving Repr, BEq, Inhabited  -- Pa·s/m (rayl)
structure AcousticImpedance_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AcousticImpedance_R   where val : ℝ     deriving Inhabited

structure SpecificImpedance_F   where val : Float deriving Repr, BEq, Inhabited  -- Pa·s/m³
structure SpecificImpedance_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpecificImpedance_R   where val : ℝ     deriving Inhabited

structure MechanicalImpedance_F  where val : Float deriving Repr, BEq, Inhabited  -- N·s/m
structure MechanicalImpedance_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MechanicalImpedance_R  where val : ℝ     deriving Inhabited

structure AbsorptionCoeff_F     where val : Float deriving Repr, BEq, Inhabited  -- α (0-1)
structure AbsorptionCoeff_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AbsorptionCoeff_R     where val : ℝ     deriving Inhabited

structure TransmissionLoss_F    where val : Float deriving Repr, BEq, Inhabited  -- dB
structure TransmissionLoss_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TransmissionLoss_R    where val : ℝ     deriving Inhabited

structure ReflectionCoeff_F     where val : Float deriving Repr, BEq, Inhabited  -- (-1 to 1)
structure ReflectionCoeff_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ReflectionCoeff_R     where val : ℝ     deriving Inhabited

structure TransmissionCoeff_F   where val : Float deriving Repr, BEq, Inhabited  -- (0-1)
structure TransmissionCoeff_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TransmissionCoeff_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Psychoacoustics & Perception
================================================================================================
-/
structure Loudness_F      where val : Float deriving Repr, BEq, Inhabited  -- sone
structure Loudness_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Loudness_R      where val : ℝ     deriving Inhabited

structure LoudnessLevel_F where val : Float deriving Repr, BEq, Inhabited  -- phon
structure LoudnessLevel_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LoudnessLevel_R where val : ℝ     deriving Inhabited

structure Pitch_F         where val : Float deriving Repr, BEq, Inhabited  -- mel
structure Pitch_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Pitch_R         where val : ℝ     deriving Inhabited

structure CriticalBand_F  where val : Float deriving Repr, BEq, Inhabited  -- Bark
structure CriticalBand_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CriticalBand_R  where val : ℝ     deriving Inhabited

structure Sharpness_F     where val : Float deriving Repr, BEq, Inhabited  -- acum
structure Sharpness_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Sharpness_R     where val : ℝ     deriving Inhabited

structure Roughness_F     where val : Float deriving Repr, BEq, Inhabited  -- asper
structure Roughness_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Roughness_R     where val : ℝ     deriving Inhabited

structure Fluctuation_F   where val : Float deriving Repr, BEq, Inhabited  -- vacil
structure Fluctuation_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fluctuation_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Musical Acoustics
================================================================================================
-/
structure MusicalInterval_F  where val : Float deriving Repr, BEq, Inhabited  -- cents
structure MusicalInterval_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MusicalInterval_R  where val : ℝ     deriving Inhabited

structure Octave_F           where val : Float deriving Repr, BEq, Inhabited  -- frequency ratio 2:1
structure Octave_Q           where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Octave_R           where val : ℝ     deriving Inhabited

structure Semitone_F         where val : Float deriving Repr, BEq, Inhabited  -- 100 cents
structure Semitone_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Semitone_R         where val : ℝ     deriving Inhabited

structure MIDINote           where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited  -- 0-127

structure Tempo_F            where val : Float deriving Repr, BEq, Inhabited  -- BPM
structure Tempo_Q            where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Tempo_R            where val : ℝ     deriving Inhabited

/--
================================================================================================
   Ultrasound & Medical
================================================================================================
-/
structure AcousticPower_F       where val : Float deriving Repr, BEq, Inhabited  -- W
structure AcousticPower_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AcousticPower_R       where val : ℝ     deriving Inhabited

structure IntensitySPTA_F       where val : Float deriving Repr, BEq, Inhabited  -- W/cm² (spatial peak temporal avg)
structure IntensitySPTA_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IntensitySPTA_R       where val : ℝ     deriving Inhabited

structure IntensitySPTP_F       where val : Float deriving Repr, BEq, Inhabited  -- W/cm² (spatial peak temporal peak)
structure IntensitySPTP_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure IntensitySPTP_R       where val : ℝ     deriving Inhabited

structure MechanicalIndex_F     where val : Float deriving Repr, BEq, Inhabited  -- MI (dimensionless)
structure MechanicalIndex_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MechanicalIndex_R     where val : ℝ     deriving Inhabited

structure ThermalIndex_F        where val : Float deriving Repr, BEq, Inhabited  -- TI (dimensionless)
structure ThermalIndex_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThermalIndex_R        where val : ℝ     deriving Inhabited

structure PulseDurationUS_F     where val : Float deriving Repr, BEq, Inhabited  -- μs
structure PulseDurationUS_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseDurationUS_R     where val : ℝ     deriving Inhabited

structure PulseRepetitionFreq_F where val : Float deriving Repr, BEq, Inhabited  -- Hz
structure PulseRepetitionFreq_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PulseRepetitionFreq_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Seismic & Elastic Waves
================================================================================================
-/
structure SeismicVelocity_F     where val : Float deriving Repr, BEq, Inhabited  -- km/s
structure SeismicVelocity_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeismicVelocity_R     where val : ℝ     deriving Inhabited

structure PWaveVelocity_F       where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure PWaveVelocity_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PWaveVelocity_R       where val : ℝ     deriving Inhabited

structure SWaveVelocity_F       where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure SWaveVelocity_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SWaveVelocity_R       where val : ℝ     deriving Inhabited

structure RayleighWaveVel_F     where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure RayleighWaveVel_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RayleighWaveVel_R     where val : ℝ     deriving Inhabited

structure LoveWaveVel_F         where val : Float deriving Repr, BEq, Inhabited  -- m/s
structure LoveWaveVel_Q         where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LoveWaveVel_R         where val : ℝ     deriving Inhabited

structure SeismicMoment_F       where val : Float deriving Repr, BEq, Inhabited  -- N·m
structure SeismicMoment_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SeismicMoment_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Dispersion & Attenuation
================================================================================================
-/
structure Dispersion_F          where val : Float deriving Repr, BEq, Inhabited  -- s/m
structure Dispersion_Q          where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Dispersion_R          where val : ℝ     deriving Inhabited

structure AttenuationCoeff_F    where val : Float deriving Repr, BEq, Inhabited  -- Np/m or dB/m
structure AttenuationCoeff_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AttenuationCoeff_R    where val : ℝ     deriving Inhabited

structure QualityFactorQ_F      where val : Float deriving Repr, BEq, Inhabited  -- Q factor
structure QualityFactorQ_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QualityFactorQ_R      where val : ℝ     deriving Inhabited

structure DampingRatio_F        where val : Float deriving Repr, BEq, Inhabited  -- ζ (zeta)
structure DampingRatio_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DampingRatio_R        where val : ℝ     deriving Inhabited

structure LogarithmicDecrement_F where val : Float deriving Repr, BEq, Inhabited  -- δ
structure LogarithmicDecrement_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogarithmicDecrement_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Standing Waves & Resonance
================================================================================================
-/
structure ResonantFrequency_F   where val : Float deriving Repr, BEq, Inhabited  -- Hz
structure ResonantFrequency_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ResonantFrequency_R   where val : ℝ     deriving Inhabited

structure Harmonic              where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited  -- 1st, 2nd, ...

structure StandingWaveRatio_F   where val : Float deriving Repr, BEq, Inhabited  -- SWR
structure StandingWaveRatio_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StandingWaveRatio_R   where val : ℝ     deriving Inhabited

structure NodePosition_F        where val : Float deriving Repr, BEq, Inhabited  -- m
structure NodePosition_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure NodePosition_R        where val : ℝ     deriving Inhabited

structure AntinodePosition_F    where val : Float deriving Repr, BEq, Inhabited  -- m
structure AntinodePosition_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure AntinodePosition_R    where val : ℝ     deriving Inhabited

/--
================================================================================================
   Measurement Uncertainty for Common Wave Quantities
================================================================================================
-/
structure FrequencyWithError_F where
  value : Hertz_F
  uncertainty : Hertz_F
  deriving Repr, BEq, Inhabited

structure WavelengthWithError_F where
  value : WavelengthM_F
  uncertainty : WavelengthM_F
  deriving Repr, BEq, Inhabited

structure SoundLevelWithError_F where
  value : SoundPressureLevel_F
  uncertainty : SoundPressureLevel_F
  deriving Repr, BEq, Inhabited

structure PhaseWithError_F where
  value : Phase_F
  uncertainty : Phase_F
  deriving Repr, BEq, Inhabited

/--
================================================================================================
   Helper Functions
================================================================================================
-/

-- Constructor with range check for absorption coefficient (0-1)
def mkAbsorptionCoeff_F (v : Float) : Option AbsorptionCoeff_F :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

def mkAbsorptionCoeff_Q (v : ℚ) : Option AbsorptionCoeff_Q :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

noncomputable def mkAbsorptionCoeff_R (v : ℝ) : Option AbsorptionCoeff_R :=
  if 0.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

-- Constructor for reflection coefficient (-1 to 1)
def mkReflectionCoeff_F (v : Float) : Option ReflectionCoeff_F :=
  if -1.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

def mkReflectionCoeff_Q (v : ℚ) : Option ReflectionCoeff_Q :=
  if -1.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

noncomputable def mkReflectionCoeff_R (v : ℝ) : Option ReflectionCoeff_R :=
  if -1.0 ≤ v && v ≤ 1.0 then some ⟨v⟩ else none

-- Constructor for MIDI notes (0-127)
-- def mkMIDINote (v : ℕ) : Option MIDINote :=
--   if v ≤ 127 then some

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Frequency conversions
def hertzToKilohertz_F (hz : Hertz_F) : Kilohertz_F :=
  ⟨hz.val / 1000.0⟩

def kilohertzToHertz_F (khz : Kilohertz_F) : Hertz_F :=
  ⟨khz.val * 1000.0⟩

def hertzToMegahertz_F (hz : Hertz_F) : Megahertz_F :=
  ⟨hz.val / 1e6⟩

def megahertzToHertz_F (mhz : Megahertz_F) : Hertz_F :=
  ⟨mhz.val * 1e6⟩

def hertzToAngularFreq_F (f : Hertz_F) : AngularFrequency_F :=
  ⟨2.0 * pi_F * f.val⟩

def angularFreqToHertz_F (omega : AngularFrequency_F) : Hertz_F :=
  ⟨omega.val / (2.0 * pi_F)⟩

def bpmToHertz_F (bpm : BeatsPerMinute_F) : Hertz_F :=
  ⟨bpm.val / 60.0⟩

def hertzToBPM_F (hz : Hertz_F) : BeatsPerMinute_F :=
  ⟨hz.val * 60.0⟩

def rpmToHertz_F (rpm : RevolutionsPerMinute_F) : Hertz_F :=
  ⟨rpm.val / 60.0⟩

-- Period-frequency conversions
def periodToFrequency_F (T : Period_F) : Hertz_F :=
  ⟨1.0 / T.val⟩

def frequencyToPeriod_F (f : Hertz_F) : Period_F :=
  ⟨1.0 / f.val⟩

-- Wavelength conversions
def wavelengthMToCM_F (lambda : WavelengthM_F) : WavelengthCM_F :=
  ⟨lambda.val * 100.0⟩

def wavelengthCMToM_F (lambda : WavelengthCM_F) : WavelengthM_F :=
  ⟨lambda.val / 100.0⟩

def wavelengthMToMM_F (lambda : WavelengthM_F) : WavelengthMM_F :=
  ⟨lambda.val * 1000.0⟩

def wavelengthMMToM_F (lambda : WavelengthMM_F) : WavelengthM_F :=
  ⟨lambda.val / 1000.0⟩

-- Phase conversions
def phaseRadToDeg_F (phase : Phase_F) : PhaseDeg_F :=
  ⟨phase.val * 180.0 / pi_F⟩

def phaseDegToRad_F (phase : PhaseDeg_F) : Phase_F :=
  ⟨phase.val * pi_F / 180.0⟩

-- Decibel conversions
def soundPressureToSPL_F (pressure : SoundPressure_F) : SoundPressureLevel_F :=
  let p_ref := 20e-6  -- 20 μPa reference
  ⟨20.0 * Float.log10 (pressure.val / p_ref)⟩

def splToSoundPressure_F (spl : SoundPressureLevel_F) : SoundPressure_F :=
  let p_ref := 20e-6
  ⟨p_ref * (10.0 ^ (spl.val / 20.0))⟩

def soundIntensityToSIL_F (intensity : SoundIntensity_F) : SoundIntensityLevel_F :=
  let I_ref := 1e-12  -- 10^-12 W/m² reference
  ⟨10.0 * Float.log10 (intensity.val / I_ref)⟩

def silToSoundIntensity_F (sil : SoundIntensityLevel_F) : SoundIntensity_F :=
  let I_ref := 1e-12
  ⟨I_ref * (10.0 ^ (sil.val / 10.0))⟩

def soundPowerToPWL_F (power : SoundPower_F) : SoundPowerLevel_F :=
  let P_ref := 1e-12  -- 10^-12 W reference
  ⟨10.0 * Float.log10 (power.val / P_ref)⟩

def pwlToSoundPower_F (pwl : SoundPowerLevel_F) : SoundPower_F :=
  let P_ref := 1e-12
  ⟨P_ref * (10.0 ^ (pwl.val / 10.0))⟩

-- Musical interval conversions
def frequencyRatioToCents_F (ratio : Float) : MusicalInterval_F :=
  ⟨1200.0 * Float.log2 ratio⟩

def centsToFrequencyRatio_F (cents : MusicalInterval_F) : Float :=
  2.0 ^ (cents.val / 1200.0)

def octavesToCents_F (octaves : Octave_F) : MusicalInterval_F :=
  ⟨octaves.val * 1200.0⟩

def semitonesToCents_F (semitones : Semitone_F) : MusicalInterval_F :=
  ⟨semitones.val * 100.0⟩

-- MIDI note to frequency (A4 = 440 Hz, MIDI note 69)
def midiNoteToFrequency_F (note : MIDINote) (a4Freq : Float := 440.0) : Hertz_F :=
  ⟨a4Freq * (2.0 ^ ((note.val.toFloat - 69.0) / 12.0))⟩

def frequencyToMidiNote_F (freq : Hertz_F) (a4Freq : Float := 440.0) : Float :=
  69.0 + 12.0 * Float.log2 (freq.val / a4Freq)

-- Neper to decibel conversion
def neperToDecibel_F (np : Neper_F) : Decibel_F :=
  ⟨np.val * 20.0 / Float.log 10.0⟩  -- ≈ 8.686 dB/Np

def decibelToNeper_F (db : Decibel_F) : Neper_F :=
  ⟨db.val * Float.log 10.0 / 20.0⟩

/--
================================================================================================
   Common Wave Calculations
================================================================================================
-/

-- Wave equation: v = f × λ
def waveSpeed_F (freq : Hertz_F) (wavelength : WavelengthM_F) : PhaseVelocity_F :=
  ⟨freq.val * wavelength.val⟩

def wavelengthFromSpeed_F (speed : PhaseVelocity_F) (freq : Hertz_F) : WavelengthM_F :=
  ⟨speed.val / freq.val⟩

def frequencyFromSpeed_F (speed : PhaseVelocity_F) (wavelength : WavelengthM_F) : Hertz_F :=
  ⟨speed.val / wavelength.val⟩

-- Wave number k = 2π/λ = ω/v
def waveNumber_F (wavelength : WavelengthM_F) : WaveNumber_F :=
  ⟨2.0 * pi_F / wavelength.val⟩

def waveNumberFromFreq_F (omega : AngularFrequency_F) (speed : PhaseVelocity_F) : WaveNumber_F :=
  ⟨omega.val / speed.val⟩

-- Doppler effect (source moving)
def dopplerFrequency_F (sourceFreq : Hertz_F) (waveSpeed : PhaseVelocity_F)
    (sourceVel : Float) (observerVel : Float := 0.0) : Hertz_F :=
  ⟨sourceFreq.val * (waveSpeed.val + observerVel) / (waveSpeed.val - sourceVel)⟩

-- Beat frequency
def beatFrequency_F (f1 f2 : Hertz_F) : Hertz_F :=
  ⟨(f1.val - f2.val).abs⟩

-- Standing wave resonant frequencies (string/pipe)
def harmonicFrequency_F (fundamental : ResonantFrequency_F) (n : Harmonic) : Hertz_F :=
  ⟨fundamental.val * n.val.toFloat⟩

-- Open pipe/string resonance
def openPipeResonance_F (length : Meter_F) (soundSpeed : PhaseVelocity_F)
    (n : Harmonic) : ResonantFrequency_F :=
  ⟨n.val.toFloat * soundSpeed.val / (2.0 * length.val)⟩

-- Closed pipe resonance (odd harmonics only)
def closedPipeResonance_F (length : Meter_F) (soundSpeed : PhaseVelocity_F)
    (n : ℕ) : ResonantFrequency_F :=
  ⟨(2.0 * n.toFloat - 1.0) * soundSpeed.val / (4.0 * length.val)⟩

-- Acoustic impedance Z = ρc
def acousticImpedance_F (density : Float) (soundSpeed : PhaseVelocity_F)
    : AcousticImpedance_F :=
  ⟨density * soundSpeed.val⟩

-- Sound intensity from pressure
def soundIntensityFromPressure_F (pressure : SoundPressure_F)
    (impedance : AcousticImpedance_F) : SoundIntensity_F :=
  ⟨pressure.val^2 / (2.0 * impedance.val)⟩

-- Particle velocity from pressure
def particleVelocity_F (pressure : SoundPressure_F)
    (impedance : AcousticImpedance_F) : ParticleVelocity_F :=
  ⟨pressure.val / impedance.val⟩

-- Reflection coefficient at interface
def reflectionCoefficient_F (Z1 Z2 : AcousticImpedance_F) : ReflectionCoeff_F :=
  ⟨(Z2.val - Z1.val) / (Z2.val + Z1.val)⟩

-- Transmission coefficient
def transmissionCoefficient_F (Z1 Z2 : AcousticImpedance_F) : TransmissionCoeff_F :=
  ⟨2.0 * Z2.val / (Z2.val + Z1.val)⟩

-- Absorption coefficient from reflection
def absorptionFromReflection_F (r : ReflectionCoeff_F) : AbsorptionCoeff_F :=
  ⟨1.0 - r.val^2⟩

-- Standing wave ratio
def standingWaveRatio_F (r : ReflectionCoeff_F) : StandingWaveRatio_F :=
  ⟨(1.0 + r.val.abs) / (1.0 - r.val.abs)⟩

-- Q factor from damping ratio
def qFactorFromDamping_F (zeta : DampingRatio_F) : QualityFactorQ_F :=
  ⟨1.0 / (2.0 * zeta.val)⟩

-- Damping ratio from Q factor
def dampingFromQFactor_F (Q : QualityFactorQ_F) : DampingRatio_F :=
  ⟨1.0 / (2.0 * Q.val)⟩

-- Logarithmic decrement from damping ratio
def logarithmicDecrement_F (zeta : DampingRatio_F) : LogarithmicDecrement_F :=
  ⟨2.0 * pi_F * zeta.val / Float.sqrt (1.0 - zeta.val^2)⟩

-- Attenuation in dB/m from Neper/m
def attenuationDbFromNp_F (alpha_np : Float) : AttenuationCoeff_F :=
  ⟨alpha_np * 8.686⟩

-- Wavelength in different media
def wavelengthInMedium_F (vacuumWavelength : WavelengthM_F)
    (refractiveIndex : Float) : WavelengthM_F :=
  ⟨vacuumWavelength.val / refractiveIndex⟩

-- Group velocity from dispersion relation
def groupVelocity_F (phaseVel : PhaseVelocity_F) (wavelength : WavelengthM_F)
    (dispersion : Dispersion_F) : GroupVelocity_F :=
  ⟨phaseVel.val - wavelength.val * dispersion.val⟩

-- Sound level addition (logarithmic)
def addSoundLevels_F (levels : Array SoundPressureLevel_F) : SoundPressureLevel_F :=
  let sum := levels.foldl (fun acc spl => acc + 10.0 ^ (spl.val / 10.0)) 0.0
  ⟨10.0 * Float.log10 sum⟩

-- A-weighting approximation for frequency
def aWeighting_F (freq : Hertz_F) : Float :=
  let f := freq.val
  let f2 := f * f
  let f4 := f2 * f2
  let num := 12194.0^2 * f4
  let den := (f2 + 20.6^2) * Float.sqrt ((f2 + 107.7^2) * (f2 + 737.9^2)) * (f2 + 12194.0^2)
  20.0 * Float.log10 (num / den) + 2.0

-- Node positions for standing wave
def nodePositions_F (wavelength : WavelengthM_F) (n : ℕ) : NodePosition_F :=
  ⟨n.toFloat * wavelength.val / 2.0⟩

-- Antinode positions for standing wave
def antinodePositions_F (wavelength : WavelengthM_F) (n : ℕ) : AntinodePosition_F :=
  ⟨(2.0 * n.toFloat + 1.0) * wavelength.val / 4.0⟩

-- Ultrasound mechanical index
def mechanicalIndex_F (peakNegPressure : Float) (freq : Megahertz_F) : MechanicalIndex_F :=
  ⟨peakNegPressure / Float.sqrt freq.val⟩

-- Seismic wave velocities from elastic moduli
def pWaveVelocity_F (bulkMod : Float) (shearMod : Float) (density : Float) : PWaveVelocity_F :=
  ⟨Float.sqrt ((bulkMod + 4.0/3.0 * shearMod) / density)⟩

def sWaveVelocity_F (shearMod : Float) (density : Float) : SWaveVelocity_F :=
  ⟨Float.sqrt (shearMod / density)⟩

-- Rayleigh wave velocity approximation
def rayleighWaveVelocity_F (sWaveVel : SWaveVelocity_F) : RayleighWaveVel_F :=
  ⟨0.92 * sWaveVel.val⟩  -- Approximate for Poisson ratio ~0.25

-- Critical angle for total internal reflection
def criticalAngle_F (n1 n2 : Float) : Option Phase_F :=
  if n1 > n2 then
    some ⟨Float.asin (n2 / n1)⟩
  else
    none

-- Phon to sone conversion (Stevens' power law approximation)
def phonToSone_F (phon : LoudnessLevel_F) : Loudness_F :=
  if phon.val < 40.0 then
    ⟨2.0 ^ ((phon.val - 40.0) / 10.0)⟩
  else
    ⟨2.0 ^ ((phon.val - 40.0) / 10.0)⟩

-- Frequency to mel scale
def frequencyToMel_F (freq : Hertz_F) : Pitch_F :=
  ⟨2595.0 * Float.log10 (1.0 + freq.val / 700.0)⟩

-- Mel to frequency
def melToFrequency_F (mel : Pitch_F) : Hertz_F :=
  ⟨700.0 * (10.0 ^ (mel.val / 2595.0) - 1.0)⟩

-- Frequency to Bark scale
def frequencyToBark_F (freq : Hertz_F) : CriticalBand_F :=
  let f_khz := freq.val / 1000.0
  ⟨13.0 * Float.atan (0.76 * f_khz) + 3.5 * Float.atan ((f_khz / 7.5)^2)⟩

end Units.Waves
