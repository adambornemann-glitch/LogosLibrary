-- Information.lean        -- Information theory, data, entropy, compression
import LogosLibrary.Units.Core
import LogosLibrary.Units.Chemistry
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

namespace Units.Information

open Units.SI Units.Chemistry

/-
================================================================================
INFORMATION THEORY AND DATA UNITS LIBRARY
================================================================================

This module provides type-safe units for information theory, data storage,
communication, compression, entropy measures, and computational complexity.
Following the triple-type architecture for maximum flexibility without type
conversion friction.

## COVERAGE
- Information content (bits, bytes, nats, dits)
- Data storage (KB, MB, GB, TB, PB, EB with both binary and decimal)
- Bandwidth and data rates (bps, baud, throughput)
- Shannon entropy and information measures
- Relative entropy (KL divergence) and mutual information
- Channel capacity and error rates
- Compression ratios and algorithmic complexity
- Signal-to-noise ratios (linear and dB)
- Error rates (BER, FER, SER)
- Quantum information (qubits, ebits)
- Computational complexity measures
- Network metrics (latency, jitter, packet loss)

## USAGE PATTERNS
Float: Network measurements, compression algorithms, real-time communications,
signal processing, machine learning metrics, streaming data, sensor networks,
codec implementations, channel measurements

ℚ: Exact entropy calculations, lossless compression ratios, error correction
codes, cryptographic computations, discrete channel capacities,
Huffman coding, arithmetic coding, exact information measures

ℝ: Continuous entropy, differential entropy, rate-distortion theory,
information-theoretic proofs, asymptotic analysis, source coding theorems,
channel coding theorems, complexity theory bounds
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Information Theory
================================================================================================
-/
def ln2_F : Float := 0.693147180559945309417
def log2_e_F : Float := 1.44269504088896340736  -- 1/ln(2)
def log10_2_F : Float := 0.301029995663981195214
def log2_10_F : Float := 3.32192809488736234787

/--
================================================================================================
   Basic Information Units
================================================================================================
-/
-- Bit: binary digit
structure Bit_F        where val : Float deriving Repr, BEq, Inhabited
structure Bit_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Bit_R        where val : ℝ     deriving Inhabited

structure Kilobit_F    where val : Float deriving Repr, BEq, Inhabited
structure Kilobit_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilobit_R    where val : ℝ     deriving Inhabited

structure Megabit_F    where val : Float deriving Repr, BEq, Inhabited
structure Megabit_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megabit_R    where val : ℝ     deriving Inhabited

structure Gigabit_F    where val : Float deriving Repr, BEq, Inhabited
structure Gigabit_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigabit_R    where val : ℝ     deriving Inhabited

-- Byte: 8 bits
structure Byte_F       where val : Float deriving Repr, BEq, Inhabited
structure Byte_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Byte_R       where val : ℝ     deriving Inhabited

-- Decimal prefixes (SI: 1000-based)
structure Kilobyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Kilobyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilobyte_R   where val : ℝ     deriving Inhabited

structure Megabyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Megabyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megabyte_R   where val : ℝ     deriving Inhabited

structure Gigabyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Gigabyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gigabyte_R   where val : ℝ     deriving Inhabited

structure Terabyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Terabyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Terabyte_R   where val : ℝ     deriving Inhabited

structure Petabyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Petabyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Petabyte_R   where val : ℝ     deriving Inhabited

structure Exabyte_F    where val : Float deriving Repr, BEq, Inhabited
structure Exabyte_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Exabyte_R    where val : ℝ     deriving Inhabited

-- Binary prefixes (IEC: 1024-based)
structure Kibibyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Kibibyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kibibyte_R   where val : ℝ     deriving Inhabited

structure Mebibyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Mebibyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mebibyte_R   where val : ℝ     deriving Inhabited

structure Gibibyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Gibibyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gibibyte_R   where val : ℝ     deriving Inhabited

structure Tebibyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Tebibyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Tebibyte_R   where val : ℝ     deriving Inhabited

structure Pebibyte_F   where val : Float deriving Repr, BEq, Inhabited
structure Pebibyte_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Pebibyte_R   where val : ℝ     deriving Inhabited

-- Natural units of information
structure Nat_F        where val : Float deriving Repr, BEq, Inhabited  -- Natural unit (base e)
structure Nat_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Nat_R        where val : ℝ     deriving Inhabited

-- Decimal digit of information
structure Dit_F        where val : Float deriving Repr, BEq, Inhabited  -- Decimal digit (base 10)
structure Dit_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Dit_R        where val : ℝ     deriving Inhabited

-- Trit: ternary digit
structure Trit_F       where val : Float deriving Repr, BEq, Inhabited
structure Trit_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Trit_R       where val : ℝ     deriving Inhabited

/--
================================================================================================
   Data Rates and Bandwidth
================================================================================================
-/
-- Bits per second
structure BitsPerSec_F where val : Float deriving Repr, BEq, Inhabited
structure BitsPerSec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BitsPerSec_R where val : ℝ     deriving Inhabited

structure Kbps_F       where val : Float deriving Repr, BEq, Inhabited
structure Kbps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kbps_R       where val : ℝ     deriving Inhabited

structure Mbps_F       where val : Float deriving Repr, BEq, Inhabited
structure Mbps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Mbps_R       where val : ℝ     deriving Inhabited

structure Gbps_F       where val : Float deriving Repr, BEq, Inhabited
structure Gbps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Gbps_R       where val : ℝ     deriving Inhabited

structure Tbps_F       where val : Float deriving Repr, BEq, Inhabited
structure Tbps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Tbps_R       where val : ℝ     deriving Inhabited

-- Bytes per second
structure BytesPerSec_F where val : Float deriving Repr, BEq, Inhabited
structure BytesPerSec_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BytesPerSec_R where val : ℝ     deriving Inhabited

structure KBps_F       where val : Float deriving Repr, BEq, Inhabited
structure KBps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KBps_R       where val : ℝ     deriving Inhabited

structure MBps_F       where val : Float deriving Repr, BEq, Inhabited
structure MBps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MBps_R       where val : ℝ     deriving Inhabited

structure GBps_F       where val : Float deriving Repr, BEq, Inhabited
structure GBps_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GBps_R       where val : ℝ     deriving Inhabited

-- Baud rate: symbols per second
structure Baud_F       where val : Float deriving Repr, BEq, Inhabited
structure Baud_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Baud_R       where val : ℝ     deriving Inhabited

structure Kilobaud_F   where val : Float deriving Repr, BEq, Inhabited
structure Kilobaud_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Kilobaud_R   where val : ℝ     deriving Inhabited

structure Megabaud_F   where val : Float deriving Repr, BEq, Inhabited
structure Megabaud_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Megabaud_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Entropy and Information Measures
================================================================================================
-/
-- Shannon entropy: bits (or nats, dits depending on base)
structure ShannonEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure ShannonEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ShannonEntropy_R where val : ℝ     deriving Inhabited

-- Differential entropy: bits (for continuous distributions)
structure DifferentialEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure DifferentialEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DifferentialEntropy_R where val : ℝ     deriving Inhabited

-- Mutual information: bits
structure MutualInfo_F where val : Float deriving Repr, BEq, Inhabited
structure MutualInfo_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MutualInfo_R where val : ℝ     deriving Inhabited

-- Kullback-Leibler divergence: bits (or nats)
structure KLDivergence_F where val : Float deriving Repr, BEq, Inhabited
structure KLDivergence_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KLDivergence_R where val : ℝ     deriving Inhabited

-- Cross entropy: bits
structure CrossEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure CrossEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CrossEntropy_R where val : ℝ     deriving Inhabited

-- Joint entropy: bits
structure JointEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure JointEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure JointEntropy_R where val : ℝ     deriving Inhabited

-- Conditional entropy: bits
structure ConditionalEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure ConditionalEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ConditionalEntropy_R where val : ℝ     deriving Inhabited

-- Rényi entropy: bits (parameterized by order α)
structure RenyiEntropy_F where
  val : Float
  order : Float  -- α parameter
  deriving Repr, BEq, Inhabited

structure RenyiEntropy_Q where
  val : ℚ
  order : ℚ
  deriving Repr, BEq, DecidableEq, Inhabited

structure RenyiEntropy_R where
  val : ℝ
  order : ℝ
  deriving Inhabited

/--
================================================================================================
   Channel Capacity and Communication
================================================================================================
-/
-- Channel capacity: bits per channel use
structure ChannelCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure ChannelCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ChannelCapacity_R where val : ℝ     deriving Inhabited

-- Spectral efficiency: bits/(s·Hz)
structure SpectralEfficiency_F where val : Float deriving Repr, BEq, Inhabited
structure SpectralEfficiency_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SpectralEfficiency_R where val : ℝ     deriving Inhabited

-- Information rate: bits/s
structure InfoRate_F   where val : Float deriving Repr, BEq, Inhabited
structure InfoRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure InfoRate_R   where val : ℝ     deriving Inhabited

-- Code rate: dimensionless (k/n)
structure CodeRate_F   where val : Float deriving Repr, BEq, Inhabited
structure CodeRate_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CodeRate_R   where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Rates and Reliability
================================================================================================
-/
-- Bit error rate: dimensionless
structure BER_F        where val : Float deriving Repr, BEq, Inhabited
structure BER_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BER_R        where val : ℝ     deriving Inhabited

-- Frame error rate: dimensionless
structure FER_F        where val : Float deriving Repr, BEq, Inhabited
structure FER_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure FER_R        where val : ℝ     deriving Inhabited

-- Symbol error rate: dimensionless
structure SER_F        where val : Float deriving Repr, BEq, Inhabited
structure SER_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SER_R        where val : ℝ     deriving Inhabited

-- Packet loss rate: dimensionless (%)
structure PacketLoss_F where val : Float deriving Repr, BEq, Inhabited
structure PacketLoss_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure PacketLoss_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Signal Quality Measures
================================================================================================
-/
-- Signal-to-noise ratio: dimensionless (linear)
structure SNR_F        where val : Float deriving Repr, BEq, Inhabited
structure SNR_Q        where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SNR_R        where val : ℝ     deriving Inhabited

-- SNR in decibels
structure SNR_dB_F     where val : Float deriving Repr, BEq, Inhabited
structure SNR_dB_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SNR_dB_R     where val : ℝ     deriving Inhabited

-- Energy per bit to noise density: dB
structure EbN0_dB_F    where val : Float deriving Repr, BEq, Inhabited
structure EbN0_dB_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EbN0_dB_R    where val : ℝ     deriving Inhabited

-- Carrier-to-noise ratio: dB
structure CNR_dB_F     where val : Float deriving Repr, BEq, Inhabited
structure CNR_dB_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CNR_dB_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Compression and Complexity
================================================================================================
-/
-- Compression ratio: dimensionless
structure CompressionRatio_F where val : Float deriving Repr, BEq, Inhabited
structure CompressionRatio_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CompressionRatio_R where val : ℝ     deriving Inhabited

-- Compression factor: dimensionless (1 - compressed/original)
structure CompressionFactor_F where val : Float deriving Repr, BEq, Inhabited
structure CompressionFactor_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CompressionFactor_R where val : ℝ     deriving Inhabited

-- Kolmogorov complexity: bits
structure KolmogorovComplexity_F where val : Float deriving Repr, BEq, Inhabited
structure KolmogorovComplexity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure KolmogorovComplexity_R where val : ℝ     deriving Inhabited

-- Lempel-Ziv complexity: dimensionless
structure LZComplexity_F where val : Float deriving Repr, BEq, Inhabited
structure LZComplexity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LZComplexity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Quantum Information
================================================================================================
-/
-- Qubit: quantum bit
structure Qubit_F      where val : Float deriving Repr, BEq, Inhabited
structure Qubit_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Qubit_R      where val : ℝ     deriving Inhabited

-- Ebit: entanglement bit
structure Ebit_F       where val : Float deriving Repr, BEq, Inhabited
structure Ebit_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ebit_R       where val : ℝ     deriving Inhabited

-- Von Neumann entropy: bits
structure VonNeumannEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure VonNeumannEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure VonNeumannEntropy_R where val : ℝ     deriving Inhabited

-- Quantum channel capacity: qubits per channel use
structure QuantumCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumCapacity_R where val : ℝ     deriving Inhabited

-- Entanglement entropy: bits
structure EntanglementEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure EntanglementEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntanglementEntropy_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Network and Latency Metrics
================================================================================================
-/
-- Latency: milliseconds
structure Latency_ms_F where val : Float deriving Repr, BEq, Inhabited
structure Latency_ms_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Latency_ms_R where val : ℝ     deriving Inhabited

-- Jitter: milliseconds
structure Jitter_ms_F  where val : Float deriving Repr, BEq, Inhabited
structure Jitter_ms_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Jitter_ms_R  where val : ℝ     deriving Inhabited

-- Round-trip time: milliseconds
structure RTT_ms_F     where val : Float deriving Repr, BEq, Inhabited
structure RTT_ms_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RTT_ms_R     where val : ℝ     deriving Inhabited

-- Throughput: Mbps (actual achieved rate)
structure Throughput_F where val : Float deriving Repr, BEq, Inhabited
structure Throughput_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Throughput_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Error Propagation & Measurement Helpers
================================================================================================
-/
-- Parametric Uncertainty Tracking with information context
structure InfoMeasured (α : Type) where
  value : α
  uncertainty : α
  sample_size : Option ℕ := none
  confidence_level : Option Float := none
  measurement_time : Option Second_F := none
  method : Option String := none
  source : Option String := none
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for entropy
structure MeasuredEntropy_F where
  entropy : ShannonEntropy_F
  entropy_error : ShannonEntropy_F
  sample_size : ℕ
  estimator : Option String := none  -- "ML", "Miller-Madow", etc.
  deriving Repr, BEq, Inhabited

-- Measurement with uncertainty for channel capacity
structure MeasuredCapacity_F where
  capacity : ChannelCapacity_F
  capacity_error : ChannelCapacity_F
  snr : Option SNR_dB_F := none
  bandwidth : Option Hertz_F := none
  deriving Repr, BEq, Inhabited

-- Error propagation for mutual information
def mutualInfoWithError_F (H_X : InfoMeasured ShannonEntropy_F)
    (H_Y : InfoMeasured ShannonEntropy_F) (H_XY : InfoMeasured JointEntropy_F)
    : InfoMeasured MutualInfo_F :=
  let I := H_X.value.val + H_Y.value.val - H_XY.value.val
  -- Error prop: δI = sqrt(δH_X² + δH_Y² + δH_XY²)
  let I_error := Float.sqrt (H_X.uncertainty.val^2 + H_Y.uncertainty.val^2 +
                             H_XY.uncertainty.val^2)
  { value := ⟨I⟩
    uncertainty := ⟨I_error⟩
    source := some "I(X;Y) = H(X) + H(Y) - H(X,Y)" }

-- Error propagation for compression ratio
def compressionRatioWithError_F (original : InfoMeasured Byte_F)
    (compressed : InfoMeasured Byte_F) : InfoMeasured CompressionRatio_F :=
  let ratio := original.value.val / compressed.value.val
  let relErrorOrig := original.uncertainty.val / original.value.val
  let relErrorComp := compressed.uncertainty.val / compressed.value.val
  let relError := Float.sqrt (relErrorOrig^2 + relErrorComp^2)
  { value := ⟨ratio⟩
    uncertainty := ⟨ratio * relError⟩
    source := some "Compression ratio calculation" }

/--
================================================================================================
   Validation & Range Checking Helpers
================================================================================================
-/

-- Entropy validation
def isValidEntropy_F (H : ShannonEntropy_F) : Bool :=
  H.val ≥ 0.0  -- Entropy must be non-negative

def isMaximalEntropy_F (H : ShannonEntropy_F) (n : ℕ) : Bool :=
  H.val ≤ Float.log (n.toFloat) / ln2_F  -- H ≤ log₂(n)

-- Probability validation for entropy calculations
def isValidProbability_F (p : Float) : Bool :=
  0.0 ≤ p && p ≤ 1.0

def isProbabilityDistribution_F (probs : Array Float) : Bool :=
  probs.all isValidProbability_F &&
  (probs.foldl (· + ·) 0.0 - 1.0).abs < 1e-10

-- Mutual information validation
def isValidMutualInfo_F (I : MutualInfo_F) : Bool :=
  I.val ≥ 0.0  -- MI must be non-negative

-- KL divergence validation
def isValidKLDivergence_F (D : KLDivergence_F) : Bool :=
  D.val ≥ 0.0  -- KL divergence must be non-negative

-- Channel capacity validation
def isValidChannelCapacity_F (C : ChannelCapacity_F) (input_size : ℕ) : Bool :=
  0.0 ≤ C.val && C.val ≤ Float.log (input_size.toFloat) / ln2_F

-- Error rate validation
def isValidErrorRate_F (ber : BER_F) : Bool :=
  0.0 ≤ ber.val && ber.val ≤ 1.0

def isAcceptableBER_F (ber : BER_F) : Bool :=
  ber.val < 1e-3  -- Typical threshold for acceptable communication

-- SNR validation
def isPositiveSNR_dB_F (snr : SNR_dB_F) : Bool :=
  snr.val > 0.0

def isHighSNR_dB_F (snr : SNR_dB_F) : Bool :=
  snr.val > 20.0  -- Generally considered good SNR

-- Compression validation
def isValidCompressionRatio_F (cr : CompressionRatio_F) : Bool :=
  cr.val ≥ 1.0  -- Compression ratio should be ≥ 1

def isGoodCompression_F (cr : CompressionRatio_F) : Bool :=
  cr.val > 2.0  -- 2:1 or better compression

-- Code rate validation
def isValidCodeRate_F (r : CodeRate_F) : Bool :=
  0.0 < r.val && r.val ≤ 1.0

-- Quantum validation
def isValidQuantumState_F (qubits : Qubit_F) : Bool :=
  qubits.val ≥ 0.0

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Bit/Byte conversions
def bitToByte_F (b : Bit_F) : Byte_F :=
  ⟨b.val / 8.0⟩

def byteToBit_F (B : Byte_F) : Bit_F :=
  ⟨B.val * 8.0⟩

def kilobitToBit_F (kb : Kilobit_F) : Bit_F :=
  ⟨kb.val * 1000.0⟩

def megabitToBit_F (mb : Megabit_F) : Bit_F :=
  ⟨mb.val * 1e6⟩

def gigabitToBit_F (gb : Gigabit_F) : Bit_F :=
  ⟨gb.val * 1e9⟩

-- Decimal prefix conversions (1000-based)
def kilobyteToByte_F (kB : Kilobyte_F) : Byte_F :=
  ⟨kB.val * 1000.0⟩

def megabyteToByte_F (MB : Megabyte_F) : Byte_F :=
  ⟨MB.val * 1e6⟩

def gigabyteToByte_F (GB : Gigabyte_F) : Byte_F :=
  ⟨GB.val * 1e9⟩

def terabyteToByte_F (TB : Terabyte_F) : Byte_F :=
  ⟨TB.val * 1e12⟩

-- Binary prefix conversions (1024-based)
def kibibyteToByte_F (KiB : Kibibyte_F) : Byte_F :=
  ⟨KiB.val * 1024.0⟩

def mebibyteToByte_F (MiB : Mebibyte_F) : Byte_F :=
  ⟨MiB.val * 1048576.0⟩

def gibibyteToByte_F (GiB : Gibibyte_F) : Byte_F :=
  ⟨GiB.val * 1073741824.0⟩

def tebibyteToByte_F (TiB : Tebibyte_F) : Byte_F :=
  ⟨TiB.val * 1099511627776.0⟩

-- Decimal vs Binary conversion
def kilobyteToKibibyte_F (kB : Kilobyte_F) : Kibibyte_F :=
  ⟨kB.val * 1000.0 / 1024.0⟩

def kibibyteToKilobyte_F (KiB : Kibibyte_F) : Kilobyte_F :=
  ⟨KiB.val * 1024.0 / 1000.0⟩

-- Information unit conversions
def bitToNat_F (b : Bit_F) : Nat_F :=
  ⟨b.val * ln2_F⟩  -- Convert bits to nats

def natToBit_F (n : Nat_F) : Bit_F :=
  ⟨n.val / ln2_F⟩  -- Convert nats to bits

def bitToDit_F (b : Bit_F) : Dit_F :=
  ⟨b.val * log10_2_F⟩  -- Convert bits to dits

def ditToBit_F (d : Dit_F) : Bit_F :=
  ⟨d.val * log2_10_F⟩  -- Convert dits to bits

-- Data rate conversions
def bpsToKbps_F (bps : BitsPerSec_F) : Kbps_F :=
  ⟨bps.val / 1000.0⟩

def kbpsToMbps_F (kbps : Kbps_F) : Mbps_F :=
  ⟨kbps.val / 1000.0⟩

def mbpsToGbps_F (mbps : Mbps_F) : Gbps_F :=
  ⟨mbps.val / 1000.0⟩

def bytesPerSecToBitsPerSec_F (Bps : BytesPerSec_F) : BitsPerSec_F :=
  ⟨Bps.val * 8.0⟩

def bitsPerSecToBytesPerSec_F (bps : BitsPerSec_F) : BytesPerSec_F :=
  ⟨bps.val / 8.0⟩

-- SNR conversions
def snrLinearToDb_F (snr : SNR_F) : SNR_dB_F :=
  ⟨10.0 * Float.log snr.val / Float.log 10.0⟩

def snrDbToLinear_F (snr_db : SNR_dB_F) : SNR_F :=
  ⟨10.0 ^ (snr_db.val / 10.0)⟩

-- Latency conversions
def msToSeconds_F (ms : Latency_ms_F) : Second_F :=
  ⟨ms.val / 1000.0⟩

def secondsToMs_F (s : Second_F) : Latency_ms_F :=
  ⟨s.val * 1000.0⟩

/--
================================================================================================
   Common Information Theory Calculations
================================================================================================
-/

-- Shannon entropy from probability distribution
def shannonEntropy_F (probs : Array Float) : ShannonEntropy_F :=
  let H := probs.foldl (init := 0.0) fun acc p =>
    if p > 0.0 then acc - p * Float.log p / ln2_F else acc
  ⟨H⟩

-- Binary entropy function
def binaryEntropy_F (p : Float) : ShannonEntropy_F :=
  if p ≤ 0.0 || p ≥ 1.0 then
    ⟨0.0⟩
  else
    ⟨-p * Float.log p / ln2_F - (1.0 - p) * Float.log (1.0 - p) / ln2_F⟩

-- Joint entropy from joint probability distribution
def jointEntropy_F (joint_probs : Array (Array Float)) : JointEntropy_F :=
  let H := joint_probs.foldl (init := 0.0) fun acc row =>
    row.foldl (init := acc) fun acc2 p =>
      if p > 0.0 then acc2 - p * Float.log p / ln2_F else acc2
  ⟨H⟩

-- Conditional entropy H(Y|X) = H(X,Y) - H(X)
def conditionalEntropy_F (H_XY : JointEntropy_F) (H_X : ShannonEntropy_F)
    : ConditionalEntropy_F :=
  ⟨H_XY.val - H_X.val⟩

-- Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y)
def mutualInformation_F (H_X : ShannonEntropy_F) (H_Y : ShannonEntropy_F)
    (H_XY : JointEntropy_F) : MutualInfo_F :=
  ⟨H_X.val + H_Y.val - H_XY.val⟩

-- KL divergence D(P||Q)
def klDivergence_F (p : Array Float) (q : Array Float) : KLDivergence_F :=
  if p.size ≠ q.size then
    ⟨0.0⟩
  else
    let D := (p.zip q).foldl (init := 0.0) fun acc (pi, qi) =>
      if pi > 0.0 && qi > 0.0 then
        acc + pi * Float.log (pi / qi) / ln2_F
      else if pi > 0.0 && qi == 0.0 then
        1e10  -- Infinity approximation
      else
        acc
    ⟨D⟩

-- Cross entropy H(P,Q) = -Σ p(x) log q(x)
def crossEntropy_F (p : Array Float) (q : Array Float) : CrossEntropy_F :=
  if p.size ≠ q.size then
    ⟨0.0⟩
  else
    let H := (p.zip q).foldl (init := 0.0) fun acc (pi, qi) =>
      if pi > 0.0 && qi > 0.0 then
        acc - pi * Float.log qi / ln2_F
      else if pi > 0.0 && qi == 0.0 then
        1e10  -- Infinity approximation
      else
        acc
    ⟨H⟩

-- Rényi entropy of order α
def renyiEntropy_F (probs : Array Float) (alpha : Float) : RenyiEntropy_F :=
  if alpha == 1.0 then
    -- Limit case: Shannon entropy
    let H := shannonEntropy_F probs
    { val := H.val, order := alpha }
  else if alpha == 0.0 then
    -- Hartley entropy: log(support size)
    let support := probs.filter (· > 0.0) |>.size
    { val := Float.log support.toFloat / ln2_F, order := alpha }
  else
    let sum := probs.foldl (init := 0.0) fun acc p =>
      if p > 0.0 then acc + p^alpha else acc
    { val := Float.log sum / ((1.0 - alpha) * ln2_F), order := alpha }

-- Channel capacity (binary symmetric channel)
def bscCapacity_F (p : Float) : ChannelCapacity_F :=
  let H := binaryEntropy_F p
  ⟨1.0 - H.val⟩

-- Channel capacity (AWGN channel) - Shannon-Hartley
def shannonCapacity_F (bandwidth : Hertz_F) (snr : SNR_F) : BitsPerSec_F :=
  ⟨bandwidth.val * Float.log (1.0 + snr.val) / ln2_F⟩

-- Spectral efficiency
def spectralEfficiency_F (rate : BitsPerSec_F) (bandwidth : Hertz_F)
    : SpectralEfficiency_F :=
  ⟨rate.val / bandwidth.val⟩

-- Hamming distance
def hammingDistance_F (x : Array Bool) (y : Array Bool) : ℕ :=
  if x.size ≠ y.size then
    0
  else
    (x.zip y).foldl (init := 0) fun acc (xi, yi) =>
      if xi ≠ yi then acc + 1 else acc

-- Hamming weight (number of 1s)
def hammingWeight_F (x : Array Bool) : ℕ :=
  x.foldl (init := 0) fun acc xi =>
    if xi then acc + 1 else acc

-- Code rate calculation
def codeRate_F (k : ℕ) (n : ℕ) : CodeRate_F :=
  ⟨k.toFloat / n.toFloat⟩

-- Compression ratio
def compressionRatio_F (original_size : Byte_F) (compressed_size : Byte_F)
    : CompressionRatio_F :=
  if compressed_size.val > 0.0 then
    ⟨original_size.val / compressed_size.val⟩
  else
    ⟨1e10⟩  -- Infinity approximation

-- Compression factor (space savings)
def compressionFactor_F (original_size : Byte_F) (compressed_size : Byte_F)
    : CompressionFactor_F :=
  ⟨1.0 - compressed_size.val / original_size.val⟩

-- Entropy rate (for Markov chains)
def entropyRate_F (transition_probs : Array (Array Float))
    (stationary_dist : Array Float) : ShannonEntropy_F :=
  let H_rate := (transition_probs.zip stationary_dist).foldl (init := 0.0)
    fun acc (row, pi) =>
      let row_entropy := row.foldl (init := 0.0) fun acc2 p =>
        if p > 0.0 then acc2 - p * Float.log p / ln2_F else acc2
      acc + pi * row_entropy
  ⟨H_rate⟩

-- Huffman coding average length (lower bound)
def huffmanLowerBound_F (probs : Array Float) : Bit_F :=
  let H := shannonEntropy_F probs
  ⟨H.val⟩  -- Average length ≥ H

-- Arithmetic coding efficiency
def arithmeticCodingLength_F (probs : Array Float) (sequence_length : ℕ)
    : Bit_F :=
  let H := shannonEntropy_F probs
  ⟨sequence_length.toFloat * H.val + 2.0⟩  -- H + overhead

-- Lempel-Ziv complexity (normalized)
def lempelZivComplexity_F (sequence : Array Bool) : LZComplexity_F :=
  -- Simplified LZ complexity calculation
  let n := sequence.size.toFloat
  let c := Float.sqrt n  -- Simplified approximation
  ⟨c / (n / Float.log n)⟩

-- Von Neumann entropy for quantum density matrix (simplified)
def vonNeumannEntropy_F (eigenvalues : Array Float) : VonNeumannEntropy_F :=
  let S := eigenvalues.foldl (init := 0.0) fun acc lambda =>
    if lambda > 0.0 then acc - lambda * Float.log lambda / ln2_F else acc
  ⟨S⟩

-- Quantum relative entropy
def quantumRelativeEntropy_F (eigenvals_rho : Array Float)
    (eigenvals_sigma : Array Float) : KLDivergence_F :=
  klDivergence_F eigenvals_rho eigenvals_sigma

-- Transfer entropy (simplified)
def transferEntropy_F (H_future_given_past : ConditionalEntropy_F)
    (H_future_given_both : ConditionalEntropy_F) : Bit_F :=
  ⟨H_future_given_past.val - H_future_given_both.val⟩

-- Normalized compression distance (NCD)
def normalizedCompressionDistance_F (C_x : KolmogorovComplexity_F)
    (C_y : KolmogorovComplexity_F) (C_xy : KolmogorovComplexity_F) : Float :=
  let max_C := max C_x.val C_y.val
  if max_C > 0.0 then
    (C_xy.val - min C_x.val C_y.val) / max_C
  else
    0.0

-- Fisher information (simplified for single parameter)
def fisherInformation_F (log_likelihood_derivatives : Array Float)
    : Bit_F :=
  let I := log_likelihood_derivatives.foldl (init := 0.0) fun acc d =>
    acc + d^2
  ⟨I / log_likelihood_derivatives.size.toFloat⟩

-- Minimum description length
def mdl_F (model_complexity : Bit_F) (data_given_model : Bit_F) : Bit_F :=
  ⟨model_complexity.val + data_given_model.val⟩

-- Akaike information criterion
def aic_F (log_likelihood : Float) (k : ℕ) : Float :=
  2.0 * k.toFloat - 2.0 * log_likelihood

-- Bayesian information criterion
def bic_F (log_likelihood : Float) (k : ℕ) (n : ℕ) : Float :=
  k.toFloat * Float.log n.toFloat - 2.0 * log_likelihood

end Units.Information
