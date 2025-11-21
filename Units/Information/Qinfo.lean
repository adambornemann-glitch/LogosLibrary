-- Qinfo.lean        -- Quantum information units and calculations
import LogosLibrary.Units.Core.SI
import LogosLibrary.Units.Information.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

namespace Units.QuantumInfo

open Units.SI Units.Information

/-
================================================================================
QUANTUM INFORMATION UNITS LIBRARY
================================================================================

This module provides type-safe units for quantum information theory,
quantum computing, and quantum communication. Following the triple-type
architecture for maximum flexibility without type conversion friction.

## COVERAGE
- Quantum states (qubits, qudits, continuous variables)
- Entanglement measures (ebits, entanglement entropy, negativity)
- State quality (fidelity, purity, trace distance)
- Decoherence (T1, T2, T2*, dephasing rates)
- Gate metrics (gate time, gate fidelity, CNOT count)
- Circuit complexity (quantum volume, circuit depth)
- Topological order (anyons, topological entropy)
- Quantum channels (capacity, coherent information)
- Error correction (logical error rate, threshold)
- NISQ metrics (quantum supremacy, quantum advantage)

## USAGE PATTERNS
Float: Experimental measurements, gate calibration, real-time error tracking,
NISQ device characterization, quantum process tomography, dynamical decoupling,
noise spectroscopy, benchmarking protocols

ℚ: Exact quantum circuits, stabilizer codes, Clifford group operations,
graph states, discrete quantum walks, quantum algorithms with rational phases,
exact error models, syndrome decoding

ℝ: Continuous variable quantum info, Gaussian states, quantum field theory,
quantum thermodynamics, open quantum systems, master equations,
quantum optimal control, quantum metrology bounds
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/--
================================================================================================
   Mathematical Constants for Quantum Information
================================================================================================
-/
def sqrt2_F : Float := 1.41421356237309504880
def sqrt_half_F : Float := 0.70710678118654752440
def ln2_F : Float := 0.693147180559945309417
def pi_F : Float := 3.14159265358979323846
def e_F : Float := 2.71828182845904523536

/--
================================================================================================
   Basic Quantum Information Units
================================================================================================
-/
-- Qubit: quantum bit (2-level system)
structure Qubit_F      where val : Float deriving Repr, BEq, Inhabited
structure Qubit_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Qubit_R      where val : ℝ     deriving Inhabited

-- Qudit: d-dimensional quantum system
structure Qudit_F where
  val : Float
  dimension : ℕ  -- d-level system
  deriving Repr, BEq, Inhabited

structure Qudit_Q where
  val : ℚ
  dimension : ℕ
  deriving Repr, BEq, DecidableEq, Inhabited

structure Qudit_R where
  val : ℝ
  dimension : ℕ
  deriving Inhabited

-- Qutrit: 3-level quantum system
structure Qutrit_F     where val : Float deriving Repr, BEq, Inhabited
structure Qutrit_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Qutrit_R     where val : ℝ     deriving Inhabited

-- Continuous variable mode
structure CVMode_F     where val : Float deriving Repr, BEq, Inhabited
structure CVMode_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CVMode_R     where val : ℝ     deriving Inhabited

/--
================================================================================================
   Entanglement Measures
================================================================================================
-/
-- Ebit: maximally entangled qubit pair (Bell state)
structure Ebit_F       where val : Float deriving Repr, BEq, Inhabited
structure Ebit_Q       where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Ebit_R       where val : ℝ     deriving Inhabited

-- Entanglement entropy (von Neumann entropy of reduced state)
structure EntanglementEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure EntanglementEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntanglementEntropy_R where val : ℝ     deriving Inhabited

-- Entanglement of formation
structure EntanglementFormation_F where val : Float deriving Repr, BEq, Inhabited
structure EntanglementFormation_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntanglementFormation_R where val : ℝ     deriving Inhabited

-- Distillable entanglement
structure DistillableEntanglement_F where val : Float deriving Repr, BEq, Inhabited
structure DistillableEntanglement_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DistillableEntanglement_R where val : ℝ     deriving Inhabited

-- Logarithmic negativity
structure LogNegativity_F where val : Float deriving Repr, BEq, Inhabited
structure LogNegativity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogNegativity_R where val : ℝ     deriving Inhabited

-- Concurrence (for 2-qubit states)
structure Concurrence_F where val : Float deriving Repr, BEq, Inhabited
structure Concurrence_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Concurrence_R where val : ℝ     deriving Inhabited

-- Tangle (squared concurrence)
structure Tangle_F     where val : Float deriving Repr, BEq, Inhabited
structure Tangle_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Tangle_R     where val : ℝ     deriving Inhabited

-- Schmidt rank
structure SchmidtRank  where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

/--
================================================================================================
   State Quality Measures
================================================================================================
-/
-- Fidelity: overlap between quantum states
structure Fidelity_F   where val : Float deriving Repr, BEq, Inhabited
structure Fidelity_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Fidelity_R   where val : ℝ     deriving Inhabited

-- Purity: Tr(ρ²)
structure Purity_F     where val : Float deriving Repr, BEq, Inhabited
structure Purity_Q     where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure Purity_R     where val : ℝ     deriving Inhabited

-- Trace distance
structure TraceDistance_F where val : Float deriving Repr, BEq, Inhabited
structure TraceDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TraceDistance_R where val : ℝ     deriving Inhabited

-- Bures distance
structure BuresDistance_F where val : Float deriving Repr, BEq, Inhabited
structure BuresDistance_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BuresDistance_R where val : ℝ     deriving Inhabited

-- Relative entropy (quantum)
structure RelativeEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure RelativeEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure RelativeEntropy_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Decoherence and Coherence Times
================================================================================================
-/
-- T1: longitudinal relaxation time (energy relaxation)
structure T1_Time_F    where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure T1_Time_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure T1_Time_R    where val : ℝ     deriving Inhabited

-- T2: transverse relaxation time (dephasing)
structure T2_Time_F    where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure T2_Time_Q    where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure T2_Time_R    where val : ℝ     deriving Inhabited

-- T2*: inhomogeneous dephasing time
structure T2Star_Time_F where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure T2Star_Time_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure T2Star_Time_R where val : ℝ     deriving Inhabited

-- T2 echo: spin echo coherence time
structure T2Echo_Time_F where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure T2Echo_Time_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure T2Echo_Time_R where val : ℝ     deriving Inhabited

-- Coherence time (general)
structure CoherenceTime_F where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure CoherenceTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoherenceTime_R where val : ℝ     deriving Inhabited

-- Dephasing rate: 1/T2
structure DephasingRate_F where val : Float deriving Repr, BEq, Inhabited  -- MHz
structure DephasingRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DephasingRate_R where val : ℝ     deriving Inhabited

-- Decay rate: 1/T1
structure DecayRate_F  where val : Float deriving Repr, BEq, Inhabited  -- MHz
structure DecayRate_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure DecayRate_R  where val : ℝ     deriving Inhabited

/--
================================================================================================
   Gate and Circuit Metrics
================================================================================================
-/
-- Gate time: duration of quantum gate
structure GateTime_F   where val : Float deriving Repr, BEq, Inhabited  -- nanoseconds
structure GateTime_Q   where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GateTime_R   where val : ℝ     deriving Inhabited

-- Gate fidelity
structure GateFidelity_F where val : Float deriving Repr, BEq, Inhabited
structure GateFidelity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GateFidelity_R where val : ℝ     deriving Inhabited

-- Gate error rate
structure GateError_F  where val : Float deriving Repr, BEq, Inhabited
structure GateError_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure GateError_R  where val : ℝ     deriving Inhabited

-- CNOT count: number of two-qubit gates
structure CNOTCount    where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- T gate count (for fault-tolerant computing)
structure TGateCount   where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- Clifford gate count
structure CliffordCount where val : ℕ    deriving Repr, BEq, DecidableEq, Inhabited

-- Circuit depth
structure CircuitDepth where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- Circuit width (number of qubits)
structure CircuitWidth where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- Two-qubit gate depth
structure TwoQubitDepth where val : ℕ    deriving Repr, BEq, DecidableEq, Inhabited

/--
================================================================================================
   Quantum Volume and Complexity
================================================================================================
-/
-- Quantum volume: 2^n where n is largest random circuit achievable
structure QuantumVolume_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumVolume_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumVolume_R where val : ℝ     deriving Inhabited

-- Algorithmic qubits: effective qubits for algorithms
structure AlgorithmicQubits where val : ℕ deriving Repr, BEq, DecidableEq, Inhabited

-- Layer fidelity: fidelity per circuit layer
structure LayerFidelity_F where val : Float deriving Repr, BEq, Inhabited
structure LayerFidelity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LayerFidelity_R where val : ℝ     deriving Inhabited

-- CLOPS: Circuit Layer Operations Per Second
structure CLOPS_F      where val : Float deriving Repr, BEq, Inhabited
structure CLOPS_Q      where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CLOPS_R      where val : ℝ     deriving Inhabited

/--
================================================================================================
   Topological Quantum Order
================================================================================================
-/
-- Topological entanglement entropy
structure TopologicalEntropy_F where val : Float deriving Repr, BEq, Inhabited
structure TopologicalEntropy_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure TopologicalEntropy_R where val : ℝ     deriving Inhabited

-- Anyon type (fusion rules encoded)
structure AnyonType where
  label : String  -- e.g., "σ", "ψ", "1"
  dimension : Float  -- quantum dimension
  deriving Repr, BEq, Inhabited

-- Total quantum dimension
structure QuantumDimension_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumDimension_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumDimension_R where val : ℝ     deriving Inhabited

-- Chern number
structure ChernNumber  where val : ℤ     deriving Repr, BEq, DecidableEq, Inhabited

-- Berry phase
structure BerryPhase_F where val : Float deriving Repr, BEq, Inhabited
structure BerryPhase_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure BerryPhase_R where val : ℝ     deriving Inhabited

-- String order parameter
structure StringOrder_F where val : Float deriving Repr, BEq, Inhabited
structure StringOrder_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure StringOrder_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Quantum Error Correction
================================================================================================
-/
-- Logical qubit
structure LogicalQubit_F where val : Float deriving Repr, BEq, Inhabited
structure LogicalQubit_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogicalQubit_R where val : ℝ     deriving Inhabited

-- Physical qubits per logical qubit
structure PhysicalPerLogical where val : ℕ deriving Repr, BEq, DecidableEq, Inhabited

-- Code distance
structure CodeDistance where val : ℕ     deriving Repr, BEq, DecidableEq, Inhabited

-- Logical error rate
structure LogicalErrorRate_F where val : Float deriving Repr, BEq, Inhabited
structure LogicalErrorRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure LogicalErrorRate_R where val : ℝ     deriving Inhabited

-- Threshold error rate
structure ThresholdRate_F where val : Float deriving Repr, BEq, Inhabited
structure ThresholdRate_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ThresholdRate_R where val : ℝ     deriving Inhabited

-- Syndrome extraction time
structure SyndromeTime_F where val : Float deriving Repr, BEq, Inhabited  -- microseconds
structure SyndromeTime_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SyndromeTime_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Quantum Communication
================================================================================================
-/
-- Quantum channel capacity
structure QuantumCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumCapacity_R where val : ℝ     deriving Inhabited

-- Classical capacity of quantum channel
structure ClassicalCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure ClassicalCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ClassicalCapacity_R where val : ℝ     deriving Inhabited

-- Entanglement-assisted capacity
structure EntAssistedCapacity_F where val : Float deriving Repr, BEq, Inhabited
structure EntAssistedCapacity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure EntAssistedCapacity_R where val : ℝ     deriving Inhabited

-- Coherent information
structure CoherentInfo_F where val : Float deriving Repr, BEq, Inhabited
structure CoherentInfo_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure CoherentInfo_R where val : ℝ     deriving Inhabited

-- Quantum discord
structure QuantumDiscord_F where val : Float deriving Repr, BEq, Inhabited
structure QuantumDiscord_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QuantumDiscord_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Measurement and Readout
================================================================================================
-/
-- Measurement fidelity
structure MeasurementFidelity_F where val : Float deriving Repr, BEq, Inhabited
structure MeasurementFidelity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure MeasurementFidelity_R where val : ℝ     deriving Inhabited

-- Readout error
structure ReadoutError_F where val : Float deriving Repr, BEq, Inhabited
structure ReadoutError_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure ReadoutError_R where val : ℝ     deriving Inhabited

-- SPAM error (State Preparation And Measurement)
structure SPAMError_F  where val : Float deriving Repr, BEq, Inhabited
structure SPAMError_Q  where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure SPAMError_R  where val : ℝ     deriving Inhabited

-- QND measurement fidelity (Quantum Non-Demolition)
structure QNDFidelity_F where val : Float deriving Repr, BEq, Inhabited
structure QNDFidelity_Q where val : ℚ     deriving Repr, BEq, DecidableEq, Inhabited
structure QNDFidelity_R where val : ℝ     deriving Inhabited

/--
================================================================================================
   Validation Helpers
================================================================================================
-/

-- Fidelity must be between 0 and 1
def isValidFidelity_F (f : Fidelity_F) : Bool :=
  0.0 ≤ f.val && f.val ≤ 1.0

-- Purity must be between 1/d and 1 for d-dimensional system
def isValidPurity_F (p : Purity_F) (d : ℕ) : Bool :=
  1.0 / d.toFloat ≤ p.val && p.val ≤ 1.0

-- Concurrence must be between 0 and 1
def isValidConcurrence_F (c : Concurrence_F) : Bool :=
  0.0 ≤ c.val && c.val ≤ 1.0

-- Entanglement entropy bounded by log(d) for d-dimensional subsystem
def isValidEntanglementEntropy_F (S : EntanglementEntropy_F) (d : ℕ) : Bool :=
  0.0 ≤ S.val && S.val ≤ Float.log d.toFloat / ln2_F

-- T2 ≤ 2*T1 (fundamental limit)
def isValidT2_F (t1 : T1_Time_F) (t2 : T2_Time_F) : Bool :=
  t2.val ≤ 2.0 * t1.val

-- T2* ≤ T2 ≤ T2_echo
def isValidDephasingHierarchy_F (t2star : T2Star_Time_F) (t2 : T2_Time_F)
    (t2echo : T2Echo_Time_F) : Bool :=
  t2star.val ≤ t2.val && t2.val ≤ t2echo.val

-- Gate error rate validation
def isValidGateError_F (e : GateError_F) : Bool :=
  0.0 ≤ e.val && e.val ≤ 1.0

-- Quantum volume must be power of 2
def isValidQuantumVolume_F (qv : QuantumVolume_F) : Bool :=
  let log2_qv := Float.log qv.val / Float.log 2.0
  (log2_qv - log2_qv.round).abs < 1e-10

-- Trace distance between 0 and 1
def isValidTraceDistance_F (d : TraceDistance_F) : Bool :=
  0.0 ≤ d.val && d.val ≤ 1.0

-- Error rate below threshold
def isBelowThreshold_F (error : GateError_F) (threshold : ThresholdRate_F) : Bool :=
  error.val < threshold.val

-- Check if state is entangled (negativity > 0)
def isEntangled_F (neg : LogNegativity_F) : Bool :=
  neg.val > 0.0

-- Check if state is maximally entangled
def isMaximallyEntangled_F (S : EntanglementEntropy_F) (d : ℕ) : Bool :=
  (S.val - Float.log d.toFloat / ln2_F).abs < 1e-10

/--
================================================================================================
   Unit Conversions
================================================================================================
-/

-- Qubit to qudit conversions
def qubitToQudit_F (q : Qubit_F) : Qudit_F :=
  { val := q.val, dimension := 2 }

def qutritToQudit_F (q : Qutrit_F) : Qudit_F :=
  { val := q.val, dimension := 3 }

-- Time conversions
def nsToUs_F (ns : GateTime_F) : Float :=
  ns.val / 1000.0

def usToMs_F (us : T1_Time_F) : Millisecond_F :=
  ⟨us.val / 1000.0⟩

def msToUs_F (ms : Millisecond_F) : T1_Time_F :=
  ⟨ms.val * 1000.0⟩

-- Rate conversions
def dephasingRateFromT2_F (t2 : T2_Time_F) : DephasingRate_F :=
  ⟨1.0 / t2.val⟩  -- MHz if t2 in microseconds

def decayRateFromT1_F (t1 : T1_Time_F) : DecayRate_F :=
  ⟨1.0 / t1.val⟩  -- MHz if t1 in microseconds

-- Fidelity to error rate
def fidelityToError_F (f : GateFidelity_F) : GateError_F :=
  ⟨1.0 - f.val⟩

def errorToFidelity_F (e : GateError_F) : GateFidelity_F :=
  ⟨1.0 - e.val⟩

-- Purity to mixedness
def purityToMixedness_F (p : Purity_F) (d : ℕ) : Float :=
  (1.0 - p.val) * d.toFloat / (d.toFloat - 1.0)

-- Concurrence to entanglement of formation (2-qubit)
def concurrenceToEoF_F (c : Concurrence_F) : EntanglementFormation_F :=
  let h := (1.0 + Float.sqrt (1.0 - c.val^2)) / 2.0
  let S := if h > 0.0 && h < 1.0 then
    -h * Float.log h / ln2_F - (1.0 - h) * Float.log (1.0 - h) / ln2_F
  else 0.0
  ⟨S⟩

-- Tangle from concurrence
def concurrenceToTangle_F (c : Concurrence_F) : Tangle_F :=
  ⟨c.val^2⟩

def tangleToConcurrence_F (t : Tangle_F) : Concurrence_F :=
  ⟨Float.sqrt t.val⟩

-- Bures to trace distance approximation
def buresToTraceApprox_F (b : BuresDistance_F) : TraceDistance_F :=
  ⟨Float.sqrt 2.0 * b.val⟩  -- Upper bound

-- Fidelity to Bures distance
def fidelityToBures_F (f : Fidelity_F) : BuresDistance_F :=
  ⟨Float.sqrt (2.0 * (1.0 - Float.sqrt f.val))⟩

-- Quantum volume to effective qubits
def quantumVolumeToQubits_F (qv : QuantumVolume_F) : ℕ :=
  (Float.log qv.val / Float.log 2.0).toUInt64.toNat

/--
================================================================================================
   Common Quantum Information Calculations
================================================================================================
-/

-- Von Neumann entropy from eigenvalues
def vonNeumannEntropy_F (eigenvalues : Array Float) : EntanglementEntropy_F :=
  let S := eigenvalues.foldl (init := 0.0) fun acc lambda =>
    if lambda > 1e-12 then acc - lambda * Float.log lambda / ln2_F else acc
  ⟨S⟩

-- Purity from density matrix eigenvalues
def purityFromEigenvalues_F (eigenvalues : Array Float) : Purity_F :=
  let p := eigenvalues.foldl (init := 0.0) fun acc lambda => acc + lambda^2
  ⟨p⟩

-- Linear entropy from purity
def linearEntropy_F (p : Purity_F) (d : ℕ) : Float :=
  d.toFloat / (d.toFloat - 1.0) * (1.0 - p.val)

-- Participation ratio
def participationRatio_F (amplitudes : Array Float) : Float :=
  let sum2 := amplitudes.foldl (init := 0.0) fun acc a => acc + a^2
  let sum4 := amplitudes.foldl (init := 0.0) fun acc a => acc + a^4
  if sum4 > 0.0 then sum2^2 / sum4 else 0.0

-- Schmidt decomposition entropy
def schmidtEntropy_F (schmidt_coeffs : Array Float) : EntanglementEntropy_F :=
  vonNeumannEntropy_F schmidt_coeffs

-- Negativity from partial transpose eigenvalues
def negativity_F (pt_eigenvalues : Array Float) : Float :=
  pt_eigenvalues.foldl (init := 0.0) fun acc lambda =>
    if lambda < 0.0 then acc - lambda else acc

-- Logarithmic negativity
def logNegativity_F (pt_eigenvalues : Array Float) : LogNegativity_F :=
  let neg := negativity_F pt_eigenvalues
  ⟨Float.log (1.0 + 2.0 * neg) / ln2_F⟩

-- Mutual information for quantum states
def quantumMutualInfo_F (S_A : EntanglementEntropy_F) (S_B : EntanglementEntropy_F)
    (S_AB : EntanglementEntropy_F) : MutualInfo_F :=
  ⟨S_A.val + S_B.val - S_AB.val⟩

-- Coherent information
def coherentInfo_F (S_B : EntanglementEntropy_F) (S_AB : EntanglementEntropy_F)
    : CoherentInfo_F :=
  ⟨S_B.val - S_AB.val⟩

-- Average gate fidelity from process matrix
def averageGateFidelity_F (process_fidelity : Float) (d : ℕ) : GateFidelity_F :=
  ⟨(process_fidelity * d.toFloat + 1.0) / (d.toFloat + 1.0)⟩

-- Diamond distance from average gate fidelity (approximate)
def diamondDistance_F (avg_fidelity : GateFidelity_F) (d : ℕ) : Float :=
  Float.sqrt (d.toFloat * (d.toFloat + 1.0) * (1.0 - avg_fidelity.val))

-- Randomized benchmarking decay
def rbDecay_F (sequence_length : ℕ) (error_per_gate : GateError_F) : GateFidelity_F :=
  ⟨(1.0 - error_per_gate.val) ^ sequence_length.toFloat⟩

-- T1 limited fidelity
def t1LimitedFidelity_F (gate_time : GateTime_F) (t1 : T1_Time_F) : GateFidelity_F :=
  let t_us := nsToUs_F gate_time
  ⟨Float.exp (-t_us / t1.val)⟩

-- T2 limited fidelity
def t2LimitedFidelity_F (gate_time : GateTime_F) (t2 : T2_Time_F) : GateFidelity_F :=
  let t_us := nsToUs_F gate_time
  ⟨Float.exp (-t_us / t2.val)⟩

-- Combined decoherence fidelity
def decoherenceFidelity_F (gate_time : GateTime_F) (t1 : T1_Time_F) (t2 : T2_Time_F)
    : GateFidelity_F :=
  let f1 := t1LimitedFidelity_F gate_time t1
  let f2 := t2LimitedFidelity_F gate_time t2
  ⟨f1.val * f2.val⟩

-- Quantum volume calculation
def quantumVolume_F (width : CircuitWidth) (depth : CircuitDepth)
    (layer_fidelity : LayerFidelity_F) : QuantumVolume_F :=
  if layer_fidelity.val ^ depth.val.toFloat > 2.0/3.0 then
    ⟨2.0 ^ (min width.val depth.val).toFloat⟩
  else
    ⟨1.0⟩

-- CNOT cost for arbitrary two-qubit gate
def cnotCost_F (gate_type : String) : CNOTCount :=
  match gate_type with
  | "CZ" => ⟨1⟩       -- CZ needs 1 CNOT
  | "iSWAP" => ⟨2⟩    -- iSWAP needs 2 CNOTs
  | "SWAP" => ⟨3⟩     -- SWAP needs 3 CNOTs
  | "Controlled-U" => ⟨2⟩  -- Generic controlled unitary
  | _ => ⟨1⟩

-- Surface code logical error rate
def surfaceCodeError_F (physical_error : GateError_F) (code_distance : CodeDistance)
    : LogicalErrorRate_F :=
  let d := code_distance.val.toFloat
  let p := physical_error.val
  ⟨0.1 * (100.0 * p) ^ ((d + 1.0) / 2.0)⟩  -- Approximate formula

-- Threshold calculation
def isAboveThreshold_F (physical_error : GateError_F) : Bool :=
  physical_error.val < 0.01  -- Typical surface code threshold

-- Topological entanglement entropy (Kitaev-Preskill)
def topologicalEntropy_F (total_entropy : EntanglementEntropy_F)
    (boundary_entropy : EntanglementEntropy_F) : TopologicalEntropy_F :=
  ⟨total_entropy.val - boundary_entropy.val⟩

-- Quantum dimension from fusion rules
def quantumDimension_F (anyon : AnyonType) : QuantumDimension_F :=
  ⟨anyon.dimension⟩

-- Total quantum dimension for anyon model
def totalQuantumDimension_F (anyons : Array AnyonType) : QuantumDimension_F :=
  let D_squared := anyons.foldl (init := 0.0) fun acc a => acc + a.dimension^2
  ⟨Float.sqrt D_squared⟩

-- Berry phase from path integral
def berryPhase_F (path_length : Float) (curvature : Float) : BerryPhase_F :=
  ⟨path_length * curvature⟩

-- CLOPS calculation
def clops_F (layer_time : GateTime_F) (num_qubits : CircuitWidth)
    (update_time : Millisecond_F) : CLOPS_F :=
  let total_time := nsToUs_F layer_time / 1000.0 + update_time.val
  ⟨1000.0 / total_time⟩  -- Layers per second

-- Quantum advantage metric
def quantumAdvantage_F (quantum_time : Second_F) (classical_time : Second_F) : Float :=
  classical_time.val / quantum_time.val

-- Entangling gate quality
def entanglingQuality_F (cnot_fidelity : GateFidelity_F) (cnot_time : GateTime_F)
    (coherence : CoherenceTime_F) : Float :=
  cnot_fidelity.val * Float.exp (-(nsToUs_F cnot_time) / coherence.val)

-- SPAM-corrected measurement
def spamCorrectedValue_F (raw_value : Float) (spam_error : SPAMError_F) : Float :=
  raw_value / (1.0 - 2.0 * spam_error.val)

-- Readout mitigation matrix
def readoutMitigation_F (p0given0 : Float) (p1given1 : Float) : Array (Array Float) :=
  #[#[p0given0, 1.0 - p1given1],
    #[1.0 - p0given0, p1given1]]

-- ZNE extrapolation (Zero Noise Extrapolation)
def zneExtrapolation_F (values : Array Float) (noise_factors : Array Float) : Float :=
  -- Linear extrapolation to zero noise
  if values.size ≥ 2 && noise_factors.size ≥ 2 then
    let x1 := noise_factors[0]!
    let x2 := noise_factors[1]!
    let y1 := values[0]!
    let y2 := values[1]!
    let slope := (y2 - y1) / (x2 - x1)
    y1 - slope * x1  -- Extrapolate to x=0
  else
    values[0]!

end Units.QuantumInfo
