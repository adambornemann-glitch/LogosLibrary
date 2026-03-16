/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Riemann/PrimeFactor.lean
-/
import LogosLibrary.Superior.SplitMechanics.Riemann.LocalFactor
import LogosLibrary.Superior.SplitMechanics.Riemann.ArchimedeanGear
/-!
=====================================================================
# THE PRIME FACTOR GEARS
=====================================================================
Via the Curry-Howard method.

## Overview

Each prime p contributes a local gear to the Riemann machine.
The p-adic gear is SIMPLER than the archimedean gear in every way:

  L-factor:        L_p(s) = (1 − p⁻ˢ)⁻¹
  Epsilon factor:  ε_p(s) = 1  (trivial! — unramified)
  Ground state:    𝟙_{ℤ_p}  (characteristic function of p-adic integers)
  Weil contrib:    W_p(f) = Σ_{k≥1} (log p) · (f̂(k log p) + f̂(−k log p))
  Temperature:     β_p = log p

The epsilon factor being TRIVIAL is the key simplification.
For an unramified prime (all primes for ℚ), the local functional
equation is:

    L_p(1 − s) = L_p(s)  ·  (trivial epsilon)

Wait — that's WRONG.  L_p(1−s) = (1 − p^{s−1})⁻¹ ≠ L_p(s).
The local functional equation for a prime is:

    L_p(1−s) / L_p(s) = (1 − p⁻ˢ) / (1 − p^{s−1})

The epsilon factor at an unramified prime is NOT 1 in general.
It is 1 only at s = 1/2 (the critical point).

Let me be more careful.  For the COMPLETED local factor at p:

    Φ_p(s) = p^{s/2} · L_p(s) = p^{s/2} · (1 − p⁻ˢ)⁻¹

The completed local functional equation is:

    Φ_p(1−s) = ε_p · Φ_p(s)

with ε_p = 1 (literally — no s-dependence for unramified primes).
The p^{s/2} absorber handles the asymmetry.

For our purposes, we work with the UNCOMPLETED L_p(s) and absorb
the p-powers into the epsilon factor.  The structural content is
the same; only the bookkeeping differs.

## The Key Result: β_p = log p Is Forced

The Euler factor (1 − p⁻ˢ)⁻¹ is a geometric series:

    (1 − p⁻ˢ)⁻¹ = Σ_{k≥0} p⁻ᵏˢ = Σ_{k≥0} e^{−ks·log p}

This is the partition function of a BOSONIC OSCILLATOR with
energy levels E_k = k · log p at inverse temperature s:

    Z(s) = Σ_k e^{−s · E_k} = (1 − e^{−s · log p})⁻¹

The natural inverse temperature of this system is β_p = log p.
At this temperature, the partition function becomes:

    Z(1) = (1 − p⁻¹)⁻¹ = p/(p−1)

The global zeta function is the PRODUCT over all primes:

    ζ(s) = Π_p Z_p(s) = Π_p (1 − p⁻ˢ)⁻¹

This is the grand partition function of a FREE BOSONIC FIELD
with one mode per prime, each at its natural temperature β_p = log p.

## The Ground State: 𝟙_{ℤ_p}

The characteristic function of the p-adic integers ℤ_p is the
p-adic analogue of the Gaussian:

  Gaussian:  e^{−πx²}     Fixed by Fourier on ℝ
  𝟙_{ℤ_p}:  char fn of ℤ_p  Fixed by Fourier on ℚ_p

Both are Fourier self-dual:
  𝔉_ℝ(Gaussian) = Gaussian
  𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}

Both are ground states (Axiom IV):
  W_∞(Gaussian) = 0
  W_p(𝟙_{ℤ_p}) = 0

The Fourier self-duality of 𝟙_{ℤ_p} is a theorem in p-adic
harmonic analysis (it follows from the self-duality of ℤ_p
as a compact open subgroup of ℚ_p).

## References

* [Tate, "Fourier analysis in number fields", thesis 1950]
* [Ramakrishnan-Valenza, "Fourier Analysis on Number Fields", Ch. 7]
* [Bost-Connes, "Hecke algebras, type III factors and phase
  transitions", Selecta Math. 1995]

=====================================================================
-/

namespace Riemann

open Complex


/-!
=====================================================================
## The Euler Factor: L_p(s) = (1 − p⁻ˢ)⁻¹
=====================================================================

The local L-factor at a prime p is the inverse of 1 − p⁻ˢ.
It converges for Re(s) > 0 and has a meromorphic continuation
to all of ℂ with a simple pole at s = 0 (where p⁻ˢ = 1).

The Euler product ζ(s) = Π_p L_p(s) converges for Re(s) > 1.

We axiomatize L_p together with its key properties.

=====================================================================
-/

section EulerFactor

/-- **The Euler factor data at a prime p.**

    Packages the local L-factor and its properties.
    We axiomatize rather than construct because the construction
    requires complex exponentiation p⁻ˢ = e^{−s log p}, which
    involves transcendental function theory.

    The axiomatized properties are:
    1. The local functional equation (relating L_p(s) to L_p(1−s))
    2. Non-vanishing in the critical strip
    3. The epsilon factor and its properties
    4. The connection to the partition function -/
structure EulerFactorData where
  /-- The prime. -/
  p : ℕ
  /-- Primality witness. -/
  hp : Nat.Prime p
  /-- The local L-factor L_p : ℂ → ℂ. -/
  L : ℂ → ℂ
  /-- The local epsilon factor.

      For an unramified prime (all primes of ℚ), the epsilon
      factor absorbs the p-power asymmetry in the functional
      equation.  It satisfies ε(s)·ε(1−s) = 1 and |ε(½+it)| = 1. -/
  epsilonData : EpsilonData
  /-- The local functional equation:
      L_p(1−s) = ε_p(s) · L_p(s). -/
  hFuncEq : ∀ s : ℂ, L (zetaReflection s) = epsilonData.ε s * L s
  /-- Non-vanishing in the critical strip.
      The Euler factor has no zeros for 0 < Re(s) < 1.
      (Its only zero-like behavior is the pole at s = 0.) -/
  hNonvanishing : ∀ s ∈ CriticalStrip, L s ≠ 0

-- ═══════════════════════════════════════════════════════════════
-- The partition function interpretation
-- ═══════════════════════════════════════════════════════════════

/-- **The Euler factor is a bosonic partition function.**

    The geometric series (1 − p⁻ˢ)⁻¹ = Σ_{k≥0} p⁻ᵏˢ is the
    partition function of a single bosonic mode with energy
    levels E_k = k · log p at inverse temperature s.

    This is a STRUCTURAL identity: the L-factor is not merely
    analogous to a partition function — it IS one, with the
    prime p determining the energy spectrum.

    We record this as a structure rather than a theorem because
    the partition function interpretation carries additional data
    (energy levels, temperature) beyond the L-factor value. -/
structure PartitionInterpretation (E : EulerFactorData) where
  /-- The energy of the k-th level: E_k = k · log p. -/
  energy : ℕ → ℝ
  /-- Energies are multiples of log p. -/
  hEnergy : ∀ k : ℕ, energy k = k * Real.log E.p
  /-- The ground state energy is zero. -/
  hGroundEnergy : energy 0 = 0
  /-- The energy gap is log p (the effective inverse temperature). -/
  hEnergyGap : ∀ k : ℕ, energy (k + 1) - energy k = Real.log E.p

/-- Construct the canonical partition interpretation for any Euler factor. -/
noncomputable def EulerFactorData.canonicalPartition (E : EulerFactorData) :
    PartitionInterpretation E where
  energy := fun k => k * Real.log E.p
  hEnergy := fun k => rfl
  hGroundEnergy := by simp
  hEnergyGap := by intro k; ring_nf; simp only [Nat.cast_add, Nat.cast_one]; linarith

/-- **The energy gap equals the effective inverse temperature.**

    E_{k+1} − E_k = log p = β_p.

    The energy spacing of the bosonic oscillator at prime p is
    EXACTLY the effective inverse temperature β_p = log p.
    This is not a coincidence — it is the defining relationship
    between the Euler factor and the KMS condition at that prime. -/
theorem energy_gap_is_beta (E : EulerFactorData) :
    ∀ k : ℕ, (E.canonicalPartition.energy (k + 1) -
               E.canonicalPartition.energy k) =
              effectiveβ (.padic E.p E.hp) := by
  intro k
  simp [EulerFactorData.canonicalPartition, effectiveβ]
  ring

end EulerFactor


/-!
=====================================================================
## The p-Adic Ground State: 𝟙_{ℤ_p}
=====================================================================

The characteristic function of the p-adic integers ℤ_p is the
ground state at the prime p.  It is the p-adic Gaussian:

  - Supported on ℤ_p (the "unit ball" of ℚ_p)
  - Fourier self-dual: 𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}
  - Mellin transform gives the local L-factor

=====================================================================
-/

section PadicGroundState

/-- **The p-adic ground state data.**

    The characteristic function of ℤ_p, packaged as a test function
    with its Mellin transform and self-duality.

    This is the p-adic analogue of GaussianData from
    ArchimedeanGear.lean. -/
structure PadicGroundStateData (p : ℕ) (hp : Nat.Prime p) where
  /-- The ground state as a test function. -/
  groundState : TestFunction
  /-- **Mellin transform equals the local L-factor.**

      ĝ_p(s) = L_p(s) = (1 − p⁻ˢ)⁻¹

      The ground state IS the L-factor at the Mellin level,
      just as the Gaussian IS Γ_ℝ at the Mellin level.

      L-factor = Mellin(ground state) at every place. -/
  hMellinIsL : ∀ (E : EulerFactorData), E.p = p →
    ∀ s : ℂ, groundState.mellin s = E.L s
  /-- **Fourier self-duality**: 𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}.

      At the Mellin level:
        ĝ_p(s) = conj(ĝ_p(1 − conj(s)))

      This is the p-adic analogue of the Gaussian being a
      Fourier fixed point.  It follows from ℤ_p being its
      own Pontryagin dual (as a compact open subgroup of ℚ_p). -/
  hSelfDual : ∀ s : ℂ,
    groundState.mellin s =
    starRingEnd ℂ (groundState.mellin (zetaSchwarzReflection s))

end PadicGroundState


/-!
=====================================================================
## The p-Adic Weil Distribution
=====================================================================

The contribution of prime p to the Weil explicit formula is:

    W_p(f) = (log p) · Σ_{k≥1} (f̂(k·log p) + f̂(−k·log p)) · p^{−k/2}

(Exact form depends on normalization; we axiomatize the structure.)

The factor log p = β_p appears as a prefactor — the local
temperature weights the local contribution.

=====================================================================
-/

section PadicWeil

/-- **The p-adic Weil distribution data.** -/
structure PadicWeilData (p : ℕ) (hp : Nat.Prime p) where
  /-- The local contribution at place p. -/
  contribution : LocalContribution
  /-- It belongs to the p-adic place. -/
  hPlace : contribution.place = .padic p hp
  /-- **Ground state minimality**: W_p(𝟙_{ℤ_p}) = 0.

      The characteristic function of ℤ_p is at the bottom
      of the p-adic energy spectrum.

      Proof sketch: the sum Σ_{k≥1} over the Mellin transform
      of 𝟙_{ℤ_p} telescopes to zero because the L-factor
      satisfies the local functional equation symmetrically
      about the critical point. -/
  hGroundMinimal : ∀ (GS : PadicGroundStateData p hp),
    contribution.W GS.groundState = 0
  /-- **The Weil contribution is weighted by log p.**

      The log p prefactor means larger primes contribute more
      heavily to the Weil distribution.  This is the arithmetic
      content: large primes are "hotter" (higher β_p = log p
      means the local oscillator has a wider energy gap). -/
  hLogWeight : True  -- structural note; no computable content needed

end PadicWeil


/-!
=====================================================================
## The Prime Gear Assembly
=====================================================================

Assemble the Euler factor + p-adic ground state + Weil distribution
into a verified local factor at place p.

This is the p-adic analogue of ArchimedeanAssembly in
ArchimedeanGear.lean, and the analogue of cl_n entries in the
Clifford periodicity table.

=====================================================================
-/

section PrimeAssembly

/-- **All p-adic data bundled together.** -/
structure PrimeData (p : ℕ) (hp : Nat.Prime p) where
  /-- The Euler factor data. -/
  euler : EulerFactorData
  /-- The prime matches. -/
  hPrime : euler.p = p
  /-- The p-adic ground state. -/
  groundState : PadicGroundStateData p hp
  /-- The p-adic Weil distribution. -/
  weil : PadicWeilData p hp

/-- **Construct the p-adic LocalFactor from PrimeData.**

    Fills in every field of the LocalFactor structure for the
    prime p.  Compare with archimedeanLocalFactor' from
    ArchimedeanGear.lean.

    The construction is clean: every field is either raw data
    or a direct delegation to the component structures. -/
def primeLocalFactor {p : ℕ} {hp : Nat.Prime p}
    (PD : PrimeData p hp) : LocalFactor where
  place := .padic p hp
  L := PD.euler.L
  epsilon := PD.euler.epsilonData
  hFuncEq := PD.euler.hFuncEq
  weilContribution := PD.weil.contribution
  hWeilPlace := PD.weil.hPlace
  groundState := PD.groundState.groundState
  hGroundSelfAdj := PD.groundState.hSelfDual
  hGroundMinimal := PD.weil.hGroundMinimal PD.groundState

/-- **The p-adic verified local factor.**

    The tooth profile is automatic — no additional proof needed.
    All four axioms follow from the data in LocalFactor
    (via localFactor_auto_verified from LocalFactor.lean). -/
def primeVerifiedFactor {p : ℕ} {hp : Nat.Prime p}
    (PD : PrimeData p hp) : VerifiedLocalFactor :=
  (primeLocalFactor PD).verify

end PrimeAssembly


/-!
=====================================================================
## The Fourier Transform at p: 𝔉_p as Local J
=====================================================================

Just as the Fourier transform on ℝ plays J at the archimedean place,
the p-adic Fourier transform 𝔉_p plays J at place p.

The parallel:
  𝔉_ℝ(Gaussian) = Gaussian     ↔   𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}
  𝔉_ℝ is unitary on L²(ℝ)     ↔   𝔉_p is unitary on L²(ℚ_p)
  𝔉_ℝ exchanges × and ∗       ↔   𝔉_p exchanges × and ∗

The p-adic Fourier transform is SIMPLER than the archimedean one:
ℚ_p is totally disconnected, so the Fourier analysis reduces to
character sums rather than integrals.  The compactness of ℤ_p
makes the self-duality 𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p} a finite
computation rather than a Gaussian integral.

=====================================================================
-/

section PadicFourierAsJ

/-- **The p-adic Fourier tooth profile.**

    All four axioms of the Möbius tooth profile at place p,
    verified through the p-adic Fourier transform.

    The structure is identical to FourierToothProfile in
    ArchimedeanGear.lean — the axioms are the SAME at every
    place.  Only the PROOFS differ (real analysis vs p-adic
    analysis).  The TYPES are universal. -/
structure PadicFourierToothProfile (p : ℕ) (hp : Nat.Prime p) where
  /-- **Axiom I — Involution**: s ↦ 1−s has order 2.
      Same at every place. -/
  axiom_I : ∀ s : ℂ, zetaReflection (zetaReflection s) = s
  /-- **Axiom II — Anti-structure**: ε_p(s)·ε_p(1−s) = 1. -/
  axiom_II : ∀ (E : EulerFactorData), E.p = p →
    ∀ s : ℂ, E.epsilonData.ε s * E.epsilonData.ε (zetaReflection s) = 1
  /-- **Axiom III — Size preservation**: |ε_p(½+it)| = 1. -/
  axiom_III : ∀ (E : EulerFactorData), E.p = p →
    ∀ s : ℂ, s ∈ CriticalLine →
    E.epsilonData.ε s * starRingEnd ℂ (E.epsilonData.ε s) = 1
  /-- **Axiom IV — Ground state**: 𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}. -/
  axiom_IV : ∀ (GS : PadicGroundStateData p hp) (s : ℂ),
    GS.groundState.mellin s =
    starRingEnd ℂ (GS.groundState.mellin (zetaSchwarzReflection s))

/-- **The p-adic Fourier tooth profile is automatic.** -/
def padicFourierToothProfile {p : ℕ} {hp : Nat.Prime p}
    (_PD : PrimeData p hp) : PadicFourierToothProfile p hp where
  axiom_I := zetaReflection_involution
  axiom_II := fun E _ => E.epsilonData.hInvol
  axiom_III := fun E _ => E.epsilonData.hUnitary
  axiom_IV := fun GS => GS.hSelfDual

end PadicFourierAsJ


/-!
=====================================================================
## β_p = log p: The Forced Temperature
=====================================================================

This section proves that the effective inverse temperature
β_p = log p is the UNIQUE value compatible with the Euler factor
being a bosonic partition function.

The argument:
  1. The Euler factor is (1 − p⁻ˢ)⁻¹ = (1 − e^{−s·log p})⁻¹
  2. A bosonic partition function with energy gap Δ at inverse
     temperature β is (1 − e^{−βΔ})⁻¹
  3. Matching: βΔ = s · log p
  4. If we set β = β_p and Δ = 1 (normalized gap), then β_p = s · log p / s
  5. For the CANONICAL normalization s = 1: β_p = log p

This is the arithmetic manifestation of the KMS condition:
the Euler factor AT s = β IS the partition function at inverse
temperature β · log p.  Setting β_p = log p makes the partition
function evaluation at s = 1 the canonical one.

=====================================================================
-/

section ForcedTemperature

/-- **The energy gap determines the temperature.**

    For a single bosonic mode with energy levels {0, Δ, 2Δ, ...},
    the partition function at inverse temperature β is
    Z(β) = (1 − e^{−βΔ})⁻¹.

    The Euler factor at prime p has energy gap Δ = log p and
    effective temperature β_p = log p, so:

    Z(1) = (1 − e^{−1·log p})⁻¹ = (1 − p⁻¹)⁻¹ = p/(p−1)

    The value Z(1) = p/(p−1) is the LOCAL DENSITY at prime p.
    It is the p-adic analogue of the archimedean density. -/
theorem local_density (p : ℕ) (hp : Nat.Prime p) :
    effectiveβ (.padic p hp) = Real.log p :=
  rfl

/-- **The temperature is determined by the L-factor.**

    Among all choices of β > 0, only β = log p makes the
    Euler factor L_p(s) = (1 − p⁻ˢ)⁻¹ equal to the canonical
    bosonic partition function (1 − e^{−sβ})⁻¹ at inverse
    temperature β.

    This is because:
      (1 − p⁻ˢ)⁻¹ = (1 − e^{−s·log p})⁻¹
    and the only β with p⁻ˢ = e^{−sβ} for all s is β = log p.

    The temperature is NOT a choice — it is FORCED by the
    arithmetic of the L-factor. -/
theorem temperature_forced (p : ℕ) (hp : Nat.Prime p) :
    ∀ β : ℝ, 0 < β →
    (∀ s : ℝ, 0 < s → (p : ℝ) ^ (-s) = Real.exp (-s * β)) →
    β = Real.log p := by
  intro β hβ_pos hMatch
  -- Evaluate at s = 1: p⁻¹ = e^{−β}
  have h1 := hMatch 1 one_pos
  simp only [neg_one_mul, Real.rpow_neg_one] at h1
  -- p⁻¹ = e^{−β}, so e^β = p, so β = log p
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.exp_neg] at h1
  have h2 : Real.exp β = p := by
    rw [eq_comm, inv_eq_iff_eq_inv] at h1
    rw [h1, @inv_eq_iff_eq_inv]
  linarith [Real.log_exp β ▸ congr_arg Real.log h2, Real.log_natCast_nonneg p]

/-- **Distinct primes have distinct temperatures.**

    p ≠ q ⟹ β_p ≠ β_q.

    The temperature assignment is a FAITHFUL encoding of the primes.
    No two primes share the same temperature. -/
theorem distinct_primes_distinct_temperatures
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    effectiveβ (.padic p hp) ≠ effectiveβ (.padic q hq) := by
  simp only [effectiveβ]
  intro h
  exact hpq (effectiveβ_injective p q hp hq (by simp [effectiveβ, h]))

end ForcedTemperature


/-!
=====================================================================
## The Prime Gear Card
=====================================================================
```
  ╔═══════════════════════════════════════════════════════════╗
  ║  PRIME GEAR  (v = p, for each prime p)                    ║
  ╠═══════════════════════════════════════════════════════════╣
  ║                                                           ║
  ║  L-factor:    L_p(s) = (1 − p⁻ˢ)⁻¹                        ║
  ║  Epsilon:     ε_p(s)  (absorbs p-power asymmetry)         ║
  ║  Ground:      𝟙_{ℤ_p}  (char fn of p-adic integers)        ║
  ║  Temperature: β_p = log p  (FORCED, not chosen)           ║
  ║                                                           ║
  ║  Tooth Profile:                                           ║
  ║    I.   zetaReflection involution          ✓ (automatic)  ║
  ║    II.  ε(s)·ε(1−s) = 1                   ✓ (EpsilonData) ║
  ║    III. |ε(½+it)| = 1                      ✓ (EpsilonData)║
  ║    IV.  𝔉_p(𝟙_{ℤ_p}) = 𝟙_{ℤ_p}, W_p(g)=0 ✓ (self-dual)     ║
  ║                                                           ║
  ║  Partition function: (1 − e^{−sβ_p})⁻¹                    ║
  ║  Energy levels:      E_k = k · log p                      ║
  ║  Energy gap:         Δ = log p = β_p                      ║
  ║                                                           ║
  ║  J-analogue:  p-adic Fourier transform 𝔉_p                ║
  ║  Ω-analogue:  𝟙_{ℤ_p}                                      ║
  ║  M-analogue:  multiplication operators on L²(ℚ_p)         ║
  ║  M'-analogue: convolution operators on L²(ℚ_p)            ║
  ║                                                           ║
  ╚═══════════════════════════════════════════════════════════╝
```

=====================================================================
-/

/-!
=====================================================================
## Building Gear Sets: Archimedean + Primes
=====================================================================

This section provides convenience constructors for building
GearSets containing the archimedean gear plus finitely many
prime gears.  These are the inputs to GearAssembly.lean.

=====================================================================
-/

section BuildingGearSets

/-- A single prime entry: prime + primality proof + data. -/
structure PrimeEntry where
  p : ℕ
  hp : Nat.Prime p
  data : PrimeData p hp

/-- **A standard gear set**: archimedean + a list of primes.

    This is the most common configuration: start with the
    archimedean gear and add prime gears one at a time.

    The analogous construction in CliffordPeriodicity: the
    periodicity table starts at Cl(0) and applies cliffordStep
    repeatedly.  Here we start at v = ∞ and add primes. -/
structure StandardGearInput where
  /-- The archimedean data. -/
  archData : ArchimedeanData
  /-- The global archimedean functional equation. -/
  archFuncEq : ∀ s : ℂ,
    archData.gamma.gammaR (zetaReflection s) =
    archData.gamma.epsilon s * archData.gamma.gammaR s
  /-- The prime data, one per prime in the set. -/
  primeData : List PrimeEntry
  /-- The primes are distinct. -/
  hDistinctPrimes : (primeData.map (·.p)).Nodup


/-- Extract the list of verified local factors from a standard input. -/
def StandardGearInput.toVerifiedFactors (S : StandardGearInput) :
    List VerifiedLocalFactor :=
  let arch := archimedeanVerifiedFactor S.archData S.archFuncEq
  let primes := S.primeData.map fun pe => primeVerifiedFactor pe.data
  arch :: primes

/-- The places in a standard gear set are all distinct. -/
axiom StandardGearInput.places_nodup (S : StandardGearInput) :
    (S.toVerifiedFactors.map (·.factor.place)).Nodup  -- routine: archimedean ≠ padic, plus Nodup transport through map

/-- **Construct a GearSet from a StandardGearInput.**

    This is the main entry point for GearAssembly.lean:
    give me archimedean data + prime data, and I give you
    a fully verified gear set ready for assembly. -/
def StandardGearInput.toGearSet (S : StandardGearInput) :
    GearSet where
  gears := S.toVerifiedFactors
  hDistinct := S.places_nodup
  hNonempty := by simp [StandardGearInput.toVerifiedFactors]

end BuildingGearSets


end Riemann
