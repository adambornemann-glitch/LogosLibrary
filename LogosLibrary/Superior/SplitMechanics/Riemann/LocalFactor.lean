/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Riemann/LocalFactor.lean
-/
import LogosLibrary.Superior.SplitMechanics.Riemann.ExplicitFormula
/-!
=====================================================================
# LOCAL FACTORS AND THE TOOTH PROFILE
=====================================================================
Via the Curry-Howard method.

## Overview

Each place v of ℚ contributes a local factor to the Euler product
and a local term to the Weil distribution.  This file defines the
TYPED INTERFACE that each local factor must satisfy — the number-
theoretic instantiation of the Möbius tooth profile.

The file defines three structures:

  1. `LocalFactor`:   the RAW DATA a place must provide
  2. `LocalToothProfile`:  the 4-AXIOM VERIFICATION on that data
  3. `VerifiedLocalFactor`:  a LocalFactor bundled with its proof

ArchimedeanGear.lean and PrimeFactor.lean will each construct a
`VerifiedLocalFactor` — proving that their local data satisfies
all four axioms of the tooth profile.

## The Four Axioms (Number-Theoretic Version)

  **Axiom I — Involution**:
    The local functional equation respects s ↦ 1 − s.
    L_v(s) and L_v(1 − s) are related by the local epsilon factor.
    This is the SAME involution at every place — the universal shaft.

  **Axiom II — Anti-Structure**:
    The local epsilon factor ε_v(s) satisfies
    ε_v(s) · ε_v(1 − s) = 1.
    The product of two half-twists is the identity.
    Analogous to J(ab) = J(b)J(a) (the twist reverses order).

  **Axiom III — Size Preservation**:
    |ε_v(1/2 + it)| = 1 on the critical line.
    The epsilon factor is UNITARY on the fixed locus of the
    involution.  Analogous to ‖Jψ‖ = ‖ψ‖ (antiunitary).

  **Axiom IV — Ground State**:
    There exists a distinguished test function g_v (the local
    ground state) with g_v = g̃_v (self-adjoint under Mellin
    adjunction) and W_v(g_v) = 0 (minimal energy).
    At v = ∞: the Gaussian e^{−πx²}.
    At v = p: the characteristic function of ℤ_p.
    Analogous to JΩ = Ω (the vacuum is fixed by the twist).

## The Parallel

    Axiom    CD (algebraic)      Tomita (operator)     Zeta (arithmetic)
    ─────    ──────────────      ─────────────────     ─────────────────
    I        J² = 1              J² = 1                ε(s)ε(1−s) = 1
    II       J(ab) = J(b)J(a)   JMJ = M'              local func. eq.
    III      ‖J(a)‖ = ‖a‖       ⟨Jψ,Jφ⟩ = ⟨φ,ψ⟩     |ε(½+it)| = 1
    IV       a·J(a) = ‖a‖²      JΩ = Ω                g_v = g̃_v, W_v(g)=0

## References

* [Tate, "Fourier analysis in number fields and Hecke's zeta-functions",
  thesis, Princeton 1950]
* [Weil, "Sur les 'formules explicites'", 1952]
* [Connes, "Trace formula in noncommutative geometry", 1999]

=====================================================================
-/

namespace Riemann

open Complex


/-!
=====================================================================
## The Local Epsilon Factor
=====================================================================

The epsilon factor ε_v(s) is the ratio relating L_v(s) to L_v(1−s)
in the local functional equation:

    L_v(1 − s) = ε_v(s) · L_v(s)

It encodes the "twisting" that the involution s ↦ 1−s induces on
the local L-factor.  The global functional equation ξ(s) = ξ(1−s)
assembles from the product of all local equations, with the product
of all ε_v equaling 1 (the global epsilon factor is trivial for ℚ).

The epsilon factor is the number-theoretic analogue of the Tomita
modular conjugation J at the local level: it implements the half-twist
from one boundary of the KMS strip to the other.

=====================================================================
-/

section EpsilonFactor

/-- **Local epsilon factor data**.

    The ratio ε_v(s) in the local functional equation
    L_v(1−s) = ε_v(s) · L_v(s).

    Packages the function together with its key structural
    properties.  These properties are the raw material from
    which the tooth profile axioms are verified. -/
structure EpsilonData where
  /-- The epsilon factor ε : ℂ → ℂ -/
  ε : ℂ → ℂ
  /-- **Involution compatibility**: ε(s) · ε(1−s) = 1.

      Applying the local functional equation twice must return
      to the start.  This is the epsilon-level manifestation
      of Axiom I (involution).

      L(s) →[ε(1−s)] L(1−s) →[ε(s)] L(1−(1−s)) = L(s)
      The round trip is multiplication by ε(s)·ε(1−s) = 1. -/
  hInvol : ∀ s : ℂ, ε s * ε (zetaReflection s) = 1
  /-- **Unitarity on the critical line**: |ε(1/2 + it)| = 1.

      We state this as: on the critical line, ε(s) · ε(s)̄ = 1.
      Equivalently, |ε(s)|² = 1 when Re(s) = 1/2.

      This is Axiom III (size preservation) at the epsilon level:
      the twist preserves the "size" of the L-factor on the
      fixed locus of the involution. -/
  hUnitary : ∀ s : ℂ, s ∈ CriticalLine →
    ε s * starRingEnd ℂ (ε s) = 1

-- ═══════════════════════════════════════════════════════════════
-- Consequences of the epsilon data
-- ═══════════════════════════════════════════════════════════════

/-- The epsilon factor is nonvanishing: ε(s) ≠ 0 everywhere.

    Proof: if ε(s) = 0, then ε(s) · ε(1−s) = 0 ≠ 1. -/
theorem EpsilonData.ne_zero (E : EpsilonData) (s : ℂ) :
    E.ε s ≠ 0 := by
  intro h
  have := E.hInvol s
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- On the critical line, ε(s) = 1/ε(s)̄ — the conjugate is
    the multiplicative inverse.  This is the arithmetic
    manifestation of antiunitary: J reverses the inner product
    just as ε conjugation inverts the value. -/
theorem EpsilonData.conj_eq_inv (E : EpsilonData) {s : ℂ}
    (hs : s ∈ CriticalLine) :
    starRingEnd ℂ (E.ε s) = (E.ε s)⁻¹ := by
  have h := E.hUnitary s hs
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  rwa [mul_comm]

end EpsilonFactor


/-!
=====================================================================
## The Local L-Factor
=====================================================================

Each place v contributes a local L-factor L_v(s).  The global
completed zeta function is the product:

    ξ(s) = ½s(s−1) · Π_v L_v(s)

(with the s(s−1)/2 prefactor handling the trivial zeros and pole).

For v = ∞ (archimedean):   L_∞(s) = π^{−s/2} Γ(s/2)
For v = p (prime):          L_p(s) = (1 − p^{−s})^{−1}

The local functional equation at each place is:

    L_v(1 − s) = ε_v(s) · L_v(s)

=====================================================================
-/

section LocalLFactor

/-- **A local L-factor at a place of ℚ.**

    Packages the place, the L-factor function, the epsilon factor,
    the local contribution to the Weil distribution, and all
    consistency conditions.

    This is the analogue of `CliffordData`: typed data with
    built-in proofs that the components fit together.

    The fields are organized by the tooth profile they serve:
    - `place`, `L`, `epsilon`: raw data
    - `hFuncEq`: Axiom I (involution) at the L-factor level
    - `epsilon`: Axiom I + II at the epsilon level
    - `weilContribution`: connects to ExplicitFormula.lean
    - `groundState`: Axiom IV -/
structure LocalFactor where
  /-- Which place of ℚ this factor belongs to. -/
  place : Place
  /-- The local L-factor L_v : ℂ → ℂ. -/
  L : ℂ → ℂ
  /-- The local epsilon factor data. -/
  epsilon : EpsilonData
  /-- **Local functional equation**: L(1−s) = ε(s) · L(s).

      The local manifestation of the global ξ(s) = ξ(1−s).
      Each place has its OWN local equation with its own ε,
      but all share the SAME involution s ↦ 1−s.

      The universal shaft: every gear turns on the same axis. -/
  hFuncEq : ∀ s : ℂ, L (zetaReflection s) = epsilon.ε s * L s
  /-- The local Weil contribution: W_v maps test functions to ℂ.
      This is the GEOMETRIC SIDE contribution from place v. -/
  weilContribution : LocalContribution
  /-- The Weil contribution belongs to the correct place. -/
  hWeilPlace : weilContribution.place = place
  /-- **The ground state test function**: the distinguished
      self-adjoint element at this place.

      At v = ∞:  the Gaussian g(x) = e^{−πx²}
      At v = p:  the characteristic function of ℤ_p

      The ground state is the analogue of the vacuum Ω in
      Tomita theory: the fixed point of the half-twist. -/
  groundState : TestFunction
  /-- **Ground state self-adjointness**: ĝ(s) = ĝ(1−s̄)̄.

      The Mellin transform of the ground state is invariant
      under the Schwarz reflection.  This is the arithmetic
      JΩ = Ω: the ground state is fixed by the full twist
      (reflection + conjugation). -/
  hGroundSelfAdj : ∀ s : ℂ,
    groundState.mellin s =
    starRingEnd ℂ (groundState.mellin (zetaSchwarzReflection s))
  /-- **Ground state minimality**: W_v(g_v) = 0.

      The local Weil distribution evaluates to zero on the
      ground state.  This is the vacuum energy condition:
      the ground state is at the bottom of the energy spectrum.

      In Tomita language: ⟨Ω, [H, ·]Ω⟩ = 0 — the vacuum
      has zero expectation value for the Hamiltonian commutator. -/
  hGroundMinimal : weilContribution.W groundState = 0

end LocalLFactor


/-!
=====================================================================
## The Tooth Profile: Four Axioms
=====================================================================

A `LocalToothProfile` is the VERIFICATION that a `LocalFactor`
satisfies all four axioms of the Möbius gear.  It is a Prop-valued
structure — a certificate of compliance.

The analogy:
  - `LocalFactor` is to `LocalToothProfile` as
    `CliffordData` is to `hDimCheck`
  - The data carries structural fields; the profile
    verifies the RELATIONSHIPS between them.

But we separate them (unlike CliffordData where hDimCheck is
internal) because the SAME LocalFactor data might satisfy the
profile under one set of assumptions but not another.  The
profile is a JUDGMENT on the data, not part of it.

Compare with the three-twist analysis from MobiusGear.lean:
  CD:     4/4 axioms (full tooth profile)
  Tomita: 4/4 axioms (full tooth profile)
  Bott:   1/4 axioms (involution only)

Every VerifiedLocalFactor achieves 4/4.

=====================================================================
-/

section ToothProfile

/-- **The Möbius tooth profile for a local factor.**

    Four axioms, four teeth.  A local factor is a valid
    Möbius gear if and only if all four are satisfied.

    This is the number-theoretic instantiation of the tooth
    profile from MobiusGear.lean (Part II: THE TOOTH PROFILE). -/
structure LocalToothProfile (LF : LocalFactor) : Prop where
  /-- **Axiom I — Involution**.

      The involution s ↦ 1−s, applied twice, returns to start.
      At the local level, this means the local functional equation
      applied twice recovers the original L-factor:

        L(s) →[ε(1−s)] L(1−s) →[ε(s)] L(s)

      This is automatic from ε(s)·ε(1−s) = 1, which is built
      into EpsilonData.  But we state it explicitly at the
      L-factor level for completeness.

      Compare:
        CD:     qConj(qConj(q)) = q
        Tomita: J(J(ψ)) = ψ
        Zeta:   L(1−(1−s)) = L(s) via epsilon involution -/
  axiom_I : ∀ s : ℂ,
    LF.L (zetaReflection (zetaReflection s)) = LF.L s

  /-- **Axiom II — Anti-Structure**.

      The local functional equation is the "anti-multiplicative"
      content: it REVERSES the direction across the critical strip.
      L(s) on one side becomes ε(s)·L(s) on the other.

      The structural content: the epsilon factor mediates between
      the L-factor and its "reflected self", just as J mediates
      between M and M'.

      We state it as: the local functional equation is CONSISTENT
      with the global one.  Applying the local equation at s and
      at 1−s gives compatible results.

      Compare:
        CD:     J(ab) = J(b)J(a)
        Tomita: b(JaJψ) = JaJ(bψ)  (exchange)
        Zeta:   ε(s)·ε(1−s) = 1    (round-trip consistency) -/
  axiom_II : ∀ s : ℂ,
    LF.epsilon.ε s * LF.epsilon.ε (zetaReflection s) = 1

  /-- **Axiom III — Size Preservation**.

      The epsilon factor is unitary on the critical line:
      |ε(s)| = 1 when Re(s) = 1/2.

      The local functional equation PRESERVES THE SIZE of the
      L-factor on the fixed locus of the involution.  The twist
      rotates but does not stretch.

      This is the arithmetic manifestation of antiunitary:
        ⟨Jψ, Jφ⟩ = ⟨φ, ψ⟩  ⟹  ‖Jψ‖ = ‖ψ‖

      Compare:
        CD:     ‖qConj(q)‖ = ‖q‖
        Tomita: ⟨Jψ,Jφ⟩ = ⟨φ,ψ⟩
        Zeta:   |ε(½+it)| = 1 -/
  axiom_III : ∀ s : ℂ, s ∈ CriticalLine →
    LF.epsilon.ε s * starRingEnd ℂ (LF.epsilon.ε s) = 1

  /-- **Axiom IV — Ground State**.

      There exists a distinguished self-adjoint test function
      (the ground state) at which the local Weil distribution
      vanishes.  The ground state is the FIXED POINT of the
      Mellin adjunction — the local analogue of JΩ = Ω.

      The self-adjointness condition ĝ(s) = conj(ĝ(1−s̄))
      means g is invariant under the Schwarz reflection at
      the Mellin level.  The vanishing W_v(g) = 0 means
      g is at the energy minimum.

      Compare:
        CD:     1 · qConj(1) = ‖1‖² = 1  (unit generates the norm)
        Tomita: JΩ = Ω  (vacuum is J-fixed)
        Zeta:   ĝ(s) = ĝ(1−s̄)̄ and W_v(g) = 0 -/
  axiom_IV_selfAdj : ∀ s : ℂ,
    LF.groundState.mellin s =
    starRingEnd ℂ (LF.groundState.mellin (zetaSchwarzReflection s))
  axiom_IV_minimal : LF.weilContribution.W LF.groundState = 0

/-- **A verified local factor**: data + proof bundled together.

    This is the type that ArchimedeanGear.lean and PrimeFactor.lean
    will construct.  Having a term of this type means the local
    factor at place v is a VALID Möbius gear: all four teeth mesh. -/
structure VerifiedLocalFactor where
  /-- The local factor data. -/
  factor : LocalFactor
  /-- The tooth profile verification. -/
  profile : LocalToothProfile factor

end ToothProfile


/-!
=====================================================================
## Automatic Verifications
=====================================================================

Some axioms follow automatically from the data in `LocalFactor`
and `EpsilonData`.  We prove these lemmas here so that
ArchimedeanGear.lean and PrimeFactor.lean can focus on the
non-trivial verifications.

=====================================================================
-/

section AutomaticVerifications

/-- **Axiom I is automatic**: it follows from the involution
    property of zetaReflection and the local functional equation.

    L(1−(1−s)) = L(s) because 1−(1−s) = s. -/
theorem axiom_I_automatic (LF : LocalFactor) (s : ℂ) :
    LF.L (zetaReflection (zetaReflection s)) = LF.L s := by
  rw [zetaReflection_involution]

/-- **Axiom II is automatic**: it is built into EpsilonData.hInvol.

    ε(s) · ε(1−s) = 1 is a field of EpsilonData. -/
theorem axiom_II_automatic (LF : LocalFactor) (s : ℂ) :
    LF.epsilon.ε s * LF.epsilon.ε (zetaReflection s) = 1 :=
  LF.epsilon.hInvol s

/-- **Axiom III is automatic**: it is built into EpsilonData.hUnitary. -/
theorem axiom_III_automatic (LF : LocalFactor) (s : ℂ)
    (hs : s ∈ CriticalLine) :
    LF.epsilon.ε s * starRingEnd ℂ (LF.epsilon.ε s) = 1 :=
  LF.epsilon.hUnitary s hs

/-- **Axiom IV self-adjointness is in LocalFactor.hGroundSelfAdj.** -/
theorem axiom_IV_selfAdj_automatic (LF : LocalFactor) (s : ℂ) :
    LF.groundState.mellin s =
    starRingEnd ℂ (LF.groundState.mellin (zetaSchwarzReflection s)) :=
  LF.hGroundSelfAdj s

/-- **Axiom IV minimality is in LocalFactor.hGroundMinimal.** -/
theorem axiom_IV_minimal_automatic (LF : LocalFactor) :
    LF.weilContribution.W LF.groundState = 0 :=
  LF.hGroundMinimal

/-- **Every LocalFactor automatically satisfies the full tooth profile.**

    All four axioms are consequences of the data already
    packaged in LocalFactor and EpsilonData.

    This means: if you can construct a LocalFactor (providing
    the data with its consistency proofs), you automatically
    get a VerifiedLocalFactor.  The tooth profile is BAKED INTO
    the type.

    Compare with CliffordData: the consistency conditions
    (hRealDim, hSpinorDim, hDimCheck) are internal to the
    structure, so every CliffordData automatically satisfies
    the "Clifford tooth profile" — the dimensional consistency. -/
theorem localFactor_auto_verified (LF : LocalFactor) :
    LocalToothProfile LF where
  axiom_I := axiom_I_automatic LF
  axiom_II := axiom_II_automatic LF
  axiom_III := axiom_III_automatic LF
  axiom_IV_selfAdj := axiom_IV_selfAdj_automatic LF
  axiom_IV_minimal := axiom_IV_minimal_automatic LF

/-- **Construct a VerifiedLocalFactor from any LocalFactor.**

    No additional proof needed — the type does the work. -/
def LocalFactor.verify (LF : LocalFactor) : VerifiedLocalFactor :=
  ⟨LF, localFactor_auto_verified LF⟩

end AutomaticVerifications


/-!
=====================================================================
## The Tooth Count: Comparing with Bott
=====================================================================

The Bott clock involution (clockConjugate) satisfies only Axiom I
of the tooth profile.  The number-theoretic local factors satisfy
all four.  This section records the tooth count comparison.

  Bott:   1/4  (involution only — no algebra, no norm, no vacuum)
  CD:     4/4  (full profile on ℍ, 𝕆)
  Tomita: 4/4  (full profile on B(H))
  Zeta:   4/4  (full profile on each local factor)

The arithmetic gears mesh with the same completeness as the
algebraic and operator-theoretic gears.

=====================================================================
-/

section ToothCount

/-- **The tooth count is 4/4 for every local factor.**

    Every local factor that can be constructed (i.e., every
    term of type LocalFactor) automatically has a full tooth
    profile.  This is a THEOREM, not an axiom.

    The proof is trivial because the axioms are built into the
    types — but the CONTENT is non-trivial: it means the
    functional equation, epsilon unitarity, and ground state
    conditions are SUFFICIENT for a complete Möbius gear.

    No additional structure is needed beyond what Tate's thesis
    already provides for each place of ℚ. -/
theorem tooth_count_four (LF : LocalFactor) :
    -- Axiom I: involution
    (∀ s : ℂ, LF.L (zetaReflection (zetaReflection s)) = LF.L s)
    ∧
    -- Axiom II: anti-structure
    (∀ s : ℂ, LF.epsilon.ε s * LF.epsilon.ε (zetaReflection s) = 1)
    ∧
    -- Axiom III: size preservation
    (∀ s : ℂ, s ∈ CriticalLine →
      LF.epsilon.ε s * starRingEnd ℂ (LF.epsilon.ε s) = 1)
    ∧
    -- Axiom IV: ground state
    (∀ s : ℂ,
      LF.groundState.mellin s =
      starRingEnd ℂ (LF.groundState.mellin (zetaSchwarzReflection s)))
    ∧ LF.weilContribution.W LF.groundState = 0 :=
  ⟨axiom_I_automatic LF,
   axiom_II_automatic LF,
   axiom_III_automatic LF,
   axiom_IV_selfAdj_automatic LF,
   axiom_IV_minimal_automatic LF⟩

end ToothCount


/-!
=====================================================================
## The Effective Inverse Temperature
=====================================================================

Each place v of ℚ carries an effective inverse temperature β_v.
This is the number-theoretic analogue of the KMS parameter β
in the Tomita modular flow.

  At v = ∞ (archimedean):  β_∞ is a continuous parameter
    (it scales the Gaussian ground state)
  At v = p (p-adic):       β_p = log p
    (the natural scale of the p-adic place)

The key insight from the battle plan: β_p = log p is NOT a choice.
It is FORCED by the local functional equation.  The Euler factor
(1 − p⁻ˢ)⁻¹ evaluated at s = β gives the partition function of
a one-mode bosonic system at inverse temperature β · log p.
Setting β_p = log p normalizes this to the standard form.

The Euler product Π_p (1 − p⁻ˢ)⁻¹ = ζ(s) then becomes:
the grand partition function of a system with one mode per prime,
each at its own inverse temperature β_p = log p, evaluated at
the "modular parameter" s.

=====================================================================
-/

section InverseTemperature

/-- **The effective inverse temperature at a place.**

    Maps each place of ℚ to a positive real number representing
    the local thermal scale.

    At the archimedean place: β_∞ is a parameter (we set it to 1
    as a normalization choice — the archimedean temperature scale
    is continuous, not quantized).

    At a prime p: β_p = log p.  This is the UNIQUE value compatible
    with the Euler factor being a bosonic partition function. -/
noncomputable def effectiveβ : Place → ℝ
  | .archimedean => 1
  | .padic p _ => Real.log p

/-- **β_p is positive for every prime.**

    log p > 0 because p ≥ 2 > 1. -/
theorem effectiveβ_pos (v : Place) : 0 < effectiveβ v := by
  cases v with
  | archimedean => exact one_pos
  | padic p hp =>
    simp only [effectiveβ]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)

/-- **β_p = log p for a prime p.**

    The defining property: the effective inverse temperature
    at a p-adic place is the logarithm of the prime. -/
theorem effectiveβ_padic (p : ℕ) (hp : Nat.Prime p) :
    effectiveβ (.padic p hp) = Real.log p := rfl

/-- **The β-function determines the Euler factor.**

    The Euler factor (1 − p⁻ˢ)⁻¹ can be rewritten as
    (1 − e^{−s · β_p})⁻¹ where β_p = log p.

    This is because p⁻ˢ = e^{−s log p} = e^{−s · β_p}.

    The Euler factor is therefore a BOSONIC PARTITION FUNCTION
    at inverse temperature s · β_p for a single mode.

    We record this as a structural identity at the real level:
    for real s > 0, p^{−s} = e^{−s · log p}. -/
theorem euler_as_partition (p : ℕ) (hp : Nat.Prime p) (s : ℝ) (_hs : 0 < s) :
    (p : ℝ) ^ (-s) = Real.exp (-s * effectiveβ (.padic p hp)) := by
  simp only [effectiveβ]
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp_pos]
  ring_nf

/-- **The temperature assignment is injective on primes.**

    Distinct primes have distinct inverse temperatures.
    β_p = β_q ⟹ log p = log q ⟹ p = q.

    This means the temperature assignment is a FAITHFUL
    encoding of the primes: you can recover the prime from
    its temperature.  No information is lost. -/
theorem effectiveβ_injective :
    ∀ p q : ℕ, ∀ hp : Nat.Prime p, ∀ hq : Nat.Prime q,
    effectiveβ (.padic p hp) = effectiveβ (.padic q hq) → p = q := by
  intro p q hp hq h
  simp only [effectiveβ] at h
  exact Nat.cast_injective (Real.log_injOn_pos
    (by exact_mod_cast hp.pos : (0 : ℝ) < p)
    (by exact_mod_cast hq.pos : (0 : ℝ) < q) h)

end InverseTemperature


/-!
=====================================================================
## The Local-to-Global Interface
=====================================================================

This section defines the interface that GearAssembly.lean will use
to assemble local factors into a semi-local (and eventually global)
gear system.

The key structure: `GearSet`, a finite collection of verified local
factors indexed by places, ready for assembly.

=====================================================================
-/

section LocalToGlobal

/-- **A set of local gears ready for assembly.**

    A finite collection of verified local factors, one per place,
    with no duplicates.  This is the INPUT to the gear assembly.

    Compare with the Clifford periodicity table: a finite set of
    classified data (one per dimension mod 8) from which universal
    theorems are derived. -/
structure GearSet where
  /-- The verified local factors. -/
  gears : List VerifiedLocalFactor
  /-- No two gears share a place. -/
  hDistinct : (gears.map (·.factor.place)).Nodup
  /-- The set is nonempty (at least one gear). -/
  hNonempty : gears ≠ []

/-- The places covered by a gear set. -/
def GearSet.places (G : GearSet) : List Place :=
  G.gears.map (·.factor.place)

/-- Extract the Weil contributions from a gear set. -/
def GearSet.toSemiLocalGeometric (G : GearSet) : SemiLocalGeometric where
  contributions := G.gears.map (·.factor.weilContribution)
  hDistinct := by
    have h := G.hDistinct
    simp only [List.map_map] at h ⊢
    convert h using 1
    congr 1
    ext vlf
    simp only [Function.comp_apply]
    exact vlf.factor.hWeilPlace

/-- **All gears in a GearSet satisfy the tooth profile.**

    This is trivially true because each gear is a
    VerifiedLocalFactor.  But stating it makes the
    tooth-count-4 theorem available at the set level. -/
theorem GearSet.all_verified (G : GearSet)
    (vlf : VerifiedLocalFactor) (_h : vlf ∈ G.gears) :
    LocalToothProfile vlf.factor :=
  vlf.profile

end LocalToGlobal


end Riemann
