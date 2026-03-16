/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: Riemann/ExplicitFormula.lean
-/
import LogosLibrary.Superior.SplitMechanics.Riemann.ZetaData
/-!
=====================================================================
# THE EXPLICIT FORMULA AND WEIL POSITIVITY
=====================================================================
Via the Curry-Howard method.

## Overview

The Riemann-Weil explicit formula equates two sums:

  **SPECTRAL SIDE**: Σ_ρ f̂(ρ)          (sum over non-trivial zeros)
  **GEOMETRIC SIDE**: Σ_v W_v(f)        (sum over places of ℚ)

The sum over places decomposes into:
  - The archimedean place v = ∞ (gamma factor contribution)
  - One term for each prime p (Euler factor contribution)

This file axiomatizes:
  1. Test functions with their Mellin transforms
  2. Places of ℚ (archimedean + primes)
  3. The explicit formula as typed data
  4. The Weil quadratic form and its positivity
  5. The equivalence: WeilPositivity ↔ CriticalLineConfinement (RH)

## The Gear Interface

The explicit formula is the NUMBER-THEORETIC CARRIER SHAFT.

Each place v contributes a local term W_v(f) — a local gear.
The explicit formula says the sum of local contributions equals
the spectral side — this is the SHAFT INDEPENDENCE theorem:
the spectral content (zeros) is the same no matter which
combination of local gears you use to compute it.

    Σ_ρ f̂(ρ) = Σ_v W_v(f)

Compare with the Tomita carrier shaft:

    [σ_t^φ] = [σ_t^ψ] in Out(M)

Both say: the global invariant (zeros / outer flow) is independent
of the local viewpoint (place / state).

## The Weil Positivity Criterion

The quadratic form W(f ∗ f̃) ≥ 0 for all test functions f is
EQUIVALENT to the Riemann Hypothesis.

  **Forward**: RH ⟹ on the critical line, the Weil kernel is
  |f̂(ρ)|² ≥ 0 at each zero, so the sum is non-negative.

  **Converse**: ¬RH ⟹ a zero off the line lets us construct a
  test function making the quadratic form negative.

The forward direction is PROVABLE within our framework.
The converse is AXIOMATIZED (it requires constructing specific
test functions, which is hard analysis).

## References

* [Weil, "Sur les 'formules explicites' de la théorie des
  nombres premiers", Meddelanden Fran Lunds Univ. 1952]
* [Connes, "Trace formula in noncommutative geometry and
  the zeros of the Riemann zeta function", 1999]

=====================================================================
-/

namespace Riemann

open Complex

/-!
=====================================================================
## Places of ℚ
=====================================================================

A place of ℚ is either the archimedean place (the real absolute
value) or a p-adic place (for each prime p).  The product formula
Π_v |x|_v = 1 ties them together.

The explicit formula has one term per place.  The gear assembly
has one gear per place.  The place type is the INDEX SET for both.

=====================================================================
-/

section Places

/-- **A place of ℚ**: either archimedean or p-adic.

    These index the local factors of the zeta function:
      ζ(s) = Π_v L_v(s)⁻¹  (Euler product over all places)

    The archimedean place contributes the gamma factor.
    Each prime p contributes (1 − p⁻ˢ)⁻¹.

    This is the analogue of Fin 8 for the Bott clock —
    the index set for the local data. -/
inductive Place : Type where
  /-- The archimedean (real) place v = ∞. -/
  | archimedean : Place
  /-- The p-adic place for a prime p. -/
  | padic (p : ℕ) (hp : Nat.Prime p) : Place
  deriving DecidableEq

/-- A place is either archimedean or p-adic (exhaustion).
    Trivially true from the inductive definition, but stated
    for the partition record. -/
theorem place_dichotomy (v : Place) :
    (v = .archimedean) ∨ (∃ p hp, v = .padic p hp) := by
  cases v with
  | archimedean => left; rfl
  | padic p hp => right; exact ⟨p, hp, rfl⟩

/-- The local degree: 1 for every place of ℚ.
    (Over number fields, the local degree [k_v : ℚ_p] can
    be > 1.  Over ℚ, every completion is ℚ_p itself.) -/
def Place.localDegree : Place → ℕ
  | .archimedean => 1
  | .padic _ _ => 1

end Places


/-!
=====================================================================
## Test Functions and Mellin Transforms
=====================================================================

A test function for the Weil explicit formula is a smooth
function on ℝ₊* (the multiplicative group of positive reals)
with compact support.  Its Mellin transform

    f̂(s) = ∫₀^∞ f(x) x^s dx/x

is entire and of rapid decay in vertical strips.

We axiomatize the test function TOGETHER with its Mellin
transform, just as CliffordData carries both n and 2ⁿ
with the proof they match.

The key operation: the **ADJOINT** f̃(x) = f̄(1/x)/x, whose
Mellin transform is f̂(1 − s̄)̄.  This connects to the
Schwarz reflection from ZetaData.lean.

=====================================================================
-/

section TestFunctions

/-- **A test function for the Weil explicit formula.**

    Packages a function f and its Mellin transform f̂ together
    with the regularity and consistency conditions.

    We do NOT construct the Mellin transform — we carry it as
    data and axiomatize the relationship.  The consistency
    conditions are theorems about the Mellin transform that
    the explicit formula requires.

    This is the analogue of carrying both matDim and spinorDim
    in CliffordData with hSpinorDim : spinorDim = matDim. -/
structure TestFunction where
  /-- The test function f : ℝ → ℂ.
      (Defined on all of ℝ, supported on ℝ₊*.) -/
  f : ℝ → ℂ
  /-- The Mellin transform f̂ : ℂ → ℂ.
      f̂(s) = ∫₀^∞ f(x) x^s dx/x -/
  mellin : ℂ → ℂ
  /-- The Mellin transform is holomorphic (entire). -/
  hHolo : Differentiable ℂ mellin
  /-- The Mellin transform decays in vertical strips:
      for any σ₁ < σ₂, f̂(σ + it) → 0 as |t| → ∞
      uniformly for σ ∈ [σ₁, σ₂].
      We axiomatize this as boundedness on closed strips. -/
  hDecay : ∀ σ₁ σ₂ : ℝ, σ₁ < σ₂ →
    Bornology.IsBounded (mellin '' {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂})

/-- **The Mellin adjoint**: the involution f ↦ f̃ on test functions.

    At the function level: f̃(x) = conj(f(1/x)) / x
    At the Mellin level:   f̃̂(s) = conj(f̂(1 − conj(s)))

    The Mellin-level formula uses the SCHWARZ REFLECTION
    s ↦ 1 − s̄ from ZetaData.lean.  The Weil quadratic form
    is built from this pairing.

    Note: we axiomatize the adjoint Mellin transform rather
    than deriving it, since the derivation requires the full
    Mellin inversion theory. -/
structure AdjointPair where
  /-- The original test function -/
  func : TestFunction
  /-- The adjoint test function -/
  adjoint : TestFunction
  /-- **Mellin adjoint identity**: the Mellin transform of f̃
      at s is the conjugate of f̂ at the Schwarz reflection of s.

      f̃̂(s) = conj(f̂(zetaSchwarzReflection(s)))

      This is where the Schwarz reflection from ZetaData enters
      the explicit formula.  The functional equation involution
      (s ↦ 1−s) and complex conjugation (s ↦ s̄) combine into
      the Schwarz reflection (s ↦ 1 − s̄), which is the NATURAL
      involution for the Mellin convolution algebra. -/
  hAdjointMellin : ∀ s : ℂ,
    adjoint.mellin s = starRingEnd ℂ (func.mellin (zetaSchwarzReflection s))

/-- **The Weil kernel**: the value of f̂(s) · conj(f̂(1 − s̄)) at a point.

    This is what appears in the Weil quadratic form when summed
    over zeros.  It is the Mellin transform of f ∗ f̃ evaluated at s.

    On the critical line (Re(s) = 1/2), zetaSchwarzReflection(s) = s,
    so the kernel becomes f̂(s) · conj(f̂(s)) = |f̂(s)|².

    Off the critical line, the kernel mixes f̂(s) with f̂ at a
    DIFFERENT point, and can be negative. -/
def weilKernel (F : TestFunction) (s : ℂ) : ℂ :=
  F.mellin s * starRingEnd ℂ (F.mellin (zetaSchwarzReflection s))

/-- **On the critical line, the Weil kernel is |f̂(ρ)|².**

    When Re(s) = 1/2, the Schwarz reflection is the identity,
    so the kernel simplifies to f̂(s) · conj(f̂(s)) = |f̂(s)|².

    This is a non-negative real number.  This fact is the ENGINE
    of the forward direction RH ⟹ Weil positivity. -/
theorem weilKernel_on_criticalLine (F : TestFunction) {s : ℂ}
    (hs : s ∈ CriticalLine) :
    weilKernel F s = F.mellin s * starRingEnd ℂ (F.mellin s) := by
  unfold weilKernel
  congr 1
  have h : zetaSchwarzReflection s = s :=
    (zetaSchwarzReflection_fixed_iff s).mpr hs
  rw [h]

/-- z · z̄ has non-negative real part (it equals |z|²). -/
private theorem mul_conj_nonneg (z : ℂ) :
    0 ≤ (z * starRingEnd ℂ z).re := by
  simp [Complex.mul_conj, Complex.normSq_nonneg]

/-- The Weil kernel on the critical line has non-negative real part.

    In fact it IS real and non-negative: z · z̄ = |z|² ≥ 0.
    We state the weaker "real part ≥ 0" to avoid norm_sq machinery
    and prove the essential content. -/
theorem weilKernel_on_criticalLine_re_nonneg (F : TestFunction) {s : ℂ}
    (hs : s ∈ CriticalLine) :
    0 ≤ (weilKernel F s).re := by
  rw [weilKernel_on_criticalLine F hs]
  exact mul_conj_nonneg (F.mellin s)


end TestFunctions


/-!
=====================================================================
## The Spectral Side
=====================================================================

The spectral side of the explicit formula is the sum

    W_spec(f) = Σ_ρ f̂(ρ)

over non-trivial zeros ρ of ζ, counted with multiplicity.

For the Weil quadratic form applied to f ∗ f̃, this becomes

    W_spec(f ∗ f̃) = Σ_ρ f̂(ρ) · conj(f̂(1 − ρ̄))
                    = Σ_ρ weilKernel(f, ρ)

If RH holds (all ρ on the critical line), each summand is
|f̂(ρ)|² ≥ 0, so the sum is non-negative.

=====================================================================
-/

section SpectralSide

/-- **Spectral data**: the zero-side of the explicit formula.

    Packages a finite truncation of the zero sum together with
    the convergence/tail estimate needed to control the full sum.

    We work with FINITE sums (lists of zeros) and axiomatize
    the convergence.  This avoids building infinite summation
    theory while keeping the types honest.

    The analogue in CliffordPeriodicity: the table has finitely
    many entries (8), and we work with Fin 8 → data.  Here, we
    work with a finite list of ZeroData and axiomatize that it
    captures the full spectral content. -/
structure SpectralData (Z : CompletedZetaData) where
  /-- A finite list of non-trivial zeros (with multiplicity). -/
  zeros : List ZeroData
  /-- Every zero in the list is actually a zero of ξ. -/
  hZeros : ∀ z ∈ zeros, Z.ξ z.ρ = 0
  /-- The list is non-empty (ξ has at least one zero). -/
  hNonempty : zeros ≠ []

/-- The spectral sum of the Weil kernel over a list of zeros. -/
def spectralSum (F : TestFunction) (zeros : List ZeroData) : ℂ :=
  (zeros.map (fun z => weilKernel F z.ρ)).sum

/-- **Under RH, every term of the spectral sum is non-negative.**

    If every zero in the list is on the critical line, then
    each weilKernel(f, ρ) = |f̂(ρ)|² ≥ 0 in the real part. -/
theorem spectralSum_re_nonneg_of_rh (F : TestFunction)
    (zeros : List ZeroData)
    (hOnLine : ∀ z ∈ zeros, z.onCriticalLine) :
    0 ≤ (spectralSum F zeros).re := by
  unfold spectralSum
  induction zeros with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re]
    have hz : z.onCriticalLine := hOnLine z (List.mem_cons.mpr (Or.inl rfl))
    have hzs : ∀ w ∈ zs, w.onCriticalLine :=
      fun w hw => hOnLine w (List.mem_cons.mpr (Or.inr hw))
    exact add_nonneg
      (weilKernel_on_criticalLine_re_nonneg F hz)
      (ih hzs)

end SpectralSide


/-!
=====================================================================
## The Geometric Side: Local Contributions
=====================================================================

The geometric side of the explicit formula is a sum over places:

    W_geom(f) = W_∞(f) + Σ_p W_p(f)

Each place contributes a local term.  The explicit formula says
W_spec(f) = W_geom(f).

We define the TYPE of a local contribution here.  The actual
VALUES at each place will be constructed in ArchimedeanGear.lean
and PrimeFactor.lean.

This is the analogue of defining CliffordAlgStructure (simple/double)
before filling in the table entries.

=====================================================================
-/

section GeometricSide

/-- **A local contribution to the Weil distribution.**

    Each place v of ℚ contributes a functional W_v that maps
    test functions to complex numbers.  The explicit formula
    says the sum of all W_v equals the spectral side.

    The local contribution encodes the arithmetic of v:
    - At v = ∞: gamma factor, archimedean analysis
    - At v = p: Euler factor, p-adic arithmetic

    This is the interface that LocalFactor.lean will instantiate. -/
structure LocalContribution where
  /-- The place this contribution belongs to. -/
  place : Place
  /-- The local functional: maps a test function to a value. -/
  W : TestFunction → ℂ
  /-- Linearity: W(f + g) = W(f) + W(g).
      (We axiomatize this rather than carrying a linear map
      to keep the structure lightweight.) -/
  hLinear : ∀ f g : TestFunction,
    ∀ hSum : TestFunction,
    (∀ s : ℂ, hSum.mellin s = f.mellin s + g.mellin s) →
    W hSum = W f + W g

/-- A finite collection of local contributions, one per place
    in a given set.  The semi-local assembly in GearAssembly.lean
    will use this as its geometric side. -/
structure SemiLocalGeometric where
  /-- The contributions, one per place. -/
  contributions : List LocalContribution
  /-- No duplicate places. -/
  hDistinct : contributions.map (·.place) |>.Nodup

/-- The semi-local geometric sum: Σ_{v ∈ S} W_v(f). -/
def SemiLocalGeometric.totalW (G : SemiLocalGeometric)
    (f : TestFunction) : ℂ :=
  (G.contributions.map (·.W f)).sum

end GeometricSide


/-!
=====================================================================
## The Explicit Formula
=====================================================================

The explicit formula equates the spectral side (sum over zeros)
with the geometric side (sum over places):

    Σ_ρ f̂(ρ) = Σ_v W_v(f)

for every test function f.

This is a KNOWN THEOREM.  We axiomatize it as a structure
containing both sides and their equality.

The equality is the number-theoretic carrier shaft:
the spectral content (zeros) is determined by the arithmetic
content (primes), and vice versa.  No matter which local
gears (places) you examine, the carrier shaft (zero set)
turns at the same rate.

=====================================================================
-/

section ExplicitFormula

/-- **The Riemann-Weil explicit formula, axiomatized.**

    Packages:
    - The completed zeta function (from ZetaData)
    - The spectral data (zeros)
    - The geometric data (local contributions at all places)
    - The equality of the two sides

    This is the analogue of cliffordStep from Table.lean:
    a structure encoding a THEOREM (the periodicity step / the
    explicit formula) as typed data with consistency proofs.

    The equality `hFormula` is the SHAFT INDEPENDENCE axiom:
    the spectral side (computed from zeros) equals the geometric
    side (computed from places) for every test function.

    Compare with `carrier_shaft_well_defined`:
      [σ_t^φ] = [σ_t^ψ]  ↔  Σ_ρ f̂(ρ) = Σ_v W_v(f) -/
structure ExplicitFormulaData where
  /-- The underlying zeta data. -/
  zetaData : CompletedZetaData
  /-- The complete spectral data. -/
  spectral : SpectralData zetaData
  /-- The complete geometric data (all places). -/
  geometric : SemiLocalGeometric
  /-- **THE EXPLICIT FORMULA**: spectral = geometric.

      For every test function, the sum over zeros equals
      the sum over places.  This is the number-theoretic
      shaft independence theorem.

      We state it for the Weil kernel (quadratic form version)
      rather than the linear version, since the quadratic form
      is what connects to positivity and hence to RH. -/
  hFormula : ∀ f : TestFunction,
    spectralSum f spectral.zeros = geometric.totalW f

end ExplicitFormula


/-!
=====================================================================
## The Weil Quadratic Form and Positivity
=====================================================================

The Weil quadratic form is:

    Q(f) = Re(Σ_ρ weilKernel(f, ρ))  =  Re(spectralSum f zeros)

RH is EQUIVALENT to Q(f) ≥ 0 for all test functions f.

  **Forward (RH ⟹ Q ≥ 0)**:  Each summand is |f̂(ρ)|² ≥ 0
  when ρ is on the critical line.  Sum of non-negatives is
  non-negative.  PROVABLE from spectralSum_re_nonneg_of_rh.

  **Converse (Q ≥ 0 ⟹ RH)**:  If ρ is off the critical line,
  construct f with f̂ concentrated near ρ to make Q(f) < 0.
  This requires hard analysis — AXIOMATIZED.

=====================================================================
-/

section WeilPositivity

/-- **The Weil quadratic form**: the real part of the spectral sum
    of the Weil kernel.

    Q(f) = Re(Σ_ρ f̂(ρ) · conj(f̂(1 − ρ̄)))

    This is a real-valued quadratic functional on test functions. -/
def weilQuadraticForm (spectral : List ZeroData) (f : TestFunction) : ℝ :=
  (spectralSum f spectral).re

/-- **WEIL POSITIVITY**: the quadratic form is non-negative for
    all test functions.

    This is a Prop — a property of the zero list.  It is
    EQUIVALENT to the Riemann Hypothesis.

    Compare with CriticalLineConfinement from ZetaData:
    both are Props, both encode RH, but they encode it in
    different languages (zero locations vs. quadratic form). -/
def WeilPositivity (spectral : List ZeroData) : Prop :=
  ∀ f : TestFunction, 0 ≤ weilQuadraticForm spectral f

-- ═══════════════════════════════════════════════════════════════
-- The Forward Direction: RH ⟹ Weil Positivity
-- ═══════════════════════════════════════════════════════════════

/-- **RH implies Weil Positivity.**

    If every zero is on the critical line, then the Weil
    quadratic form is non-negative for every test function.

    Proof: each summand weilKernel(f, ρ) has non-negative
    real part when Re(ρ) = 1/2 (it equals |f̂(ρ)|²), and
    the sum of non-negatives is non-negative.

    This is the FORWARD DIRECTION — the easy half.
    It is PROVED, not axiomatized. -/
theorem rh_implies_weilPositivity
    (zeros : List ZeroData)
    (hRH : ∀ z ∈ zeros, z.onCriticalLine) :
    WeilPositivity zeros := by
  intro f
  exact spectralSum_re_nonneg_of_rh f zeros hRH

-- ═══════════════════════════════════════════════════════════════
-- The Converse: Weil Positivity ⟹ RH (axiomatized)
-- ═══════════════════════════════════════════════════════════════

/-- **Weil Positivity implies RH.**

    If the quadratic form is non-negative for all test functions,
    then every zero must lie on the critical line.

    The proof: if ρ is off the line, one can construct a test
    function f whose Mellin transform is sharply peaked near ρ,
    making weilKernel(f, ρ) dominate the sum with a NEGATIVE
    contribution (since ρ ≠ zetaSchwarzReflection(ρ), the kernel
    is not |f̂|² and can be negative).

    This construction requires hard harmonic analysis (Paley-Wiener
    theory, Mellin inversion).  We axiomatize it. -/
axiom weilPositivity_implies_onLine
    (zeros : List ZeroData)
    (hPos : WeilPositivity zeros) :
    ∀ z ∈ zeros, z.onCriticalLine

-- ═══════════════════════════════════════════════════════════════
-- The Full Equivalence
-- ═══════════════════════════════════════════════════════════════

/-- **THE WEIL EQUIVALENCE: Positivity ↔ RH.**

    The Riemann Hypothesis (all zeros on the critical line) is
    equivalent to Weil positivity (the quadratic form is non-negative
    for all test functions).

    Forward direction: PROVED (sum of |f̂(ρ)|² ≥ 0).
    Converse: AXIOMATIZED (requires Paley-Wiener construction).

    This is the BRIDGE between the gear-theoretic approach
    (which targets Weil positivity through meshing conditions)
    and the classical statement (zeros on the critical line). -/
theorem weil_iff_criticalLine (zeros : List ZeroData) :
    WeilPositivity zeros ↔ (∀ z ∈ zeros, z.onCriticalLine) :=
  ⟨weilPositivity_implies_onLine zeros, rh_implies_weilPositivity zeros⟩

end WeilPositivity


/-!
=====================================================================
## Connecting Weil Positivity to CriticalLineConfinement
=====================================================================

ZetaData defines CriticalLineConfinement on CompletedZetaData.
This section connects it to WeilPositivity on SpectralData.

The connection: if we have ExplicitFormulaData (which bundles
both the zeta function and its zeros), then:

  CriticalLineConfinement(ξ) ↔ WeilPositivity(zeros)

This closes the circle: the gear-theoretic approach
(targeting WeilPositivity) implies the classical RH
(CriticalLineConfinement) and vice versa.

=====================================================================
-/

section ConnectionToRH

/-- **Connecting the two RH formulations.**

    Given explicit formula data (which bundles both ξ and its zeros),
    the classical RH for ξ implies Weil positivity for the zeros,
    and conversely.

    This requires the additional axiom that the zero list in the
    spectral data is COMPLETE: every zero of ξ appears.  Without
    completeness, Weil positivity of a partial list says nothing
    about zeros not in the list. -/
structure CompleteSpectralData (Z : CompletedZetaData) extends
    SpectralData Z where
  /-- **Completeness**: every zero of ξ appears in the list.
      This is the analogue of the Clifford table being EXHAUSTIVE:
      the 8 entries cover ALL residues mod 8. -/
  hComplete : ∀ s : ℂ, Z.ξ s = 0 →
    ∃ z ∈ zeros, z.ρ = s

/-- **Classical RH implies Weil positivity**
    (through complete spectral data). -/
theorem criticalLine_implies_weil
    {Z : CompletedZetaData}
    (SD : CompleteSpectralData Z)
    (hRH : CriticalLineConfinement Z) :
    WeilPositivity SD.zeros := by
  apply rh_implies_weilPositivity
  intro z hz
  simp only [ZeroData.onCriticalLine, CriticalLine, Set.mem_setOf_eq]
  exact hRH z.ρ (SD.hZeros z hz)

/-- **Weil positivity implies classical RH**
    (through complete spectral data). -/
theorem weil_implies_criticalLine
    {Z : CompletedZetaData}
    (SD : CompleteSpectralData Z)
    (hPos : WeilPositivity SD.zeros) :
    CriticalLineConfinement Z := by
  intro s hs
  obtain ⟨z, hz_mem, hz_eq⟩ := SD.hComplete s hs
  have hOnLine := weilPositivity_implies_onLine SD.zeros hPos z hz_mem
  simp only [ZeroData.onCriticalLine, CriticalLine, Set.mem_setOf_eq] at hOnLine
  rw [hz_eq] at hOnLine
  exact hOnLine

/-- **THE GRAND EQUIVALENCE**: Classical RH ↔ Weil Positivity.

    Given complete spectral data, the two formulations of RH
    are interchangeable.  The gear-theoretic approach (which
    targets WeilPositivity through meshing) and the classical
    approach (which targets CriticalLineConfinement directly)
    are attacking the same Prop from different angles.

    One proved direction.  One axiomatized direction.
    Both connected through the explicit formula. -/
theorem rh_iff_weil
    {Z : CompletedZetaData}
    (SD : CompleteSpectralData Z) :
    CriticalLineConfinement Z ↔ WeilPositivity SD.zeros :=
  ⟨criticalLine_implies_weil SD, weil_implies_criticalLine SD⟩

end ConnectionToRH


/-!
=====================================================================
## Semi-Local Positivity Interface
=====================================================================

GearAssembly.lean will work with FINITE sets of places.
This section defines the semi-local positivity condition that
the gear assembly targets.

The strategy:
  1. Show WeilPositivity for larger and larger finite sets S
  2. Take the limit S → {all places}
  3. Conclude global WeilPositivity
  4. Apply rh_iff_weil to get RH

Steps 1-2 are the gear assembly program.
Steps 3-4 are the endgame in Positivity.lean.

This section sets up the INTERFACE for step 1.

=====================================================================
-/

section SemiLocalInterface

/-- **Semi-local positivity**: the geometric sum over a finite
    set of places yields a non-negative quadratic form.

    This is a WEAKER condition than global WeilPositivity —
    it only uses contributions from finitely many places.
    But if it holds for all finite S, the limit gives the
    global condition.

    The gear assembly targets this: if all gears in S mesh,
    then semi-local positivity holds for S. -/
def SemiLocalPositivity (G : SemiLocalGeometric) : Prop :=
  ∀ f : TestFunction, 0 ≤ (G.totalW f).re

/-- **The shaft identity for semi-local data.**

    If the explicit formula holds and we restrict to a
    subset of places, the spectral sum MINUS the semi-local
    geometric sum gives the contribution of the MISSING places.

    Σ_ρ kernel(ρ) − Σ_{v ∈ S} W_v(f) = Σ_{v ∉ S} W_v(f)

    As S grows, the remainder shrinks.  In the limit, both
    sides are equal (the full explicit formula). -/
structure SemiLocalFormula where
  /-- The full explicit formula data. -/
  fullFormula : ExplicitFormulaData
  /-- The semi-local piece (a subset of places). -/
  semiLocal : SemiLocalGeometric
  /-- The remainder (the complementary places). -/
  remainder : SemiLocalGeometric
  /-- The semi-local piece + remainder = full geometric. -/
  hDecomposition : ∀ f : TestFunction,
    semiLocal.totalW f + remainder.totalW f =
    fullFormula.geometric.totalW f

/-- From the explicit formula + decomposition, the spectral sum
    decomposes into semi-local + remainder.

    Σ_ρ kernel(ρ) = Σ_{v ∈ S} W_v(f) + Σ_{v ∉ S} W_v(f) -/
theorem spectral_decomposition (SF : SemiLocalFormula) (f : TestFunction) :
    spectralSum f SF.fullFormula.spectral.zeros =
    SF.semiLocal.totalW f + SF.remainder.totalW f := by
  rw [SF.hDecomposition, SF.fullFormula.hFormula]

end SemiLocalInterface

end Riemann
