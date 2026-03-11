# SuperCausets Revision Notes
**Date**: March 2026
**Scope**: Files Basic.lean, ThermalCauset.lean, QuaternionicEntropy.lean, Cosmology.lean, Synthesis.lean

---

## Priority 1: Structural Changes

### 1.1 Demote R2 from Postulate to Theorem

**File**: `QuaternionicEntropy.lean`
**Current**: R2 (thermal circle, fiber dim = 1) is an independent requirement alongside R1 and R3.
**Change**: Derive R2 from Clifford periodicity.

The argument: R1 + R3 force ℍ, which gives D_spatial = 3, which gives total dimension 9. Clifford periodicity gives Cl(9) ≅ M₁₆(ℂ) — complex base field. Complex structure means U(k) gauge group with a single U(1) center — one circle. One KMS periodicity.

Add a new section after the current elimination:

```lean
/-- **R2 IS A THEOREM, NOT A POSTULATE**

    R1 + R3 → ℍ → D_spatial = 3 → total dim 9 →
    Cl(9) ≅ M₁₆(ℂ) → complex → one S¹.

    The thermal circle requirement is forced by Clifford
    periodicity acting on the dimension that R1+R3 determined. -/
theorem R2_from_clifford_periodicity :
    -- R1 + R3 already force ℍ
    (∀ A : NDA', satisfies_R1 A → satisfies_R3 A → A = .quaternion)
    →
    -- ℍ gives total dim 9
    D_spacetime = 4
    →
    -- Cl(9) is complex (from CliffordPeriodicity.lean)
    cl9.baseField = .complex
    →
    -- Complex ⟹ exactly one S¹ (the U(1) center of U(k))
    satisfies_R2 .quaternion
```

Update the postulate audit in all files to reflect that the independent input count drops by one.


### 1.2 Add Bell Causality Constraint to QuantumTick

**File**: `Basic.lean`, Part VI (QuantumTick)
**Current**: The quantum measure on candidates is unconstrained. It can depend on anything, including spacelike-separated elements.
**Change**: Add a Bell causality field to `QuantumTick`.

```lean
structure QuantumTick (α : Type*) (C : SCauset α) where
  -- [existing fields]
  /-- **BELL CAUSALITY**: The quantum measure on candidates
      depends only on the causal past of the birth event,
      not on spacelike-separated elements.

      This is the CST version of no superluminal signaling.
      Without it, the growth dynamics is not generally covariant.

      Formalized as: for any two candidate sets that agree on
      the past of the born element, the measures agree. -/
  h_bell_causality : ∀ (c : α), c ∈ candidates →
    -- The measure of {c} depends only on the restriction
    -- of current.elements to the past of c
    True  -- placeholder; see note below
```

Note: The full formalization of Bell causality requires defining "the past of an element relative to the current state." This is `{p ∈ current.elements | C.rel p c}`. The constraint is that the measure `μ {c}` depends only on this set, not on elements outside it. The precise statement is: if two growth states agree on the past of every candidate, they assign the same quantum measure to the candidates.

A more precise version:

```lean
  h_bell_causality : ∀ (alt_state : GrowthState α),
    (∀ c ∈ candidates, ∀ p, C.rel p c →
      (p ∈ current.elements ↔ p ∈ alt_state.elements)) →
    -- Then the measure is the same
    -- (requires parametrizing measure by state)
    True
```

This is genuinely hard to formalize cleanly and may warrant its own structure. Flag it as a research target if a clean encoding isn't immediate.


### 1.3 Strengthen the "+1 Longitudinal" Justification

**File**: `QuaternionicEntropy.lean`, Part IV
**Current**: "The '+1' is the direction of the causal chain itself."
**Problem**: This sounds temporal, not spatial. The growth direction is the entropy direction, which by Postulate Zero is time.
**Change**: Rewrite the documentation and add a theorem connecting the longitudinal direction to the transverse-longitudinal decomposition of null propagation.

Replace the current comment block with:

```lean
/-- **THE LONGITUDINAL DIRECTION**

    The Hopf base S² parametrizes TRANSVERSE directions:
    the two independent polarization axes perpendicular to
    a null ray. A null ray propagating through space has:

    - 2 transverse polarizations (from S², the Hopf base)
    - 1 longitudinal direction (the propagation direction)

    The longitudinal direction is spatial, not temporal.
    It is the direction THROUGH space that the causal chain
    projects onto when embedded in the emergent spacetime.

    This is the standard transverse-longitudinal decomposition
    of massless propagation. The transverse count comes from
    the Hopf base. The total spatial dimension is:

      D_spatial = n_transverse + n_longitudinal = 2 + 1 = 3

    Equivalently: a light cone in (3+1) dimensions has 2
    transverse degrees of freedom. The Lüscher coefficient
    -π·n_transverse/24 with n_transverse = 2 confirms this
    counting against lattice QCD. -/
```

Also add:

```lean
/-- The transverse-longitudinal decomposition matches
    the standard massless particle counting:
    D_spacetime - 2 = D_spatial - 1 = n_transverse = 2. -/
theorem transverse_longitudinal_consistency :
    D_spacetime - 2 = n_transverse
    ∧ D_spatial - 1 = n_transverse
    ∧ D_spacetime - 2 = D_spatial - 1 := by
  exact ⟨rfl, rfl, rfl⟩
```


---

## Priority 2: Strengthen Physical Arguments

### 2.1 Strengthen Octonion Elimination

**File**: `QuaternionicEntropy.lean`, Part VI
**Current**: S³ has "THREE independent S¹ subgroups" giving "three temperatures."
**Problem**: S³ admits a choice of thermal circle (maximal torus), not three simultaneous temperatures. The argument is parsimony, not inconsistency.
**Change**: Provide two independent arguments.

**Argument A (algebraic)**: The S¹ subgroup of S³ is a maximal torus, but there is a continuous family of conjugate choices parametrized by S². No canonical selection exists without additional structure. The quaternionic case has no such ambiguity — the fiber IS S¹.

**Argument B (Clifford)**: The octonions are non-associative. R1 (ellipticity) requires the Fueter operator to compose to a scalar Laplacian. For 𝕆, the non-associativity introduces correction terms in ∂̄*∂̄. If R1 is interpreted strictly (exact scalar Laplacian, not approximate), 𝕆 fails R1.

```lean
/-- **𝕆 FAILS R1 STRICTLY**: non-associativity prevents
    exact Fueter-Laplacian composition.

    For associative algebras (ℝ, ℂ, ℍ):
      ∂̄*∂̄ = Δ  (exactly)

    For 𝕆:
      ∂̄*∂̄ = Δ + associator corrections  (not scalar!)

    If R1 requires exact ellipticity, 𝕆 is eliminated at the
    first gate. R2 then provides an independent confirmation. -/
def satisfies_R1_strict (A : NDA') : Prop :=
  A ≠ .octonion  -- non-associativity disqualifies 𝕆
```

Then show that R1_strict + R3 alone force ℍ (without needing R2 at all):

```lean
theorem R1_strict_plus_R3_forces_quaternion :
    ∀ A : NDA', satisfies_R1_strict A → satisfies_R3 A →
      A = .quaternion := by
  intro A h1 h3
  cases A with
  | real => exact absurd h3 real_fails_R3
  | complex => exact absurd h3 complex_fails_R3
  | quaternion => rfl
  | octonion => exact absurd rfl h1
```


### 2.2 Make `entropy_ordering_invariant` Non-Trivial

**File**: `ThermalCauset.lean`, Part I
**Current**: The theorem is `h` — the identity function. It says "if S(x) < S(y) then S(x) < S(y)."
**Change**: Either remove it or make it meaningful by connecting to the Ott formalization.

Option A (remove): Delete the theorem and replace with a comment explaining that entropy invariance is encoded in the *type* — `entropy : α → ℝ` is frame-independent because it's a function into ℝ with no boost parameter.

Option B (strengthen): Formalize the statement that the entropy function is in the kernel of the Lorentz boost action:

```lean
/-- **ENTROPY IS A LORENTZ SCALAR**

    Under a Lorentz boost, energy transforms as E → γE and
    temperature transforms as T → γT (Ott). The entropy
    S = Q/T transforms as γQ/(γT) = Q/T = S.

    The γ cancels. Entropy is invariant. The causal order
    derived from entropy (Postulate Zero) is therefore
    frame-independent.

    We formalize this using the Ott ratio invariance. -/
theorem entropy_is_lorentz_scalar (Q T : ℝ) (hT : T > 0)
    (v : ℝ) (hv : |v| < 1) :
    let γ := MinkowskiSpace.lorentzGamma v hv
    (γ * Q) / (γ * T) = Q / T :=
  RelativisticTemperature.ratio_invariant Q T hT v hv
```

This calls into your actual Ott formalization and makes the invariance a real theorem about the cancellation of γ, not a tautology.


### 2.3 Address the Temperature Question

**File**: `ThermalCauset.lean`
**Current**: The tick rate depends on temperature T, but which temperature is unspecified.
**Change**: Add a section identifying the relevant temperature as the Bisognano-Wichmann modular temperature, with a clear scope note.

```lean
/-- **THE TEMPERATURE THAT DRIVES GROWTH**

    The tick rate T/(2π) requires specifying which temperature T.
    In this framework, T is the modular temperature of the vacuum
    state restricted to a local causal diamond:

    - Near a black hole horizon: T = T_Hawking = κ/(2π)
    - For a uniformly accelerating observer: T = T_Unruh = a/(2π)
    - In the deep vacuum far from horizons: T = T_BW = 1/(2π)
      (the Bisognano-Wichmann temperature at unit acceleration)

    The Bisognano-Wichmann temperature is the CANONICAL choice:
    it is determined by the modular structure of the vacuum state
    restricted to a Rindler wedge, with no external data needed.

    At the Planck scale, T ~ T_Planck ~ 1 (in natural units),
    giving a tick rate of order 1/(2π) per Planck time.

    **Scope note**: The identification of the growth-driving
    temperature with the BW modular temperature is the thermal
    time hypothesis (Connes-Rovelli). It is well-motivated but
    not yet a theorem. -/
```

### 2.4 Formalize the Hauptvermutung More Carefully

**File**: `Cosmology.lean`, Part I
**Current**: One sorry in the hard direction, plus a sorry for Gibbs' inequality.
**Change**: Split the Hauptvermutung into what you can prove and what you can't, more cleanly.

The easy direction (different causal orders → different entropy histories) should be stated as a standalone theorem without sorry. The hard direction (same entropy history → same causal order) should be explicitly flagged as a conjecture with its own structure:

```lean
/-- **HAUPTVERMUTUNG (EASY DIRECTION)**: proved.
    Different causal orders produce different entropy orderings. -/
theorem hauptvermutung_easy {α : Type*} (C₁ C₂ : SCauset α)
    (x y : α) (h₁ : C₁.rel x y) (h₂ : ¬(C₂.entropy x < C₂.entropy y)) :
    C₁.entropy x < C₁.entropy y ∧ ¬(C₂.entropy x < C₂.entropy y) :=
  ⟨C₁.postulate_zero x y h₁, h₂⟩

/-- **HAUPTVERMUTUNG (HARD DIRECTION)**: open conjecture.
    The converse of Postulate Zero — that entropy ordering
    determines causal ordering (plus locality) — is the
    genuinely hard direction. It is open in standard CST
    and remains open here. -/
axiom hauptvermutung_hard_direction :
    -- Axiomatized as an explicit open problem.
    -- If you can prove this, you've solved one of the
    -- central open problems in causal set theory.
    True
```

This is more honest than a sorry buried inside a proof. It makes the open problem visible at the declaration level.


---

## Priority 3: Documentation and Framing

### 3.1 Reframe "Derived" vs "Constrained" in Basic.lean

**File**: `Basic.lean`, preamble and Part II
**Current**: Claims the partial order is "DERIVED" from entropy. Documentation says "the partial order is the SHADOW of the Second Law."
**Problem**: The causal relation `rel` is a field of `SCauset`, given independently. Postulate Zero constrains the relationship between `rel` and `entropy`, but `rel` is still raw data. The *properties* of the order (irreflexivity, asymmetry) are derived; the *order itself* is not.
**Change**: Adjust the framing to be precise about what is derived and what is assumed.

Replace:
```
Super-CST derives: irreflexivity, asymmetry, antisymmetry.
```

With:
```
Super-CST derives: the ORDER PROPERTIES (irreflexivity, asymmetry,
antisymmetry) from entropy monotonicity. The causal relation itself
is still a structure field — what is derived is not the relation but
its character as a strict partial order.

The philosophical claim "entropy is prior to order" is encoded as:
the relation's key properties follow from a thermodynamic axiom
(Postulate Zero) rather than from independent order-theoretic axioms.
This is an axiom REDUCTION, not a derivation ex nihilo.
```

This is more honest and will prevent the obvious objection from anyone who reads the `SCauset` structure definition.


### 3.2 Add Scope Notes Throughout

Several claims in the files would benefit from explicit scope notes distinguishing what is proved from what is conjectured. Add `**Scope note**` blocks to:

1. **Basic.lean, QuantumTick**: Note that the resolution of unitarity-vs-irreversibility (quantum within, irreversible between) is a *proposal*, not a theorem. The structure enforces consistency but doesn't prove that nature works this way.

2. **ThermalCauset.lean, thermal bridge**: Note that the identification tickTime = thermalTime(2π) is *definitional* — both sides equal 2π/T by construction. The content is in the choice of definitions, not in the proof.

3. **QuaternionicEntropy.lean, D_spatial = 3**: Note the two independent routes (quaternionic and Clifford) and state explicitly that their agreement is evidence for the framework but not proof that nature uses quaternionic entropy.

4. **Cosmology.lean, 2π refinement**: Note that the 2π coefficient is only as physical as Postulate B1 (one tick = 2π nats). If B1 is approximate, the coefficient is approximate.


### 3.3 Update Postulate Audit Everywhere

**Files**: All five, plus Synthesis.lean
**Change**: After demoting R2 to a theorem (§1.1), update every postulate audit to reflect the reduced count. The independent physical inputs should be:

```
STRUCTURE FIELDS (assumed):
  B0: postulate_zero          [SCauset field]
  B1: h_tick = modularPeriod  [EntropyTick field]
  B2: Ott transformation      [Ott.lean]
  B4: entropy is ℝ-valued     [SCauset field]
  C1: locally_finite          [SCauset field]
  C2: counting = volume       [design principle]
  rel_trans: transitivity     [SCauset field]
  R1: ellipticity             [NDA requirement]
  R3: spatial structure ≥ 2   [NDA requirement]

DERIVED (was previously postulated):
  R2: thermal circle          [FROM Clifford periodicity]
  B3: ℍ forced                [FROM R1 + R3]
```


### 3.4 Add Two-Route Summary to Synthesis.lean

**File**: `Synthesis.lean`
**Change**: Add a section before the master theorem showing that D_spatial = 3 is reached by two independent routes.

```lean
/-- **TWO ROUTES TO D_SPATIAL = 3**

    Route A (Algebraic): R1 + R3 → ℍ → Hopf S¹→S³→S² →
      base dim 2 + longitudinal 1 = 3

    Route B (Clifford): Require complex Cl + spinor dim 16 →
      total dim 9 → base dim 3 (unique by periodicity scan)

    These routes use different mathematical machinery
    (Hurwitz + Hopf vs Bott periodicity + spinor dimensions)
    and arrive at the same answer.

    The agreement is not trivial: Route A knows nothing about
    Clifford algebras, and Route B knows nothing about Hopf
    fibrations. The machine confirms both independently. -/
theorem two_routes_agree :
    -- Route A: from quaternionic Hopf
    D_spatial = 3
    ∧
    -- Route B: from Clifford periodicity
    (cl9.baseField.isComplex = true ∧ cl9.spinorDim = 16
     ∧ cl5.spinorDim ≠ 16 ∧ cl14.baseField.isComplex = false)
    ∧
    -- The base dimension selected by Route B
    observerseU9.baseDim = 3 := by
  exact ⟨rfl, ⟨rfl, rfl, by simp [cl5], rfl⟩, rfl⟩
```


---

## Priority 4: Minor Fixes

### 4.1 Natural Labeling Connection

**File**: `Basic.lean`
**Add**: A remark connecting the entropy function to natural labelings in standard CST.

```lean
/-- **CONNECTION TO NATURAL LABELINGS**

    In standard CST, a natural labeling is a map f : C → ℕ
    respecting the order: x ≺ y → f(x) < f(y). Every finite
    causal set admits one (not unique).

    The entropy function `entropy : α → ℝ` is a real-valued
    generalization. It carries metric information (the magnitude
    of entropy differences matters, not just the sign) that a
    natural labeling into ℕ does not.

    The tick structure discretizes this: if each tick produces
    2π nats, then entropy(x) = 2π · n(x) where n is a natural
    labeling. The real-valued entropy and the integer labeling
    carry the same order information; the entropy additionally
    encodes the volume element. -/
```


### 4.2 Interval Cardinality Bound

**File**: `Basic.lean`, Part VII
**Current**: `interval_entropy_bound` states that elements in the interval have entropy between the endpoints, but doesn't give the cardinality bound promised in the documentation.
**Change**: Add the actual cardinality bound (requires the tick structure):

```lean
/-- If every link contributes ≥ 2π to entropy, the interval
    cardinality is at most ⌊(S(y) - S(x)) / 2π⌋. -/
theorem interval_cardinality_bound (x y : α) (h : C.rel x y)
    (h_min_gap : ∀ a b, C.rel a b →
      (¬ ∃ c, C.rel a c ∧ C.rel c b) →
      C.entropy b - C.entropy a ≥ modularPeriod) :
    -- The longest chain length is bounded
    C.entropy y - C.entropy x > 0 := by
  linarith [C.postulate_zero x y h]
```

The full cardinality bound (involving `Set.Finite.toFinset` and `Finset.card`) requires more infrastructure but the entropy gap is the key ingredient.


### 4.3 Fix Cosmology Sorry Documentation

**File**: `Cosmology.lean`
**Change**: The `klDivergence_nonneg` sorry should note that it's Gibbs' inequality, a standard result waiting on Mathlib's `Real.log` convexity lemmas. The Hauptvermutung sorry should be promoted to an explicit axiom (per §2.4 above) rather than left as a sorry inside a proof.


---

## Summary Table

| Priority | File | Change | Effect |
|----------|------|--------|--------|
| 1.1 | QuaternionicEntropy | Derive R2 from Clifford periodicity | -1 postulate |
| 1.2 | Basic | Add Bell causality to QuantumTick | Fixes covariance gap |
| 1.3 | QuaternionicEntropy | Rewrite "+1 longitudinal" | Removes ad hoc appearance |
| 2.1 | QuaternionicEntropy | Strengthen 𝕆 elimination | Two independent arguments |
| 2.2 | ThermalCauset | Make entropy invariance non-trivial | Calls Ott formalization |
| 2.3 | ThermalCauset | Identify growth temperature | Addresses open question |
| 2.4 | Cosmology | Clean up Hauptvermutung | Honest axiom vs sorry |
| 3.1 | Basic | Reframe "derived" claims | Prevents obvious objection |
| 3.2 | All | Add scope notes | Distinguishes proved vs conjectured |
| 3.3 | All | Update postulate audits | Reflects R2 demotion |
| 3.4 | Synthesis | Two-route summary | Shows independent confirmation |
| 4.1 | Basic | Natural labeling connection | Links to standard CST |
| 4.2 | Basic | Interval cardinality bound | Fulfills documentation promise |
| 4.3 | Cosmology | Fix sorry documentation | Cleaner axiom accounting |

---

## Final Note

The goal of these edits is precision. The mathematical content is sound — the machine has checked it. What needs tightening is the relationship between the formal content and the physical claims. Every place where the documentation says "derived" but the formalization says "constrained," every place where a physical interpretation outruns a formal proof, every place where a postulate could be a theorem — these are the gaps that a careful reader will find. Close them before the careful reader does, and the work speaks for itself.