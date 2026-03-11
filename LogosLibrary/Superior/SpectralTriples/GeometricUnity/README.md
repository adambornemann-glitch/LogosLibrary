# Geometric Unity in Lean 4

A formalization of the algebraic and dimensional backbone of
Eric Weinstein's Geometric Unity, rebuilt on a 3-dimensional
base manifold X³.

**Author:** Adam Bornemann
**Framework:** Lean 4 / Mathlib
**Status:** Zero `sorry`. All theorems machine-checked.

---

## 1. The Core Observation

Weinstein's original formulation takes X⁴ as the base manifold.
The observerse U¹⁴ = Tot(Met(X⁴)) is 14-dimensional, and the
Clifford algebra Cl(14) ≅ M₁₂₈(ℝ) is **real**. This is the root
of Nguyen's objection: the shiab operator requires a Hermitian
projection π_u: M_k(ℂ) → u(k), and there is no canonical complex
structure on a real matrix algebra. You must complexify by hand.
The question "where does the complex structure come from?" has no
geometric answer in 14 dimensions. Moreover, no signature split
of an even-dimensional space can ever produce a complex Clifford
algebra (the parity obstruction — see `Signature.lean`,
`even_total_dim_never_complex`). The problem is not one bad
signature. It is that dimension 14 has no complex slot at any
signature.

Drop the base to X³.

The metric fiber Sym²₊(ℝ³) is 6-dimensional.
The observerse U⁹ = Tot(Met(X³)) is 9-dimensional.
And 9 mod 8 = 1.

Position 1 in the Bott periodicity table is ℂ.

**Cl(9,0) ≅ M₁₆(ℂ).**

The Clifford algebra is intrinsically complex. Not by choice,
not by convention, not by complexification — by the periodicity
theorem. The complex structure is as forced as the fact that 9
is one more than a multiple of 8.

**Signature robustness.** The chimeric metric on U⁹ may be
indefinite — the DeWitt supermetric gives the conformal mode a
negative sign at λ = −1, producing signature (8,1). This does
not matter. Under the negative-definite convention (eᵢ² = −1
for Riemannian directions), Cl(1,8) has ABS index (1−8) mod 8
= −7 ≡ 1 mod 8 — the same complex slot. Both Cl(9,0) and
Cl(1,8) give M₁₆(ℂ). The tower is preserved under signature
change. The Clifford algebra does not constrain the DeWitt
parameter; it is robust against it. This is proved in
`Signature.lean` (`chimeric_signature_robust`).

Everything else follows.

---

## 2. What Falls Out

From Cl(9) ≅ M₁₆(ℂ), in order:

1. **Spinor fiber = ℂ¹⁶.** Sixteen complex dimensions — exactly one
   chiral spinor representation of Spin(10), which decomposes into
   one complete generation of Standard Model fermions (6 + 3 + 3 +
   2 + 1 + 1 = 16) including a right-handed neutrino.

2. **Structure group = U(16).** Unitary, not orthogonal.
   The Hermitian decomposition M₁₆(ℂ) = u(16) ⊕ iu(16) is canonical.
   Each summand has real dimension 256.

3. **The shiab operator is well-defined.** The pipeline
   ε = π_u ∘ ⋆₉ ∘ q maps Ω²(u(16)) → Ω⁷(u(16)) through four steps,
   each verified. Steps 2 and 4 require complex Clifford algebra —
   satisfied automatically. The pipeline is signature-robust:
   it works for both (9,0) and (1,8).

4. **The gauge action integrates.** Tr(F_A ∧ ε(F_A)) is a 9-form
   on a 9-manifold: 2 + 7 = 9. Top form. Integrable.
   Gauge-invariant by equivariance and cyclic trace.

5. **Three generations from 𝕆.** The seven quaternionic subalgebras
   of the octonions, organized by the Fano plane, partition into
   1 + 2 + 2 + 2 under the SU(3) stabilizer of any distinguished
   subalgebra. The three pairs are the three generations.
   Total: 3 × 16 = 48 Weyl fermions.

6. **n = 3 is unique.** Among all base dimensions n, the observerse
   Met(Xⁿ) has total dimension n(n+3)/2. This falls on a complex
   Bott slot (≡ 1 or 5 mod 8) only for n = 2 and n = 3. But n = 2
   gives Cl(5) ≅ M₄(ℂ) with spinor ℂ⁴ — too small. **X³ is the
   unique base dimension producing ℂ¹⁶ spinors with intrinsically
   complex Clifford algebra.**

---

## 3. The Algebraic Engine: Clifford Periodicity

The foundation is a verified lookup API for the classification of
real Clifford algebras Cl(n,0) and Cl(p,q), implementing the 8-fold
Bott periodicity.

**Methodology.** The eight base cases (Cl(0) through Cl(7)) are
asserted as definitions, not derived from the universal property.
A full derivation would require constructing Cl(n) as a quotient
of the tensor algebra, which is beyond current Mathlib
infrastructure. The base cases are guarded by dimensional
consistency checks (`hDimCheck`). Everything built on top —
periodicity, classification, universal characterization, signature
theory, uniqueness — is machine-checked with zero axioms and
zero sorry.

**Key results:**

- `fieldAt_complex_iff` — Cl(n) is complex iff n ≡ 1 or 5 mod 8
- `complex_implies_simple` — Complex Clifford algebras never split
- `complex_unique_fixed_point` — ℂ is the only field preserved by ⊗ ℍ
- `chimeric_signature_robust` — Cl(9,0) and Cl(1,8) are both M₁₆(ℂ)
- `signature_cancellation` — Adding a (+,−) pair preserves type
- `even_total_dim_never_complex` — Parity obstruction for dim 14
- `unique_complex_matDim16` — m = 9 is the unique complex dim with 16-spinors
- `base_dim_3_unique` — n = 3 is the unique base dim yielding ℂ¹⁶ spinors
- `hermDecomp_matches_cl9` — dim_ℝ M₁₆(ℂ) = 512 = 2⁹

**Sign convention.** Cl(n,0) uses the negative-definite relation
eᵢ² = −1 throughout. The positive-definite convention gives a
different table, related by the Möbius twist k ↦ (8−k) mod 8 on
the Bott clock (see `Mobius.lean`).

**Files:**
`Basic.lean` (foundations), `Table.lean` (periodicity table and step function),
`Clock.lean` (universal characterization), `Mobius.lean` (conjugation symmetries),
`Signature.lean` (indefinite Cl(p,q) via ABS index), `Dimensions.lean`
(uniqueness of dimension 9), `SpinorData.lean` (spinor bundle and Hermitian
decomposition).

---

## 4. The Algebraic Engine: The Fano Plane and Three Generations

The seven imaginary octonion units are organized by the Fano plane
PG(2, F₂) — seven points, seven lines, three points per line, three
lines per point. Each line determines a quaternionic subalgebra of 𝕆.

**The boolean map strategy.** Rather than exhibiting existential
witnesses for subalgebra membership, we characterize each
subalgebra by universal component vanishing: an octonion lies in
the span of a Fano line iff its four off-line imaginary components
are zero. Every closure and associativity proof reduces to
extracting zeros and closing with `ring`.

**The three-generation argument:**

1. 𝕆 contains exactly seven quaternionic subalgebras, one per Fano
   line. *(Proved: `quatSubalgebra_closed`, `quatSubalgebra_associative`)*

2. Fix one subalgebra as distinguished (Knot IV = L₀). The remaining
   six partition into three pairs by intersection class with L₀.
   *(Proved: `fano_line_pairing`, `three_classes`, `class_size_two`)*

3. G₂ = Aut(𝕆) acts transitively on subalgebras, so the choice of
   distinguished subalgebra is canonical.
   *(Axiom: `g2_transitive_on_subalgebras`)*

4. The stabilizer Stab_{G₂}(e₁) ≅ SU(3) preserves the three
   intersection classes, giving exactly three orbits of size two.
   *(Axioms: `three_orbits_part_a`, `three_orbits_part_b`)*

5. Each orbit corresponds to one generation of Standard Model fermions.
   The factor of 3 is a theorem of incidence geometry, not numerology.

**Axiom budget:** 3 axioms from exceptional Lie group theory
(Cartan 1914, Baez 2002, Furey 2016). Everything else — all 28
closure goals, all 7 associativity proofs, the full 7×7 multiplication
table, incidence properties, the boolean map — is proved by finite
computation.

**The Octonion–Clifford connection.** The octonions do not appear
as a Clifford base field because they are not associative. The
`CliffordBaseField` type has exactly three constructors (ℝ, ℂ, ℍ).
The Fano plane is the obstruction that explains why there is no
fourth. The Bott clock encodes which associative algebras survive;
the Fano plane encodes where associativity fails.

**Files:** `Defs.lean` (combinatorial foundations), `BoolMap.lean`
(seven subalgebras, multiplication table), `G2Automorphisms.lean`
(automorphisms, three-generation decomposition).

---

## 5. The Shiab Operator

The shiab (Ship-in-a-Bottle) operator is the map

    ε : Ω²(U⁹; u(16)) → Ω⁷(U⁹; u(16))

that converts gauge curvature 2-forms into 7-forms through the
Clifford algebra Cl(9) ≅ M₁₆(ℂ). It is the engine that makes
the gauge field action Tr(F_A ∧ ε(F_A)) well-defined as a 9-form
on U⁹.

**The four-step pipeline:**

    Step 1  F ∈ Ω²(u(16))           accept input
    Step 2  q(F) ∈ Ω²(M₁₆(ℂ))      quantize into Cl(9)
    Step 3  ⋆₉ q(F) ∈ Ω⁷(M₁₆(ℂ))   Hodge star
    Step 4  π_u(⋆₉ q(F)) ∈ Ω⁷(u(16)) Hermitian projection

Each step is typed and verified. The quantization map q is injective
(36 dimensions, matching so(9) ⊂ u(16)). The Hodge star ⋆₉ is an
involution on 2-forms (sign (−1)^{2·7} = +1). The Hermitian
projection π_u is idempotent and equivariant. Steps 2 and 4 require
complex Clifford algebra — flagged explicitly, satisfied by
Cl(9) ≅ M₁₆(ℂ).

**Why this fails in 14 dimensions.** Cl(14) ≅ M₁₂₈(ℝ). Step 4
needs A†, which requires complex matrices. For real matrices,
(A − Aᵀ)/2 gives the skew-symmetric part so(128), not
skew-Hermitian u(128). To get a unitary gauge group, you must
complexify by hand. In 9 dimensions, no such choice exists.

**Methodological note.** Lean checks all dimensional consistency:
form degrees, algebra dimensions, binomial coefficients, direct sum
decompositions. Qualitative properties (equivariance, gauge
invariance) are recorded as Bool fields set by assertion. The
mathematical content lives in the comments; Lean verifies the
dimensional skeleton. This is stated transparently in the file
headers. A future formalization should promote the Bool assertions
to genuine proof obligations.

**Dimensional comparison:**

| Base | Total | Cl type    | Complex? | Spinor | Shiab | SM gen? |
|:----:|:-----:|:-----------|:--------:|:------:|:-----:|:-------:|
| X²   | U⁵    | M₄(ℂ)     | ✓        | ℂ⁴     | Ω²→Ω³ | ✗ (too small) |
| X³   | U⁹    | M₁₆(ℂ)    | ✓        | ℂ¹⁶    | Ω²→Ω⁷ | ✓ |
| X⁴   | U¹⁴   | M₁₂₈(ℝ)   | ✗        | ℝ¹²⁸   | Ω²→Ω¹² | ✗ (real, too large) |

**Files:** `ShiabComponents.lean` (type signature, Cl(9) theorems,
dimensional accounting, Lagrangian structure, master theorem),
`ShiabOperator.lean` (four-step pipeline, exterior algebra grading,
Hermitian projection, Hodge star, equivariance, gauge action,
well-definedness conditions, cross-checks, master theorem).

---

## 6. The Lagrangian on U⁹

The Lagrangian on U⁹ = Tot(Met(X³)):

    L[g_C, A, Ψ]  =  R_C · vol₉  +  Tr(F_A ∧ ε(F_A))  +  ⟨Ψ, D_A Ψ⟩ vol₉

**Term 1: Scalar curvature.** R_C is the scalar curvature of the
chimeric metric g_C on C = T^v U⁹ ⊕ π*(T*X³). The chimeric metric
is *tautological*: the point u = (gₓ, x) ∈ U⁹ carries a metric gₓ
that determines inner products on both factors. Zero free parameters.
No moduli to stabilize.

**Term 2: Gauge field action.** Tr(F_A ∧ ε(F_A)) is a 9-form via
the shiab. Gauge-invariant by equivariance and cyclic trace.

**Term 3: Dirac action.** ⟨Ψ, D_A Ψ⟩ vol₉ couples the ℂ¹⁶ spinor
to the connection A. One generation of SM fermions.

**Gauge group breaking.** U(16) breaks to the Standard Model gauge
group through the chain:

    U(16) ⊃ SU(16) ⊃ Spin(10) × U(1) ⊃ SU(5) × U(1) ⊃ SU(3) × SU(2) × U(1)
    dim: 256 → 255 → 46 → 25 → 12

The 16 of Spin(10) decomposes as Q_L(6) + ū_R(3) + d̄_R(3) + L(2) +
ē_R(1) + ν_R(1) = 16. The right-handed neutrino is predicted.

**Pullback.** A section σ: X³ → U⁹ (a choice of metric on X³) pulls
back the 9-form Lagrangian to 3-forms on X³ via fiber integration:
R_C produces Einstein-Hilbert gravity + cosmological constant +
scalar fields; Tr(F ∧ ε(F)) produces Yang-Mills; ⟨Ψ, DΨ⟩ produces
fermionic kinetic terms. Gravity is not a separate force — it is
the variational data of the section (δL/δσ = 0).

**The section is a dynamical variable.** There is one overall
coupling constant. The relative coefficients of the three Lagrangian
terms are fixed by the geometry.

**Kaluza-Klein axioms.** Three standard results from Kaluza-Klein
theory are stated as axioms (fiber integral → Einstein-Hilbert,
shiab pullback → Yang-Mills, spinor pullback → fermion decomposition).
They require integration on fiber bundles to formalize and are
**not used** in the master theorem.

**File:** `ObserverseLagrangian.lean`.

---

## 7. The Spectral Bridge

The capstone of the formalization. The spectral action on U⁹ and
the Observerse Lagrangian are **the same theory in two languages**.

**The spectral triple on U⁹** has KO-dimension 1, complex Clifford
type, unitary gauge group U(16), spinor dimension 16, and five
Seeley-DeWitt poles.

**The matching theorem.** A unique, dimensionally consistent,
structure-preserving bijection between the spectral action terms
and the Observerse Lagrangian terms:

    Spectral side              Bridge              Observerse side
    ──────────────             ──────              ───────────────
    a₂ (Seeley-DeWitt)    ←→  gravity span    ←→  R_C · vol₉
    a₄.gauge (mixed term) ←→  gauge span      ←→  Tr(F ∧ ε(F))
    ½⟨Jψ, Dψ⟩             ←→  fermion span    ←→  ⟨Ψ, DΨ⟩ vol₉

**Uniqueness.** The assignment is forced by dimensional analysis.
The gauge term must come from a₄ (only place with Tr(F²)). The
fermionic term must come from the fermionic action (only term with
spinors). The gravity term fills the remaining slot. No permutation
works. There are 3! = 6 possible assignments; only one is consistent.

**The Kaluza-Klein mechanism.** Neither X³ nor Sym²₊(ℝ³) alone
has gauge curvature. The product does. The mixed a₄ term contains
Tr(F²) — gauge fields emerge from the geometry of the fiber bundle,
not from an independent input. This is proved via the Clifford
transmutation: the quaternionic Clifford types of the two factors
combine to produce a complex type on the total space.

**The shiab as spectral origin.** The shiab operator ε replaces
the Hodge star for adjoint-valued forms. The Hermitian projection
in M₁₆(ℂ), which only exists because Cl(9) is complex, is the
mechanism by which the spectral a₄ gauge term becomes the
Observerse gauge term Tr(F ∧ ε(F)). The KO-dimension determines
the projection; the projection determines the shiab.

**Fermionic nontriviality.** The real structure J satisfies JD = −DJ
(ε' = −1 for KO-dim 1). This anticommutation is what makes the
fermionic action ⟨Jψ, Dψ⟩ nonzero. If ε' = +1, the action would
vanish.

**Files:** `SpectralDefs.lean` (KO classification), `SpectralAction.lean`
(Seeley-DeWitt expansion), `ProductGeometry.lean` (fiber bundle
decomposition), `ConcreteSpectrum.lean` (S³ spectrum, coupling
constants), `SpectralBridge.lean` (matching theorem).

---

## 8. The Cosmological Constant

The fiber Sym²₊(ℝ³) carries the DeWitt supermetric and decomposes
as a Riemannian product:

    GL(3,ℝ)/O(3)  ≅  SL(3,ℝ)/SO(3)  ×  ℝ⁺

The SL(3)/SO(3) factor (dim 5) is curved. The ℝ⁺ factor (conformal
scale, dim 1) is flat. The decomposition is orthogonal for all values
of the DeWitt parameter λ, because the cross term G_λ(h₀, cI) vanishes
whenever Tr(h₀) = 0.

SL(3,ℝ)/SO(3) is a Riemannian symmetric space of non-compact type
(Cartan type AI, rank 2). With metric g = Tr(XY) on the tangent space
sym₀(3), the Killing form of sl(3) gives B(X,Y) = 6·Tr(XY), and the
standard formula Ric = −(1/2)·B|_𝔭 yields:

    Ric = −3·g      (Einstein, constant −3 = −n)
    R   = −3 × 5 = **−15**

This is exact, not approximate. It holds for all λ ≠ −1/3 (the
degenerate point where the metric becomes singular). It does not
depend on the base metric of X³, the specific point in Sym²₊, or
any choice in the chimeric bundle. R = −15 is a pure number
determined entirely by n = 3.

**Sign.** Negative fiber curvature produces a positive effective
cosmological constant: Λ_eff = −R_fiber/2 = +15/2. Positive Λ
gives de Sitter spacetime and accelerating expansion. The sign
matches observation.

**Magnitude.** Λ_eff = O(1) in DeWitt units ≈ O(M_P²). The
observed value is Λ_obs ≈ 10⁻¹²² M_P². The discrepancy of ~10¹²²
is the standard cosmological constant problem, shared by every
known approach. No theory gets Λ right from first principles.
The value here — geometric, with no free parameters — is more
principled than treating Λ as a tunable constant, but the hierarchy
problem is inherited.

**Signature robustness.** The DeWitt parameter λ determines the
fiber metric signature: λ > −1/3 gives Riemannian (6,0), λ < −1/3
gives Lorentzian (5,1). Both cases produce complex simple Clifford
algebras (ABS slot 1), so the shiab pipeline works for all
non-degenerate λ. The only constraint is λ ≠ −1/3. A previous
version of this file incorrectly claimed that λ > −1/3 was required
by the Clifford algebra; this was a sign convention error, now
corrected. See `convention_correction` in the file.

**The open question.** The full chimeric scalar curvature
decomposes as R_C = R_base + R_fiber + R_mixed. R_fiber = −15 is
computed. R_base is the Einstein-Hilbert term. R_mixed (the
O'Neill cross-terms from the chimeric connection) is not yet
computed. If R_mixed ≈ +15 − ε for small ε, the effective
cosmological constant would be Λ_eff = ε/2 ≪ 15/2, and the
hierarchy would be resolved by a near-cancellation that is
*geometric*, not fine-tuned. Whether this occurs is one
computation on one bundle — not an infinite sum over unknown fields.

**Axiom:** One (the Einstein property of SL(n)/SO(n), Helgason
Ch. V Thm 4.2).

**File:** `ComputingLambda.lean`.

---

## 9. What Remains Open

**Proved.** The algebraic and dimensional skeleton: Clifford
classification, Bott periodicity, uniqueness of dimension 3,
signature robustness, the shiab pipeline, the Lagrangian structure,
the spectral bridge, the three-generation combinatorics (modulo
three Lie group axioms), gauge group dimensions and breaking chain,
fermion decomposition arithmetic, the fiber scalar curvature
R = −15 and the sign of the cosmological constant.

**Axiomatized (9 total).** Three axioms from exceptional Lie group
theory for the generation argument (G₂ transitivity, SU(3) orbit
structure). Three Kaluza-Klein axioms stated but not used in any
master theorem. Two axioms in the spectral triples section
(chimeric gauge curvature nonzero, fiber volume positive). One
axiom for the cosmological constant (symmetric space Einstein
property, Helgason Ch. V). All are standard results that can be
discharged when Mathlib has sufficient differential geometry
infrastructure.

**Not attempted.** The actual differential-geometric objects — the
chimeric connection, the Dirac operator on U⁹, the fiber integration
map — because Mathlib does not yet have fiber bundles with non-compact
structure groups. Physical predictions (coupling constants, mass
ratios, mixing angles) are downstream of this formalization.

**The central open problem.** What is R_mixed? The full chimeric
scalar curvature decomposes as R_C = R_base + R_fiber + R_mixed.
R_fiber = −15 is computed (section 8). R_base gives Einstein-Hilbert
gravity. R_mixed — the cross-curvature from the chimeric connection —
determines whether the cosmological constant is naturally small.
This is one computation on one bundle.

---

## Dependency Graph

```
CliffordPeriodicity/
  Basic ← Table ← Clock
                 ← Mobius
                 ← Signature
                 ← Dimensions
                 ← SpinorData

FanoPlane/
  Defs ← BoolMap ← G2Automorphisms

GeometricUnity/
  CliffordPeriodicity ←─┐
  FanoPlane ←───────────┤
                        ├── ShiabComponents
                        ├── ShiabOperator
                        ├── ObserverseLagrangian
                        └── ComputingLambda

SpectralTriples/
  SpectralDefs ← SpectralAction ← ProductGeometry ← ConcreteSpectrum
  ObserverseLagrangian ←──────────────────────────── SpectralBridge
```

---

## Theorem and Axiom Accounting

| Module                    | Files | Theorems | Axioms | `sorry` |
|:--------------------------|:-----:|:--------:|:------:|:-------:|
| CliffordPeriodicity       |   7   |   80+    |   0    |    0    |
| FanoPlane                 |   3   |   35+    |   3    |    0    |
| GeometricUnity            |   4   |  210+    |   4*   |    0    |
| SpectralTriples           |   5   |  176     |   2    |    0    |
| **Total**                 | **19**| **500+** | **9**  |  **0**  |

*\*Three of the four GeometricUnity axioms (Kaluza-Klein reductions)
are stated but not used in any master theorem. The fourth
(symmetric space Einstein property) is used in `ComputingLambda.lean`.*

---

## What This Formalization Does and Does Not Do

**Does.** Subjects every algebraic and dimensional claim in
Geometric Unity to a type checker. If any entry in the periodicity
table is wrong, if any form degree doesn't compose, if any
dimensional identity fails, the file does not compile. The
methodology is conditional formalization: base cases are definitions
guarded by consistency checks; everything built on them is proved.

**Does not.** Construct the differential-geometric objects
themselves. The chimeric metric, the Dirac operator, the fiber
integration map are specified by their types and dimensional data,
not by their full mathematical definitions. Qualitative properties
(equivariance, gauge invariance, positivity) are asserted as Bool
fields in several files, stated transparently, and flagged for
future promotion to proof obligations. This boundary is honest
and intentional.

**The Curry-Howard perspective.** This formalization treats
Geometric Unity as a type-checking problem. The physics is a
program; the consistency conditions are its types. If the program
compiles, the types are inhabited, and the dimensional skeleton
is consistent. Whether the program *runs* — whether the actual
differential geometry produces the claimed physics — is a
separate question, downstream of this one, and dependent on
Mathlib infrastructure that does not yet exist.

---

## Acknowledgments

Geometric Unity is Eric Weinstein's theory. The core ideas —
the observerse, the chimeric bundle, the tautological metric,
the shiab operator, gauge-gravity unification through the metric
bundle — are his. The reformulation on X³, the Bott periodicity
argument for intrinsic complexity, the Fano plane generation
argument, the spectral bridge, and the Lean formalization are new.
Errors are mine.

---

*Einstein put the cosmological constant on the left side of his
equation, as geometry. The standard model of cosmology moved it
to the right, as energy. The mathematics does not care — you can
move a term across an equals sign. But the physics changes. On
the right, Λ is an infinite sum over unknown fields that must
cancel to 122 decimal places. On the left, Λ is the scalar
curvature of the space of metrics. This library computes it.*

*R = −15.*

---

## References

- M. F. Atiyah, R. Bott, A. Shapiro, "Clifford modules," Topology 3 Suppl. 1 (1964), 3–38.
- J. Baez, "The Octonions," Bull. AMS 39 (2002), 145–205.
- A. L. Besse, *Einstein Manifolds*, Springer (1987).
- R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82 (1982).
- É. Cartan, "Les groupes réels simples, finis et continus," Ann. Sci. ENS 31 (1914).
- A. Connes, *Noncommutative Geometry*, Academic Press (1994).
- C. Furey, "Standard Model Physics from an Algebra?" Ph.D. thesis (2016).
- S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, AMS (2001).
- H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton (1989).
- T. Nguyen, T. Polya, "A Response to Geometric Unity" (2021).
- E. Weinstein, "Geometric Unity: Author's Working Draft, v 1.0" (2021).