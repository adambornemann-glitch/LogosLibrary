# Differential Möbius Gears

**A type-class framework for conjugation operators satisfying a 4-axiom tooth profile, with comparison infrastructure and a classification theorem for known instances.**

*Part of the Logos Library Formalization Project.*

---

## The Idea

A **Möbius gear** is a conjugation operator J on a mathematical structure that satisfies four axioms:

| Tooth | Axiom | Content |
|:-----:|:------|:--------|
| I | Involution | J² = 1 |
| II | Anti-structure | J reverses multiplication order |
| III | Size preservation | J is an isometry (or antiunitary) |
| IV | Ground state | J fixes a canonical element |

These four properties appear independently across algebra, topology, and operator theory. The framework identifies them as instances of a single interface and provides infrastructure for comparing instances, grading their axiom compliance, and detecting when two gears are "the same twist in different categories" versus "genuinely different twists."

The name is mechanical. Two gears mesh when their tooth profiles interlock. The modular conjugation J of Tomita–Takesaki theory meshes with the Cayley-Dickson conjugation because both satisfy the same 4-axiom profile. The Bott clock conjugation does *not* mesh — it satisfies only 1 of 4 axioms. The comparison is a theorem, not a metaphor.

---

## The Tooth Profile (Axiom by Axiom)

**I. Involution.** Two half-twists = no twist. This is π₁(Möbius strip) = ℤ/2. Every instance satisfies this; it is the minimum requirement for a "twist." An operator satisfying only this axiom is a *bare involution*, not a gear.

**II. Anti-structure.** J(ab) = J(b)·J(a). The twist reverses the order of composition. In algebra this is anti-multiplicativity. In operator theory this is JMJ = M′ (the twist exchanges the algebra and its commutant). An operator satisfying I–II is a *structured involution*.

**III. Size preservation.** ‖J(a)‖ = ‖a‖ in the algebraic setting; ⟨Jψ, Jφ⟩ = ⟨φ, ψ⟩ (antiunitary) in the Hilbert space setting. The twist preserves all metric data. An operator satisfying I–III is a *partial gear*.

**IV. Ground state.** a · J(a) = ‖a‖² in algebra (unit generation); JΩ = Ω in operator theory (vacuum fixed). The twist has a canonical fixed point or reference element. An operator satisfying all four is a *full gear*.

The grading is strict: each axiom requires genuinely new structure beyond the previous ones.

---

## Known Instances

### Full gears (4/4 axioms)

**Cayley-Dickson conjugation** (`qConj`, `octConj`). Acts on the normed division algebras ℝ, ℂ, ℍ, 𝕆. Satisfies the tooth profile at every level of the tower, with restriction coherence: J at level k+1 restricts to J at level k under the Cayley-Dickson embedding. Fixed points = ℝ at every level. The tower terminates at 𝕆 because one more doubling (to the sedenions) produces zero divisors — the tooth profile breaks.

*Proved in:* `MobiusTower.lean` (imported from `HopfTower/`). Zero sorry. Zero axioms.

**Tomita modular conjugation** (`J : H → H`). Acts on a Hilbert space carrying a von Neumann algebra with cyclic separating vector. Satisfies the tooth profile with anti-structure = algebra/commutant exchange (Tomita's theorem), size preservation = antiunitary, ground state = JΩ = Ω. The carrier shaft theorem proves the outer automorphism class is independent of which state (which gear) computes it — the Möbius twist dies in Out(M).

*Proved in:* `MobiusCycle.lean` (imported from `ModularTheory/`). Zero sorry. Tomita's theorem is a bundled structure hypothesis (see Axiom Inventory below).

**Arithmetic local factors** (functional equation ε-factors). Each place v of ℚ contributes a local gear whose tooth profile is: involution = ε(s)·ε(1−s) = 1, anti-structure = local functional equation, size preservation = |ε(½+it)| = 1, ground state = the Gaussian (archimedean) or 𝟙_{ℤ\_p} (p-adic). The tooth profile is *automatic from the types*: constructing a local factor is verifying its profile.

*Proved in:* The Riemann Machine formalization (`Riemann/LocalFactor.lean`). Status: application of the gear framework to number theory.

### Shadow (1/4 axioms)

**Bott clock conjugation** (`clockConjugate : Fin 8 → Fin 8`). The map k ↦ (8 − k) mod 8. Satisfies involution (axiom I). Does *not* satisfy anti-structure (Fin 8 under multiplication is commutative, so anti = homo, and clockConjugate is not even a homomorphism). Has no norm, no ground state. It is a *combinatorial shadow* of the algebraic gears, connected by the bridge map but not intertwining with them.

*Proved in:* `MobiusBridge.lean` (bridge), `FourTooth.lean` (tooth count). Zero sorry. Zero axioms.

### Planned instances

**Christoffel symbols.** The inhomogeneous transformation law ∂²x/∂x∂x under diffeomorphisms is expected to instantiate the tooth profile, with the 6th tooth (functoriality) appearing as the naturality of the transformation law under coordinate changes.

---

## Comparison Infrastructure

### The bridge map (`MobiusBridge.lean`)

The **Möbius bridge** connects the Cayley-Dickson tower to the Bott clock via the fiber dimension map:

```
CD Level    Fiber    Bott Position    clockConj    Result
────────    ─────    ─────────────    ─────────    ──────
0 (ℝ)      S⁰ (0)         0                0        FIXED
1 (ℂ)      S¹ (1)         1                7        SWAP
2 (ℍ)      S³ (3)         3                5        SWAP
3 (𝕆)      S⁷ (7)         7                1        SWAP
```

Key results:
- `twistCost_eq_fiberDim` — the algebraic twist cost equals the topological fiber dimension at every level
- `bottBridge_injective` — the bridge is injective (the tower embeds faithfully into the clock)
- `bottBridge_not_surjective` — the bridge is not surjective (4 levels ≠ 8 positions; {2, 4, 6} are unreachable)
- `intertwining_fails` — the natural candidate for intertwining the CD level-reversal with Bott conjugation provably fails
- `dim_product_constant` — ndaDim(k) × ndaDim(3−k) = 8 at every level (the algebraic reason for the pairing)
- `bridge_coverage` — bridge image ∪ conjugate image covers 5 of 8 Bott positions

### The tooth count (`FourTooth.lean`)

The **4-axiom comparison** grades each instance against the tooth profile:

| Axiom | Cayley-Dickson | Tomita | Bott |
|:-----:|:-:|:-:|:-:|
| I. Involution | ✓ | ✓ | ✓ |
| II. Anti-structure | ✓ | ✓ | ✗ |
| III. Size preservation | ✓ | ✓ | ✗ |
| IV. Ground state | ✓ | ✓ | ✗ |
| **Score** | **4/4** | **4/4** | **1/4** |

### The GNS bridge (`FourTooth.lean`)

The CD and Tomita gears are connected by the GNS construction: given a ∗-representation π : 𝔸 → B(H) with cyclic vector Ω, the algebraic J (star operation) lifts to the Hilbert-space J (Tomita conjugation) via J(π(a)Ω) = π(a∗)Ω = π(J\_CD(a))Ω. This intertwining is *consistent* — unlike the Bott bridge where it provably fails.

### Dual obstructions

Both full-gear instances have a "the twist breaks" theorem:
- **CD:** non-associativity at 𝕆 terminates the tower (algebraic)
- **Tomita:** fermionic anti-periodicity forces F ≡ 0 on ungraded algebras (analytic)

Both say: pushing the twist one step too far destroys the framework.

### Dual coherences

Both full-gear instances have a "the twist is absorbed" theorem:
- **CD:** J\_𝕆 ∘ embed = embed ∘ J\_ℍ (the restriction chain — functorial)
- **Tomita:** \[σ^φ\] = \[σ^ψ\] in Out(M) (the carrier shaft — cohomological)

Both say: the twist is intrinsic, not a choice of presentation.

---

## The Triangle Theorem

The headline result (`the_Mobius_triangle` in `FourTooth.lean`) assembles the full structural comparison as a single conjunction:

```
       Bott J (discrete, 1/4 axioms)
        /                    \
   bridge (FAILS)        bridge (FAILS)
      /                        \
  CD J ─── GNS (consistent) ── Tomita J
  (algebraic, 4/4)          (operator, 4/4)
```

**Verdict.** The algebraic twist (CD) and the operator twist (Tomita) are the same mathematical object in different categories — they satisfy the same 4-axiom interface and are connected by a consistent functor. The combinatorial twist (Bott) is a faithful but lossy shadow — injective as an embedding, but intertwining provably fails.

---

## Roadmap: Teeth 5 and 6

The current tooth profile has four axioms. Two further axioms are planned:

| Tooth | Name | Content | Status |
|:-----:|:-----|:--------|:-------|
| 5 | Sewability | Local J-data assembles globally | Infrastructure built (Sewing Lemma); integration pending |
| 6 | Functoriality | J commutes with morphisms between spaces | Proposal stage |

**Tooth 5** tests whether a gear's local data is globally coherent, using the sewing lemma to check that the defect of almost-additive J-approximations has summable decay. A 5-tooth gear is a 4-tooth gear whose defect satisfies a sewing condition with θ > 1.

**Tooth 6** promotes a family of 5-tooth gears (one per space) to a functor: the gear on X and the gear on Y are compatible through any structure-preserving map f : X → Y. A 6-tooth gear is a natural transformation between spaces; a natural transformation between 6-tooth gears is a morphism of motives.

---

## File Structure

```
MobiusGears/
├── MobiusTower.lean      Tooth profile at ℍ and 𝕆, restriction coherence,
│                         twist visibility, tower termination
│                         (imports HopfTower/)
│
├── MobiusBridge.lean     Bridge map CD → Bott, injection, surjectivity
│                         obstruction, intertwining failure, coverage
│                         (imports CliffordPeriodicity/, HopfTower/)
│
├── MobiusCycle.lean      Tomita J as Möbius half-twist, fermionic KMS
│                         obstruction, carrier shaft orientability
│                         (imports ModularTheory/)
│
└── FourTooth.lean        Triangle theorem: 4-axiom comparison of all three
                          instances, dual obstructions, dual coherences
                          (imports MobiusBridge, MobiusCycle, MobiusTower)
```

---

## Axiom Inventory

**Zero sorry across all four files.**

| File | Axioms / Structure Hypotheses | Notes |
|------|------|-------|
| MobiusTower | None | All proofs by quaternion/octonion arithmetic |
| MobiusBridge | None | All proofs by `fin_cases`, `simp`, `ring` |
| MobiusCycle | `TomitaTheorem` (bundled), `ModularOperatorData`, `ModularConjugationData` | Dischargeable via full Tomita proof (planned) |
| FourTooth | Inherits MobiusCycle's hypotheses | Same status |

The algebraic files (MobiusTower, MobiusBridge) are unconditional. The analytic file (MobiusCycle) carries bundled structure hypotheses from Tomita–Takesaki theory; see the Modular Theory README for the discharge plan.

---

## Dependencies

```
CliffordPeriodicity/     (Bott clock, clockConjugate, field/structure classification)
    │
HopfTower/               (ℍ, 𝕆, qConj, octConj, Hopf maps, fibre actions)
    │
    ├── MobiusTower.lean
    │       │
    ├── MobiusBridge.lean
    │       │
ModularTheory/            (Tomita-Takesaki, cocycle, KMS, carrier shaft)
    │       │
    ├── MobiusCycle.lean
    │       │
    └───────┴── FourTooth.lean
```

Built on [Mathlib](https://github.com/leanprover-community/mathlib4).

---

## References

- Atiyah, Bott, Shapiro, "Clifford modules," *Topology* **3** Suppl. 1 (1964), 3–38
- Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished)
- Takesaki, *Theory of Operator Algebras I–III*, Springer, 1979–2003
- Connes, Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation," *Class. Quant. Grav.* **11** (1994), 2899–2917
- Lawson, Michelsohn, *Spin Geometry*, Princeton (1989)

---

*Author: Adam Bornemann, 2026. Logos Library Formalization Project. MIT License.*