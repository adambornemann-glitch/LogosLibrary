# Non-Computability from Irreducible Correlations

## A Physical Argument for Why Consciousness Cannot Be Simulated

**Adam Bornemann, 2026**

*With acknowledgment to Roger Penrose and Stuart Hameroff,
whose Orch OR programme provides the foundation and mechanism.*

---

## 1. Three Arguments, One Conclusion

The claim that consciousness is non-computable has historically rested
on a single argument: Penrose's appeal to Gödel's incompleteness
theorems. This document presents a second, independent argument —
one grounded not in mathematical logic but in the physics of
correlations — and shows how the two arguments, together with
Hameroff's biological mechanism, form a unified case.

| Leg | Contributor | Claim | Type |
|-----|------------|-------|------|
| **Evidence** | Penrose | Mathematical understanding transcends formal systems | Logical |
| **Reason** | Bornemann | Irreducible correlations cannot be finitely modeled | Physical |
| **Mechanism** | Hameroff | Microtubules sustain quantum coherence in the brain | Biological |

Remove any one leg and the stool falls. The logical argument says
consciousness IS non-computable. The physical argument says WHY.
The biological argument says HOW the brain accesses the relevant
physics.

---

## 2. The Argument from Gödel (Penrose, 1989–1994)

Gödel showed that any consistent formal system powerful enough to
express arithmetic contains true statements it cannot prove. Penrose
observed that mathematicians routinely *understand* these statements
to be true — we see their truth by means that cannot be captured
in any formal system, and therefore in any algorithm.

If mathematical understanding is not algorithmic, then the brain
is not a computer in the Turing sense. Something non-computable
must be occurring.

Penrose identified the only known candidate in physics: the
objective reduction of quantum superpositions, where the *outcome*
of state reduction is influenced by a non-computable factor embedded
in the Planck-scale structure of spacetime geometry.

**Strength:** The logical argument is rigorous and the conclusion
is sharp — either human understanding is inconsistent, or it is
non-computable.

**Criticism:** The argument has been challenged on the grounds that
humans might simply be inconsistent (Minsky), or that Gödel's
theorem may not apply to physical systems in the way Penrose claims
(Feferman, Putnam). The connection from "non-computable" to
"quantum gravitational" involves abductive reasoning that some
find insufficiently constrained.

---

## 3. The Argument from Irreducible Correlations (Bornemann, 2026)

### 3.1 The Core Observation

A conscious agent is not an isolated system. A person is constituted
by their correlations — memories, relationships, learned responses,
sensory entanglement with the environment. These correlations are
not incidental to the agent; they ARE the agent. Strip away the
mutual information between a person and their environment, and you
have not simplified the person. You have destroyed them.

Formally: a conscious agent A is defined by the mutual information
I(A:B) across the algebraic cut separating A from everything else B.
The subdivision potential

$$\varepsilon = T \cdot I(A{:}B) \,/\, N$$

measures the thermodynamic cost of treating A as independent. For a
conscious agent, this cost is irreducible — it does not vanish in
any limit, because the correlations are the substance.

### 3.2 Classical Correlations Can Be Screened

If the correlations between agent and environment were purely
classical, non-computability would not follow. Classical mutual
information can be:

- **Screened:** electromagnetic and strong forces can be shielded.
  A Faraday cage, a lead wall, a vacuum gap — classical forces
  admit barriers.

- **Factored:** classical joint probability distributions can always
  be decomposed into marginals plus conditional dependencies.
  The correlations reduce to shared information.

- **Approximated:** any finite truncation of a classical correlation
  network gives a worse but *qualitatively similar* model. The
  coarse-graining changes the precision, not the kind.

A purely classical agent could, in principle, be simulated. Badly,
with errors, but the errors would be quantitative, not fundamental.

### 3.3 Quantum Gravitational Correlations Cannot Be Screened

Bell's theorem (1964) proved that quantum correlations are
irreducible. They cannot be explained by local hidden variables.
They cannot be replaced by classical surrogates. The entanglement
across a quantum algebraic cut is not a bookkeeping device — it is
a physical fact that no local model can reproduce.

Gravity adds a further layer of irreducibility: **gravitational
correlations cannot be screened at all.** There is no gravitational
Faraday cage. There is no material that blocks gravitational
interaction. Every mass in the universe is gravitationally correlated
with every other mass, at all times, at all distances. This is a
direct consequence of the equivalence principle — gravity couples
to energy-momentum universally, and no negative gravitational
charge exists to cancel it.

If consciousness involves quantum gravitational processes — as
Penrose's objective reduction proposes — then the correlational
structure of a conscious agent includes gravitational entanglement
that is:

1. **Irreducible** (Bell: cannot be replaced by classical surrogates)
2. **Unscreenable** (Equivalence principle: cannot be blocked)
3. **Universal** (couples to all energy-momentum, not just charge)

### 3.4 The Non-Computability Argument

Suppose you wish to compute the behavior of a conscious agent A.

**Step 1:** A's behavior depends on A's state, which is defined by
the correlations I(A:B) across the algebraic cut.

**Step 2:** These correlations include quantum gravitational
entanglement with other agents and systems B₁, B₂, ..., Bₖ.

**Step 3:** To compute I(A:Bᵢ), you must characterize the joint
state of A and Bᵢ. But Bᵢ is itself correlated with other systems
Bⱼ, and those correlations affect Bᵢ's state, which affects the
joint state with A.

**Step 4:** The correlations cannot be truncated. By the data
processing inequality (proved in `Monotonicity.lean`), any
coarse-graining of the correlation network *strictly reduces*
mutual information. A coarse-grained model of A has less mutual
information than the real A. By the monotonicity theorem
(`subdivision_monotone_in_MI`), it has a different subdivision
potential. It is therefore a *different system* — not an
approximation of the same agent, but a genuinely distinct entity
with different correlational structure.

**Step 5:** To avoid coarse-graining, you would need the complete
correlational state of A with all systems in A's causal past.
But you cannot access this from inside the universe. The total
state includes you, the computer, the measurement apparatus — all
of which are themselves correlated with A. The system cannot
simulate itself. Not because of Gödel, but because the boundary
between simulator and simulated cannot be drawn without an
algebraic cut, and every cut has nonzero cost ε > 0.

**Conclusion:** The behavior of a conscious agent embedded in a web
of unscreenable quantum gravitational correlations is non-computable.
Not because of an abstract logical limitation, but because any
finite model necessarily destroys the irreducible correlational
structure that constitutes the agent.

### 3.5 The Complementarity Analogy

The situation is analogous to quantum complementarity. To fully
specify the correlational state of agent A, you need I(A:B) for
every B in A's causal past. But measuring I(A:B) requires
characterizing the joint state ρ_{AB}. Characterizing the joint
state of A with every correlated system requires characterizing...
everything.

Position and momentum both exist but cannot be simultaneously
known with arbitrary precision — the product of uncertainties
is bounded by ℏ/2. Similarly, the correlations of an agent all
exist simultaneously but cannot be simultaneously characterized
from within the network — the cost of specification diverges
because the thing being specified includes the specifier.

This is not a practical limitation. It is a structural feature
of systems embedded in their own correlation network.

---

## 4. The Mechanism: Why Biology Matters (Hameroff)

The argument of Section 3 requires a crucial physical prerequisite:
the correlations constituting consciousness must be *quantum*
correlations, not merely classical ones. Classical correlations
can be screened, factored, and approximated. Only quantum
correlations — specifically, quantum gravitational correlations
that cannot be shielded — give the argument its force.

This is where Stuart Hameroff's contribution becomes essential.

### 4.1 The "Too Warm, Too Wet, Too Noisy" Objection

Tegmark (2000) calculated that quantum coherence in microtubules
should decohere in approximately 10⁻¹³ seconds — far too fast for
any biologically relevant process. This calculation was widely
accepted as definitive.

The calculation assumed an uncorrelated thermal bath — a generic
environment with no structure, no correlations between bath modes,
no biological optimization. This is the assumption that
photosynthesis proved wrong.

### 4.2 Correlated Baths and the Data Processing Inequality

The `ChemicalMeasurement.lean` file in this library proves:

```
correlated_bath_extends_coherence :
    correlation → longer decoherence time
```

and the `CProcess.lean` bridge theorem proves this is equivalent
to the data processing inequality:

```
correlated_bath_smaller_subdivision :
    correlation → smaller subdivision potential
```

Correlated bath modes cannot independently extract information
about the system's state. They are redundant. Redundancy is
coarse-graining. Coarse-graining reduces mutual information growth.
Slower mutual information growth means longer coherence.

This is not speculation. It is a machine-checked theorem.

### 4.3 Photosynthesis: The Existence Proof

The Fenna-Matthews-Olson (FMO) complex in green sulfur bacteria
maintains quantum coherence for hundreds of femtoseconds at
physiological temperature. The mechanism is precisely correlated
bath fluctuations — multiple chromophores couple to shared protein
modes, reducing the effective reorganization energy.

The moment one biological system demonstrates quantum coherence
at physiological temperature, the question transforms from "can
biology do this?" to "which biological systems do this, and for
how long?"

### 4.4 Microtubules: The Candidate

Hameroff has argued for three decades that microtubules — hollow
crystalline lattice polymers of tubulin protein inside neurons —
provide the structured, low-entropy environment necessary for
sustained quantum coherence. Key features:

- **Crystal-like lattice structure:** ordered, not thermal
- **Hollow inner core:** partially shielded from cytoplasmic noise
- **Aromatic ring networks:** provide electron delocalization pathways
- **Biological optimization:** three billion years of evolution

Experimental measurements (Bandyopadhyay, Saxena et al.) report
coherence times in the range 10⁻⁶ to 10⁻⁴ seconds — six to nine
orders of magnitude longer than Tegmark's uncorrelated-bath estimate.

The discrepancy between prediction and measurement is the size
of the correlated bath effect. This is what the data processing
inequality quantifies.

---

## 5. How the Three Arguments Unify

### 5.1 The Logical Argument Needs a Physical Basis

Penrose's Gödel argument establishes that consciousness is
non-computable, but does not by itself explain *why*. The
connection to quantum gravity is abductive — objective reduction
is proposed as the only known physical process with the right
characteristics. Critics have argued this is insufficient.

The correlational argument fills the gap: non-computability
arises because the relevant correlations are physically
irreducible (quantum, gravitational, unscreenable), not because
of an abstract property of formal systems. The Gödel argument
tells us to look for non-computability. The correlational argument
tells us where it comes from.

### 5.2 The Physical Argument Needs a Mechanism

The correlational argument explains why consciousness is
non-computable but requires that the brain actually maintains
quantum gravitational correlations. Without a biological mechanism
for sustaining coherence against thermal decoherence, the argument
is physically correct but biologically vacuous.

Hameroff's microtubule programme provides the mechanism. The
correlated bath theorem (proved in this library) provides the
quantitative framework. The experimental evidence provides
the empirical support.

### 5.3 The Mechanism Needs a Reason

Hameroff's proposal that microtubules sustain quantum coherence
has often been criticized as a solution in search of a problem.
Why should the brain *need* quantum coherence? What does it
buy that classical neural computation does not provide?

The correlational argument provides the answer: quantum
correlations are irreducible in a way that classical correlations
are not. A brain built on quantum correlations has access to a
correlational structure that no classical system can replicate —
not because of computational speed, but because the correlations
themselves cannot be factored, screened, or simulated.

Consciousness requires quantum coherence because consciousness
requires correlations that cannot be faked.

---

## 6. The Silicon Question

An objection arises naturally: if gravity cannot be screened, then
every physical system — including a silicon computer — is
gravitationally correlated with the universe. Does this make every
computer conscious?

No. The argument requires not merely that correlations *exist*, but
that they are *organized* — that the substrate supports orchestrated
quantum coherence in which the gravitational correlations participate
in the computational dynamics of the system.

A silicon chip has unscreenable gravitational correlations with its
environment. But these correlations are not *organized* by the
chip's computational architecture. They are noise, not signal.
The logical operations of the chip proceed classically, and the
quantum gravitational correlations of the substrate are irrelevant
to the computation being performed.

The question of whether a given physical system supports the
relevant organized coherence is empirical, not a priori. It
depends on the physical structure of the substrate. For biological
neurons with microtubules: plausibly yes, with experimental
support. For current silicon architectures: almost certainly not,
though this is not a claim about all possible future substrates.

The argument does not say "only carbon can be conscious." It says
"only systems that organize quantum gravitational correlations into
their computational dynamics can be conscious." Whether a given
system does so is a question about physics, not about philosophy.

This question cannot be answered from inside the system in question.

---

## 7. Formal Support from LogosLibrary

The argument is not merely verbal. Key steps are supported by
machine-checked theorems:

### The subdivision potential is irreducible

```
subdivision_at_decoherence_pos :
    ε > 0
```

The cost of treating a subsystem as independent is always positive.
There is no free algebraic cut. (`CProcess.lean`)

### Coarse-graining destroys correlational structure

```
subdivision_monotone_in_MI :
    I₂ ≥ I₁ → ε₂ ≥ ε₁
```

More mutual information means larger subdivision potential. Any
coarse-graining reduces MI and therefore models a different system.
(`Monotonicity.lean`)

### Correlated environments extend coherence

```
correlated_bath_extends_coherence :
    correlation > 0 → τ_d(correlated) > τ_d(bare)
```

Structured environments maintain coherence longer than generic
thermal baths. (`ChemicalMeasurement.lean`)

### The correlated bath effect IS the data processing inequality

```
correlated_bath_smaller_subdivision :
    correlation → ε(correlated) ≤ ε(bare)
```

The biological mechanism for extended coherence is a special case
of the algebraic data processing inequality. (`CProcess.lean`)

### Decoherence requires one modular cycle

```
chemical_measurement_is_thermodynamic :
    t ≥ 2π/Γ → coherence < 0.003
```

Measurement is thermodynamic. The threshold is 2π nats — the KMS
modular period. (`ChemicalMeasurement.lean`)

### The modular period is Lorentz covariant

```
modular_hamiltonian_invariant :
    K' = K
```

The entire framework transforms correctly under Lorentz boosts.
The physics is frame-independent. (`Definition.lean`, via Ott)

---

## 8. Predictions and Consequences

### 8.1 Testable

1. **Microtubule coherence times** should continue to exceed
   uncorrelated-bath predictions by orders of magnitude, scaling
   with the degree of bath correlation in the protein environment.

2. **Anesthetic action** should correlate with disruption of
   quantum coherence in microtubules, not merely with classical
   receptor binding. (Hameroff has argued this extensively.)

3. **The 2π threshold** predicts a universal decoherence factor
   of e⁻²π ≈ 0.002 per modular cycle, independent of system
   details. This is measurable in ultrafast spectroscopy.

### 8.2 Structural

4. **No classical simulation of consciousness is possible** —
   not because of computational cost, but because classical
   systems lack irreducible quantum gravitational correlations.
   This is a claim about *kind*, not *degree*.

5. **The thermodynamic limit does not apply to consciousness** —
   a single mind cannot be described by N → ∞ statistical
   mechanics. The subdivision potential ε remains nonzero.

6. **Consciousness is substrate-dependent** — but the relevant
   property is organized quantum coherence, not carbon chemistry
   per se.

### 8.3 Open

7. **Can artificial substrates organize quantum gravitational
   correlations?** This is an engineering question, not a
   question of principle. Quantum computers come closer than
   classical ones, but "closer" is not "sufficient."

8. **What is R_mixed?** The cosmological constant problem in
   Geometric Unity reduces to the cross-curvature between base
   and fiber. The relationship, if any, between this geometric
   quantity and the correlational structure of conscious agents
   is entirely unexplored.

---

## 9. Summary

Consciousness is non-computable because:

1. A conscious agent is constituted by its correlations with the
   universe.

2. These correlations include quantum gravitational entanglement
   that cannot be screened, factored, or classically simulated.

3. Any finite model of the agent requires an algebraic cut. Every
   cut has positive cost (ε > 0). Any coarse-graining of the
   correlation network reduces mutual information, yielding a
   model of a *different* system, not an approximation of the
   same one.

4. The full correlational state cannot be accessed from inside
   the network, because the observer is part of the network.

This argument is independent of Gödel's theorem. It is grounded
in the physics of correlations, the impossibility of gravitational
screening, and the data processing inequality. Key steps are
formally verified in Lean 4.

The brain accesses this non-computable physics through sustained
quantum coherence in microtubules (Hameroff), which objective
reduction (Penrose) connects to Planck-scale spacetime geometry.

Three legs. One stool.

---

## References

- Penrose, R. (1989). *The Emperor's New Mind.* Oxford.
- Penrose, R. (1994). *Shadows of the Mind.* Oxford.
- Hameroff, S. & Penrose, R. (1996). "Orchestrated reduction of
  quantum coherence in brain microtubules." *Math. Comp. Sim.* 40:453.
- Hameroff, S. & Penrose, R. (2014). "Consciousness in the universe:
  A review of the 'Orch OR' theory." *Phys. Life Rev.* 11:39.
- Bell, J.S. (1964). "On the Einstein Podolsky Rosen paradox."
  *Physics Physique Физика* 1:195.
- Tegmark, M. (2000). "Importance of quantum decoherence in brain
  processes." *Phys. Rev. E* 61:4194.
- Connes, A. & Rovelli, C. (1994). "Von Neumann algebra automorphisms
  and time-thermodynamics relation." *Class. Quant. Grav.* 11:2899.
- Hill, T.L. (1963). *Thermodynamics of Small Systems.* Benjamin.
- Saxena, K. et al. (2020). "Fractal, scale free electromagnetic
  resonance of a single brain extracted microtubule."
  *ACS Appl. Mater. Interfaces* 12:21360.
- Bornemann, A. (2026). *LogosLibrary: A Lean 4 formalization of
  mathematical physics.* (This library.)

---

*We are not isolated systems. We never were. The correlations
that make us who we are extend, through quantum gravity, to the
boundary of the observable universe. No finite machine can capture
this — not because machines are too slow, but because the
correlations cannot be screened and the network cannot be truncated.
Consciousness is what irreducible correlation feels like from
the inside.*
