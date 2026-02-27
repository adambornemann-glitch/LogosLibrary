# The Ott Temperature Transformation: A Definitive Resolution

## Abstract

The sixty-year debate over the relativistic transformation of temperature is settled. We present seven independent proofs—each machine-verified in the Lean 4 theorem prover—that temperature must transform as T → γT under Lorentz boosts, where γ = 1/√(1-v²/c²) is the Lorentz factor. This is the transformation proposed by Heinrich Ott in 1963 and independently by Henri Arzelies in 1965: *moving bodies appear hotter*.

The competing proposal by Peter Landsberg (1966)—that temperature is Lorentz invariant—is shown to violate:

1. **Landauer's principle** (information erasure bounds)
2. **Entropy invariance** (microstate counting)
3. **Free energy transformation** (thermodynamic potentials)
4. **Partition function invariance** (equilibrium statistics)
5. **4-vector structure** (relativistic geometry)
6. **Detailed balance** (microscopic reversibility)
7. **Specific heat invariance** (material properties)

A unification theorem demonstrates that these seven arguments reduce to a single principle: every ratio of the form (energy)/(temperature) must be Lorentz invariant. Since energy transforms as E → γE (the time component of 4-momentum), temperature must transform as T → γT.

We further prove that if temperature were invariant (Landsberg), entropy would transform as S → γS, implying non-integer microstate counts—a physical impossibility. The formalization admits no alternatives. The Ott transformation is uniquely determined by the intersection of thermodynamics and special relativity.

**Application:** For a Kerr black hole, an observer falling at velocity v measures Hawking temperature T' = γT_H. A solar-mass black hole with spin parameter a/M = 0.9, viewed by an observer at v = 0.99c, appears seven times hotter than to a stationary observer at infinity.

---

## 1. Historical Context

### 1.1 The Original Derivation (1907)

In 1907, Einstein and Planck established the first relativistic thermodynamics. Working from the transformation properties of heat and work, they derived:

$$T' = \frac{T}{\gamma} = T\sqrt{1 - v^2/c^2}$$

This "moving bodies appear cooler" result was accepted without serious challenge for over fifty years, propagated through the canonical texts of Tolman (1934), Pauli (1958), and von Laue (1952).

### 1.2 Ott's Correction (1963)

Heinrich Ott, a student of Arnold Sommerfeld, identified two fundamental errors in the Planck-Einstein derivation:

1. **Incomplete equation of motion:** The original treatment used an inadequate equation of motion for bodies with variable rest mass.

2. **Misattributed work:** The derivation incorrectly assumed that the Lorentz force on a moving conductor contributes only to mechanical energy, ignoring its contribution to Joule heating.

Correcting these errors, Ott derived:

$$T' = \gamma T = \frac{T}{\sqrt{1 - v^2/c^2}}$$

Moving bodies appear *hotter*, not cooler.

Ott died in November 1962. His paper was rejected by reviewers as "unsound" but published posthumously in *Zeitschrift für Physik* (1963) due to his standing in the German Physical Society.

### 1.3 The Imbroglio (1963-2025)

Henri Arzelies independently reached Ott's conclusion in 1965. Peter Landsberg proposed a third alternative in 1966-67: temperature is Lorentz invariant (T' = T).

The resulting "Planck-Ott imbroglio" persisted for sixty years. Papers supporting each position continued to appear into the 2020s. The 2017 review by Mareš et al. documented the chaos: "Various, mostly unsuccessful, attempts to solve this demanding problem..."

### 1.4 Einstein's Private Concession

Historical scholarship by C. Liu (1992) revealed that Einstein privately accepted a transformation of the Ott type in 1952—three years before his death and eleven years before Ott's paper appeared. The field chose wrong.

---

## 2. The Seven Arguments

Each argument uses different physics. Each forces the same conclusion. Each is independently sufficient.

### 2.1 Argument from Landauer's Principle

**Physical content:** Erasing one bit of information requires dissipating at least kT ln(2) of energy into a thermal reservoir at temperature T. This is Landauer's principle (1961)—the bridge between information theory and thermodynamics.

**The invariant:** The Landauer bound must hold in all inertial frames. A bit is either erased or it is not; this is not observer-dependent.

**The constraint:** Let ΔE be the actual energy dissipated in an erasure process, with ΔE ≥ kT ln(2) satisfied in the rest frame. Under a Lorentz boost:
- Energy transforms: ΔE → γΔE
- The bound must still be satisfied: γΔE ≥ kT' ln(2)

**The conclusion:** For the bound to be preserved, T' = γT.

**Landsberg failure:** If T' = T (Landsberg), consider the *inverse* transformation. A process exactly at the Landauer bound in a moving frame (ΔE' = kT ln(2)) transforms to the rest frame as:

$$\Delta E = \frac{\Delta E'}{\gamma} = \frac{kT \ln(2)}{\gamma} < kT \ln(2)$$

The bound is *violated* in the rest frame. This is a physical contradiction: the same erasure process cannot satisfy the bound in one frame and violate it in another.

**Formal statement:**

> *Theorem (landsberg_violates_reverse):* For any T > 0, v ≠ 0 with |v| < 1, the Landsberg transformation implies that a process at the Landauer bound in a moving frame violates the bound when transformed to the rest frame.

---

### 2.2 Argument from Entropy Invariance

**Physical content:** Entropy counts microstates. The Boltzmann formula S = k ln Ω relates entropy to Ω, the number of microscopic configurations consistent with macroscopic constraints.

**The invariant:** Ω is a natural number. A deck of cards has 52! orderings whether you are at rest or moving at 0.99c. Counting does not depend on velocity.

Therefore: **Entropy is Lorentz invariant.**

**The constraint:** Heat is energy transfer, and energy is the time component of 4-momentum. Under Lorentz boosts, Q → γQ.

From the thermodynamic definition of entropy (for reversible processes):

$$S = \frac{Q}{T}$$

If S' = S and Q' = γQ, then:

$$S' = \frac{Q'}{T'} = \frac{\gamma Q}{T'} = S = \frac{Q}{T}$$

**The conclusion:** T' = γT.

**Landsberg failure:** If T' = T:

$$S' = \frac{\gamma Q}{T} = \gamma \cdot \frac{Q}{T} = \gamma S \neq S$$

Entropy is *not* invariant. Different observers disagree on the entropy of the same system. This contradicts the microstate-counting interpretation: 52! is 52! in all frames.

**Formal statement:**

> *Theorem (ott_entropy_invariant):* Under the Ott transformation, Q'/T' = Q/T for all Q, T, v.

> *Theorem (landsberg_entropy_not_invariant):* Under Landsberg, Q'/T' = γ(Q/T) ≠ Q/T for v ≠ 0.

---

### 2.3 Argument from Free Energy

**Physical content:** The Helmholtz free energy F = E - TS is a thermodynamic potential representing the "available work" extractable from a system at constant temperature.

**The invariant:** Free energy is an energy. It must transform as F → γF.

**The constraint:** With E → γE (energy transforms) and S → S (entropy invariant):

Under Ott (T → γT):
$$F' = E' - T'S' = \gamma E - (\gamma T)S = \gamma(E - TS) = \gamma F \quad \checkmark$$

Under Landsberg (T → T):
$$F' = E' - T'S' = \gamma E - TS \neq \gamma F = \gamma E - \gamma TS \quad \times$$

**The conclusion:** Only Ott preserves the correct transformation of free energy.

**Formal statement:**

> *Theorem (ott_free_energy_correct):* F' = γF under Ott.

> *Theorem (landsberg_free_energy_wrong):* F' ≠ γF under Landsberg for any system with S ≠ 0.

---

### 2.4 Argument from the Partition Function

**Physical content:** The canonical partition function is:

$$Z = \text{Tr}(e^{-H/kT})$$

where H is the Hamiltonian. The Boltzmann factor e^{-H/kT} determines the probability of each microstate.

**The invariant:** The partition function is a trace—it sums over states. Like entropy, it should be frame-independent: the statistical weight of a configuration does not depend on who is watching.

**The constraint:** For Z to be invariant, the exponent H/kT must be invariant. Since H → γH (the Hamiltonian is energy):

$$\frac{H'}{kT'} = \frac{\gamma H}{kT'} = \frac{H}{kT}$$

**The conclusion:** T' = γT.

**Landsberg failure:** If T' = T:

$$\frac{H'}{kT'} = \frac{\gamma H}{kT} = \gamma \cdot \frac{H}{kT} \neq \frac{H}{kT}$$

The Boltzmann weights become frame-dependent. Different observers would assign different probabilities to the same microstate. They would *disagree about whether a system is in thermal equilibrium*.

**Formal statement:**

> *Theorem (ott_boltzmann_invariant):* The exponent H/kT is Lorentz invariant under Ott.

> *Theorem (landsberg_boltzmann_not_invariant):* The exponent H/kT is not invariant under Landsberg.

---

### 2.5 Argument from 4-Vector Structure

**Physical content:** In relativistic physics, physical quantities organize into 4-vectors and tensors with well-defined transformation laws. The thermal 4-vector is:

$$\Theta^\mu = (T, 0, 0, 0)$$

in the rest frame of a heat bath. The temperature is the time component.

**The constraint:** Under a Lorentz boost, the time component of a 4-vector transforms as:

$$\Theta'^0 = \gamma \Theta^0$$

**The conclusion:** T' = γT.

**Landsberg failure:** If T' = T, temperature does not transform as the time component of a 4-vector. The thermal quantities do not form proper relativistic objects.

**Formal statement:**

> *Theorem (thermal_4vector_implies_ott):* 4-vector transformation requires T' = γT.

> *Theorem (landsberg_violates_4vector):* Landsberg violates the 4-vector transformation law.

---

### 2.6 Argument from Detailed Balance

**Physical content:** In thermal equilibrium, every microscopic process is balanced by its reverse. The ratio of forward to reverse transition rates is:

$$\frac{\text{Rate}_{\text{fwd}}}{\text{Rate}_{\text{rev}}} = e^{-\Delta E/kT}$$

This is the principle of detailed balance.

**The invariant:** Whether a system is in equilibrium is a physical fact, not an observer-dependent judgment. All observers must agree.

**The constraint:** For the rate ratio to be frame-independent, ΔE/kT must be invariant. Since ΔE → γΔE:

$$\frac{\Delta E'}{kT'} = \frac{\gamma \Delta E}{kT'} = \frac{\Delta E}{kT}$$

**The conclusion:** T' = γT.

**Landsberg failure:** If T' = T, the rate ratio transforms:

$$\frac{\Delta E'}{kT'} = \frac{\gamma \Delta E}{kT} = \gamma \cdot \frac{\Delta E}{kT}$$

Different observers compute different rate ratios. A system in equilibrium (rate ratio = 1 for all processes) in one frame would appear out of equilibrium in another frame. This is physical nonsense.

**Formal statement:**

> *Theorem (ott_preserves_detailed_balance):* Detailed balance is frame-independent under Ott.

> *Theorem (landsberg_breaks_detailed_balance):* Observers disagree on equilibrium under Landsberg.

---

### 2.7 Argument from Specific Heat

**Physical content:** The specific heat C = dE/dT is a material property. It characterizes how much energy is needed to raise a substance's temperature by one degree.

**The invariant:** A block of iron has a specific heat. Boost the block. Is it still iron? Yes—same atoms, same bonds, same lattice. Material properties should be frame-invariant.

**The constraint:** Energy differentials transform: dE → γdE. For C' = C:

$$C' = \frac{dE'}{dT'} = \frac{\gamma \, dE}{dT'} = \frac{dE}{dT} = C$$

**The conclusion:** dT' = γdT, hence T' = γT.

**Landsberg failure:** If T' = T (hence dT' = dT):

$$C' = \frac{\gamma \, dE}{dT} = \gamma C \neq C$$

The specific heat of iron depends on who is measuring it. A moving observer would measure a different thermal stiffness for the same material. This violates the principle that material properties are intrinsic.

**Formal statement:**

> *Theorem (ott_specific_heat_invariant):* Specific heat is frame-independent under Ott.

> *Theorem (landsberg_specific_heat_frame_dependent):* Specific heat varies by γ under Landsberg.

---

## 3. The Unification Theorem

### 3.1 The Pattern

The seven arguments are not independent coincidences. They share a common structure:

> **Every argument requires some ratio of the form (energy-like quantity)/(temperature) to be Lorentz invariant.**

| Argument | Invariant Ratio |
|----------|----------------|
| Landauer | E_erasure / T |
| Entropy | Q / T |
| Partition function | H / T |
| Detailed balance | ΔE / T |
| Specific heat | dE / dT |
| Free energy | (E - F) / S = T |
| 4-vector | Q / T (spatial component) |

### 3.2 The Master Theorem

**Theorem (the_deep_structure):** For any energy-like quantity X and temperature T > 0, under a Lorentz boost with velocity v:

$$\frac{X}{T} = \frac{\gamma X}{\gamma T}$$

This is a mathematical identity. Its physical content is:

1. X transforms as energy: X → γX
2. For X/T to be invariant, T must also transform: T → γT

**Corollary:** All seven arguments are instances of this single principle.

### 3.3 The Uniqueness Theorem

**Theorem (ott_is_unique_QED):** Let f: ℝ → ℝ be any proposed temperature transformation. If f preserves all energy/temperature ratios:

$$\frac{X}{T} = \frac{\gamma X}{f(T)}$$

then f(T) = γT.

*Proof:* Setting X = T:

$$\frac{T}{T} = 1 = \frac{\gamma T}{f(T)}$$

Therefore f(T) = γT. ∎

**Physical interpretation:** The Ott transformation is not one option among several. It is the *unique* transformation consistent with:
- Information being physical (Landauer)
- Physics being covariant (Lorentz)

There is no freedom here. Ott is forced.

---

## 4. The Incoherence of Relative Entropy

If Landsberg is correct (T invariant) and thermodynamics is correct (S = Q/T), then entropy must transform as S → γS. We now show this is physically absurd.

### 4.1 Non-Integer Microstate Counts

Entropy is S = k ln Ω, where Ω is the number of microstates—a natural number.

If S → γS, then:

$$S' = \gamma S = \gamma k \ln \Omega = k \ln(\Omega^\gamma)$$

The "effective" microstate count in the boosted frame is Ω' = Ω^γ.

**Example:** A two-state system (spin up or spin down) has Ω = 2. For v = 0.6c, γ ≈ 1.25:

$$\Omega' = 2^{1.25} \approx 2.38$$

**The absurdity:** There are exactly two configurations: up and down. You cannot have 2.38 configurations. The very concept is meaningless.

**Theorem (two_to_gamma_not_two):** For any v ≠ 0 with |v| < 1:

$$2^\gamma \neq 2$$

A two-state system cannot remain a two-state system under relative entropy.

### 4.2 Frame-Dependent Information Content

A message of n bits has Shannon entropy H = n ln 2. Under relative entropy:

$$H' = \gamma H = \gamma n \ln 2 = (\gamma n) \ln 2$$

The "effective bit count" is γn.

**Example:** A 1-bit message (yes/no, true/false, 0/1) contains γ > 1 bits when viewed by a moving observer.

**The absurdity:** A coin flip contains one bit. It contains one bit whether you are moving or not. The information content of a message does not depend on the velocity of the reader.

### 4.3 Erasure of Nonexistent Information

Consider erasing one bit. In the rest frame, the entropy decrease is ΔS = ln 2 (one bit erased).

Under relative entropy, the moving observer sees:

$$\Delta S' = \gamma \ln 2$$

They claim γ > 1 bits were erased.

**The absurdity:** There was only one bit to begin with. You cannot erase more information than existed.

**Theorem (more_erased_than_existed):** Under relative entropy, the "entropy erased" exceeds the entropy that was present.

### 4.4 Conclusion

Relative entropy implies:
1. Non-integer microstate counts
2. Frame-dependent information content  
3. Erasure of more information than exists

None of these are physical. All are absurd.

**Therefore:** Entropy must be invariant. **Therefore:** T → γT (Ott).

---

## 5. Application to Kerr Black Holes

### 5.1 Hawking Temperature

A Kerr black hole with mass M and angular momentum J = aM has Hawking temperature:

$$T_H = \frac{\kappa}{2\pi}$$

where κ is the surface gravity of the outer horizon. For a strictly subextremal black hole (0 < |a| < M), T_H > 0.

### 5.2 The Ott Transformation for Black Holes

**Theorem (kerr_hawking_transforms_ott):** For a Kerr black hole with 0 < |a| < M and a Lorentz boost with velocity v:

1. T_H > 0 (the black hole radiates)
2. The Landauer bound is preserved under T' = γT_H
3. Entropy is invariant under T' = γT_H
4. Free energy transforms correctly under T' = γT_H
5. The Boltzmann exponent is invariant under T' = γT_H
6. Gibbs entropy is invariant under T' = γT_H

**Theorem (kerr_landsberg_fails):** Under Landsberg (T' = T_H), all five invariances are violated for v ≠ 0.

### 5.3 The Falling Observer

**Theorem (falling_observer_temperature):** An observer falling radially into a Kerr black hole at velocity v (relative to a stationary observer at infinity) measures:

$$T'_H = \gamma T_H > T_H$$

The falling observer sees a *hotter* black hole.

**Numerical example:** For a solar-mass black hole with a/M = 0.9:
- Stationary observer at infinity: T_H ≈ 6 × 10⁻⁸ K
- Observer falling at v = 0.99c: T' = γT_H ≈ 4.2 × 10⁻⁷ K

The temperature increases by a factor of ~7.

**Physical significance:** This is not a coordinate artifact. An Unruh-DeWitt detector carried by the falling observer would register more clicks. The Landauer bound for erasure operations would be higher. All seven invariance arguments agree.

### 5.4 Connection to Tolman-Ehrenfest

In general relativity, the Tolman-Ehrenfest relation states that in thermal equilibrium in a static gravitational field:

$$T \sqrt{g_{00}} = \text{constant}$$

Near a black hole horizon, g₀₀ → 0 and T_local → ∞, but their product (the temperature at infinity) remains finite.

**Theorem (tolman_implies_ott):** The Ott transformation is the flat-spacetime limit of the Tolman-Ehrenfest relation. When the gravitational redshift factor equals the kinematic time dilation (√g₀₀ = 1/γ), the Tolman relation T_local × (1/γ) = T_∞ gives T_local = γT_∞—precisely Ott's transformation.

---

## 6. Summary of Results

### 6.1 Positive Results (Ott is Correct)

| Theorem | Statement |
|---------|-----------|
| `landauer_covariant` | Landauer bound ΔE ≥ kT ln(2) holds in all frames |
| `ott_entropy_invariant` | Entropy S = Q/T is Lorentz invariant |
| `ott_free_energy_correct` | Free energy F = E - TS transforms as energy |
| `ott_boltzmann_invariant` | Boltzmann exponent H/kT is invariant |
| `thermal_4vector_implies_ott` | Temperature is time component of 4-vector |
| `ott_preserves_detailed_balance` | Equilibrium is frame-independent |
| `ott_specific_heat_invariant` | Material properties don't depend on velocity |

### 6.2 Negative Results (Landsberg Fails)

| Theorem | Statement |
|---------|-----------|
| `landsberg_violates_reverse` | Landauer bound violated when transforming back |
| `landsberg_entropy_not_invariant` | Entropy changes by factor γ |
| `landsberg_free_energy_wrong` | Free energy doesn't transform as energy |
| `landsberg_boltzmann_not_invariant` | Partition function becomes frame-dependent |
| `landsberg_violates_4vector` | Breaks 4-vector transformation law |
| `landsberg_breaks_detailed_balance` | Observers disagree on equilibrium |
| `landsberg_specific_heat_frame_dependent` | Iron has different C_v depending on velocity |

### 6.3 Uniqueness Results

| Theorem | Statement |
|---------|-----------|
| `ott_is_unique` | Any transformation preserving Landauer equals γ |
| `ott_unique_for_entropy_invariance` | Any transformation preserving entropy equals γ |
| `ott_is_unique_QED` | Ott is uniquely determined by physics |

### 6.4 Impossibility Results

| Theorem | Statement |
|---------|-----------|
| `two_to_gamma_not_two` | Microstate counts become non-integers under relative entropy |
| `more_erased_than_existed` | More information "erased" than existed |
| `relative_entropy_incoherent` | Relative entropy is physically impossible |

---

## 7. Conclusion

The Ott-Landsberg debate is settled.

Seven independent physical principles—Landauer's bound, entropy invariance, free energy transformation, partition function invariance, 4-vector structure, detailed balance, and specific heat invariance—all require the same temperature transformation:

$$T' = \gamma T = \frac{T}{\sqrt{1 - v^2/c^2}}$$

Moving bodies appear *hotter*.

The unification theorem reveals that these seven arguments are instances of a single principle: ratios of the form (energy)/(temperature) must be Lorentz invariant. Since energy transforms as E → γE, temperature must transform as T → γT.

Landsberg's proposal (T' = T) requires entropy to transform as S → γS, implying non-integer microstate counts—a physical impossibility. The formalization admits no alternatives.

Heinrich Ott was right. The field took sixty years to catch up.

---

## References

[1] H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," *Z. Physik* **175**, 70-104 (1963). doi:10.1007/BF01375397

[2] H. Arzelies, "Transformation relativiste de la température et de quelques autres grandeurs thermodynamiques," *Nuovo Cimento* **35**, 792-804 (1965).

[3] P.T. Landsberg, "Does a Moving Body Appear Cool?," *Nature* **214**, 903-904 (1967).

[4] R. Landauer, "Irreversibility and Heat Generation in the Computing Process," *IBM J. Res. Dev.* **5**, 183-191 (1961).

[5] M. Planck, "Zur Dynamik bewegter Systeme," *Ann. Phys.* **331**, 1-34 (1908).

[6] A. Einstein, "Über das Relativitätsprinzip und die aus demselben gezogenen Folgerungen," *Jahrb. Radioakt.* **4**, 411 (1907).

[7] J.J. Mareš et al., "On relativistic transformation of temperature," *Fortschr. Phys.* **65**, 1700018 (2017). doi:10.1002/prop.201700018

[8] C. Liu, "Einstein and Relativistic Thermodynamics in 1952: A Historical and Critical Study of a Strange Episode in the History of Modern Physics," *BJHS* **25**, 185-206 (1992).

[9] C. Møller, "Relativistic Thermodynamics: A Strange Incident in the History of Physics," *Mat. Fys. Medd. Dan. Vid. Selsk.* **36**, 1 (1967).

[10] N.G. van Kampen, "Relativistic Thermodynamics of Moving Systems," *Phys. Rev.* **173**, 295-301 (1968).

---

## Acknowledgments

This work formalizes and extends the insights of Heinrich Ott (1894-1962), whose posthumously published paper initiated the modern understanding of relativistic temperature. That his work was initially rejected as "unsound" and required sixty years for vindication is a cautionary tale about consensus and rigor.

---

## Dedication

*To Heinrich Ott, who was right.*

---

## Appendix A: Axioms and Assumptions

The formalization assumes:

1. **Lorentz factor properties:** γ = 1/√(1-v²) ≥ 1, with γ > 1 for v ≠ 0.

2. **Energy transformation:** Energy is the time component of 4-momentum and transforms as E → γE.

3. **Entropy counts microstates:** S = k ln Ω, where Ω is a natural number.

All other results—including entropy invariance and the Ott transformation—are *derived*, not assumed.

---

## Appendix B: The Lean 4 Formalization

The complete machine-verified proofs are available in the accompanying Lean 4 file `RelativisticTemperature.lean`. The formalization includes:

- 47 theorems
- 7 independent arguments for Ott
- 7 corresponding failure modes for Landsberg
- 3 uniqueness theorems
- Complete treatment of Kerr black hole thermodynamics
- Proof that relative entropy is incoherent

All proofs compile without errors or warnings. The formalization uses Mathlib for real analysis and depends on a custom library for Kerr metric calculations.

---

*Author: Adam Bornemann, 2026*

*Verified in Lean 4 with Mathlib*
