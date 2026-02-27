# Jacobson's Thermodynamic Gravity Requires Ott: A Formal Verification

## Abstract

In 1995, Ted Jacobson demonstrated that Einstein's field equations can be derived from thermodynamic principles applied to local Rindler horizons. We prove, with machine verification in Lean 4, that this derivation uniquely requires Ott's temperature transformation T → γT.

The key insight: for Jacobson's derivation to yield *tensorial* field equations—the same equation for all inertial observers—the Clausius ratio δQ/T must be Lorentz invariant. Since energy flux transforms as δQ → γδQ, temperature must transform as T → γT. This is Ott's 1963 result.

Under Landsberg's alternative (T → T), the Clausius ratio transforms as δQ/T → γ(δQ/T). Different observers would derive different field equations. A "field equation" that depends on observer velocity is not a tensor equation—it is not physics.

We further show that Landsberg violates the Unruh effect itself: the relation T ∝ a (temperature proportional to proper acceleration) cannot hold across frames if temperature is invariant while acceleration transforms as a → γa.

The formalization proves:
1. **Ott succeeds**: The Clausius ratio is Lorentz invariant under T → γT
2. **Landsberg fails**: The Clausius ratio transforms by factor γ under T → T
3. **Ott is unique**: Any transformation preserving the Clausius ratio equals γ
4. **Unruh consistency**: Only Ott preserves T ∝ a across frames

Jacobson's thermodynamic derivation of gravity is not merely *compatible* with Ott—it *uniquely determines* Ott. The temperature transformation is fixed by the requirement that gravity be a tensor theory.

---

## 1. Jacobson's Derivation: The Physical Picture

### 1.1 The Setup

Jacobson's 1995 paper established a remarkable connection: Einstein's field equations follow from demanding that the Clausius relation

$$\delta Q = T \, dS$$

hold for all local Rindler horizons at every spacetime point.

The ingredients:

1. **Local Rindler horizons**: At any point P in spacetime, consider an observer with constant proper acceleration a. This observer perceives a local causal horizon—the Rindler horizon. Quantum field theory (the Unruh effect) tells us this observer sees thermal radiation at temperature T = ℏa/(2πk_B c).

2. **Energy flux**: Matter-energy crossing the horizon appears as heat flow δQ to the accelerated observer. This is the energy component of the stress-energy tensor, integrated over the horizon.

3. **Entropy-area relation**: From black hole thermodynamics, entropy is proportional to horizon area: S = A/(4ℓ_P²). For a local Rindler horizon, changes in area correspond to gravitational focusing via the Raychaudhuri equation.

4. **The Clausius relation**: Demanding δQ = T dS at every local horizon, with T the Unruh temperature and dS determined by area change, yields a constraint on the spacetime geometry.

Jacobson showed this constraint is precisely Einstein's equation:

$$G_{\mu\nu} = 8\pi G \, T_{\mu\nu}$$

Gravity emerges as an equation of state—the condition for local thermodynamic equilibrium of spacetime.

### 1.2 The Implicit Assumption

Jacobson's derivation has a hidden requirement: the field equation must be the *same* for all inertial observers.

Consider two observers at the same spacetime point P:
- **Observer A**: At rest relative to the local Rindler frame
- **Observer B**: Boosted with velocity v relative to A

Both observers can construct local Rindler horizons and apply the Clausius relation. For Jacobson's program to work, they must derive the *same* Einstein equation.

This requires the Clausius ratio δQ/T to be Lorentz invariant. If observer B computes a different value for dS = δQ/T than observer A, they will derive a different field equation.

A field equation that depends on the observer's velocity is not tensorial. It contradicts the foundational principle of general relativity: the laws of physics are the same in all reference frames.

### 1.3 The Question

How must temperature transform under Lorentz boosts for the Clausius ratio to be invariant?

This question—unasked in the 1995 paper—connects Jacobson's thermodynamic gravity to the 60-year debate over relativistic temperature transformation.

---

## 2. The Core Result: Ott is Required

### 2.1 Energy Flux Transformation

Energy is the time component of 4-momentum. Under a Lorentz boost with velocity v, energy transforms as:

$$\delta Q' = \gamma \, \delta Q$$

where γ = 1/√(1-v²/c²) is the Lorentz factor. This is standard relativistic mechanics, not specific to thermodynamics.

### 2.2 The Clausius Ratio Under Ott

Under Ott's transformation (T → γT):

$$\frac{\delta Q'}{T'} = \frac{\gamma \, \delta Q}{\gamma \, T} = \frac{\delta Q}{T}$$

The factors of γ cancel. All observers compute the same entropy change dS = δQ/T. All observers derive the same field equation.

**Theorem (jacobson_1995_with_ott):** Under the Ott transformation T → γT, the Clausius ratio δQ/T is Lorentz invariant.

### 2.3 The Clausius Ratio Under Landsberg

Under Landsberg's transformation (T → T):

$$\frac{\delta Q'}{T'} = \frac{\gamma \, \delta Q}{T} = \gamma \cdot \frac{\delta Q}{T}$$

The boosted observer computes γ times the entropy change of the rest observer. They derive a *different* field equation.

**Theorem (jacobson_1995_requires_ott):** Under the Landsberg transformation T → T, the Clausius ratio transforms as δQ/T → γ(δQ/T). Different observers derive different field equations, violating general covariance.

### 2.4 The Quantitative Failure

The discrepancy is not subtle:

| Boost velocity | γ | Landsberg error |
|----------------|---|-----------------|
| 0.6c | 1.25 | 25% |
| 0.9c | 2.29 | 129% |
| 0.99c | 7.09 | 609% |
| 0.999c | 22.4 | 2140% |

As v → c, the error becomes arbitrarily large. There is no regime where Landsberg is "approximately correct."

---

## 3. Uniqueness: Jacobson Determines Ott

### 3.1 The Theorem

**Theorem (jacobson_uniquely_determines_ott):** Let f: ℝ → ℝ be any function that transforms temperature under boosts: T' = f(v)·T. If f preserves the Clausius ratio for all energy fluxes δQ and temperatures T:

$$\frac{\gamma \, \delta Q}{f(v) \cdot T} = \frac{\delta Q}{T}$$

then f(v) = γ(v) for all subluminal velocities.

### 3.2 The Proof

Set δQ = T = 1. Then:
- Rest frame ratio: 1/1 = 1
- Boosted ratio: γ/f(v)

For these to be equal: γ/f(v) = 1, hence f(v) = γ.

### 3.3 Physical Interpretation

This is not "Ott is one option that works." This is "Ott is the *only* option that works."

The thermodynamic derivation of gravity, taken seriously, leaves no freedom in how temperature transforms. The transformation is fixed by the requirement that Einstein's equation be a proper tensor equation.

---

## 4. The Unruh Connection

### 4.1 Temperature Proportional to Acceleration

The Unruh effect establishes:

$$T = \frac{\hbar a}{2\pi k_B c}$$

Temperature is proportional to proper acceleration: T ∝ a.

This is not a definition or convention—it is a theorem of quantum field theory in curved spacetime, derived from the Bogoliubov transformation between Minkowski and Rindler vacua.

### 4.2 Acceleration Transforms

Proper acceleration is not Lorentz invariant. Under a boost:

$$a' = \gamma a$$

(For acceleration perpendicular to the boost, or in the relevant Rindler scenario.)

### 4.3 The Inevitable Conclusion

For T ∝ a to hold in all frames:
- Rest frame: T = a (in natural units)
- Boosted frame: T' should equal a' = γa

Under Ott (T' = γT = γa): T' = a' ✓

Under Landsberg (T' = T = a): T' = a ≠ γa = a' ✗

**Theorem (landsberg_breaks_unruh_relation):** Under Landsberg, the Unruh relation T ∝ a is violated across frames. The boosted observer measures acceleration γa but (under Landsberg) temperature a. These are inconsistent.

**Theorem (ott_preserves_unruh_relation):** Under Ott, the Unruh relation is automatically preserved: T' = γT = γa = a'.

### 4.4 Why This Matters

The Unruh effect is not optional. It is a consequence of:
- Quantum field theory (vacuum fluctuations exist)
- Special relativity (Lorentz covariance)
- The equivalence principle (local Rindler horizons exist everywhere)

Landsberg contradicts QFT. This is independent of whether you accept Jacobson's thermodynamic derivation of gravity.

---

## 5. Entropy Must Be Frame-Independent

### 5.1 The Statistical Interpretation

Entropy counts microstates: S = k ln Ω. The number Ω is an integer—how many microscopic configurations are compatible with the macroscopic state.

Integers don't Lorentz transform. A deck of cards has 52! orderings whether you're at rest or moving at 0.99c. Counting doesn't depend on velocity.

Therefore: **Entropy is Lorentz invariant.**

### 5.2 Landsberg Violates This

Under Landsberg, the entropy computed from the Clausius relation is:

$$dS' = \frac{\delta Q'}{T'} = \frac{\gamma \, \delta Q}{T} = \gamma \, dS$$

The boosted observer computes γ times as much entropy change. For γ = 7 (at v = 0.99c), they claim 7 times as many microstates were accessed.

This contradicts the statistical interpretation. If entropy counts microstates, and microstates are countable, entropy cannot be frame-dependent.

**Theorem (landsberg_rindler_entropy_failure):** Under Landsberg, different observers compute different entropy changes for the same physical process: dS' = γ·dS ≠ dS.

**Theorem (ott_rindler_entropy_invariant):** Under Ott, all observers agree: dS' = dS.

---

## 6. Physical Consequences

The formalization includes proofs that Ott preserves—and Landsberg violates—numerous physical principles:

### 6.1 Carnot Efficiency

The Carnot efficiency η = 1 - T_cold/T_hot is a ratio of temperatures. Under Ott, ratios are preserved:

$$\eta' = 1 - \frac{\gamma T_{cold}}{\gamma T_{hot}} = 1 - \frac{T_{cold}}{T_{hot}} = \eta$$

All observers agree on the maximum efficiency of heat engines.

Under Landsberg (if reservoirs transform asymmetrically), observers disagree about thermodynamic limits.

### 6.2 Wien's Displacement Law

The peak wavelength of blackbody radiation satisfies λ_max·T = b (Wien's constant).

Under Ott:
- T → γT (temperature increases)
- λ_max → λ_max/γ (wavelength blueshifts)
- Product preserved: (λ_max/γ)(γT) = λ_max·T ✓

This matches the relativistic Doppler effect. Under Landsberg, Wien's law would contradict Doppler.

### 6.3 Detailed Balance

In thermal equilibrium, forward and reverse reaction rates satisfy:

$$\frac{\text{Rate}_{fwd}}{\text{Rate}_{rev}} = e^{-\Delta E / kT}$$

For all observers to agree on equilibrium, the exponent ΔE/kT must be invariant. Since ΔE → γΔE, we need T → γT.

Under Landsberg, observers disagree about whether a system is in equilibrium.

### 6.4 The Zeroth Law

If A is in equilibrium with B, and B with C, then A is in equilibrium with C. "In equilibrium" means "at the same temperature."

Under Ott, if T_A = T_B in one frame, then γT_A = γT_B in all frames. Equilibrium is preserved.

Under Landsberg (with asymmetric boosts), two systems at the same temperature could appear at different temperatures to a moving observer.

### 6.5 Information Mass

Landauer's principle: erasing one bit requires energy kT ln 2.

By E = mc², this energy has mass equivalent m = kT ln 2 / c².

Under Ott, T → γT, so m → γm. Mass transforms correctly (like energy).

Under Landsberg, the "mass of information" would be frame-invariant, contradicting E = mc².

---

## 7. The Logical Structure

```
                    Jacobson's Derivation (1995)
                              ↓
              "δQ = T dS at all local Rindler horizons
               must yield the same field equation for
               all inertial observers"
                              ↓
              δQ/T must be Lorentz invariant
                              ↓
              ∀ f, (f preserves δQ/T) → (f = γ)
                              ↓
                      T → γT (Ott)
```

The contrapositive:

```
                    ¬Ott (e.g., Landsberg)
                              ↓
              δQ/T is NOT Lorentz invariant
                              ↓
              Different observers derive different field equations
                              ↓
              Either gravity isn't thermodynamic,
              or gravity isn't tensorial
```

Since gravity IS tensorial (a century of experimental confirmation), the thermodynamic interpretation forces Ott.

---

## 8. Connection to Previous Work

### 8.1 The Ott Formalization

This work builds on the machine-verified proof that Ott's transformation is uniquely required by seven independent physical principles:

1. Landauer's principle (information erasure bounds)
2. Entropy invariance (microstate counting)
3. Free energy transformation (thermodynamic potentials)
4. Partition function invariance (equilibrium statistics)
5. 4-vector structure (relativistic geometry)
6. Detailed balance (microscopic reversibility)
7. Specific heat invariance (material properties)

The Jacobson connection provides an eighth argument—and arguably the most powerful one, because it ties temperature transformation directly to the structure of spacetime.

### 8.2 What Jacobson Adds

The previous seven arguments show Ott is required for thermodynamic consistency. Jacobson shows Ott is required for *gravitational* consistency.

If you believe:
- Gravity is described by Einstein's equations
- Einstein's equations are tensorial (same in all frames)
- Gravity has thermodynamic underpinnings

Then you must accept Ott. There is no alternative.

### 8.3 Einstein's Private View

Historical scholarship by C. Liu (1992) revealed that Einstein privately accepted a transformation of the Ott type in 1952—three years before his death. The man who initiated relativistic thermodynamics in 1907 ultimately recognized the correct answer, even if he never published it.

---

## 9. Summary of Formal Results

### 9.1 Core Theorems

| Theorem | Statement |
|---------|-----------|
| `jacobson_1995_with_ott` | Clausius ratio is invariant under Ott |
| `jacobson_1995_requires_ott` | Clausius ratio transforms by γ under Landsberg |
| `jacobson_uniquely_determines_ott` | Ott is the unique ratio-preserving transformation |
| `jacobson_complete` | Unified statement of all three results |

### 9.2 Unruh Consistency

| Theorem | Statement |
|---------|-----------|
| `ott_preserves_unruh_relation` | T' = γT matches boosted Unruh prediction a' = γa |
| `landsberg_breaks_unruh_relation` | T' = T contradicts boosted Unruh prediction |
| `landsberg_rindler_failure_summary` | Complete catalog of Landsberg failures |

### 9.3 Entropy Invariance

| Theorem | Statement |
|---------|-----------|
| `ott_rindler_entropy_invariant` | dS' = dS under Ott |
| `landsberg_rindler_entropy_failure` | dS' = γ·dS under Landsberg |

### 9.4 Physical Consequences (Extras)

| Theorem | Statement |
|---------|-----------|
| `ott_carnot_invariant` | Carnot efficiency is frame-independent |
| `ott_wien_doppler_consistent` | Wien's law consistent with Doppler |
| `ott_preserves_equilibrium` | Thermal equilibrium is frame-independent |
| `ott_chemical_potential_invariant` | μ/T ratio preserved |
| `ott_bekenstein_consistent` | Bekenstein bound transforms correctly |

---

## 10. Conclusion

Jacobson's 1995 derivation of Einstein's equations from thermodynamics is one of the deepest insights in theoretical physics. It suggests gravity is not fundamental but emergent—an equation of state for spacetime, arising from the collective behavior of underlying degrees of freedom.

This formalization proves that the derivation carries a hidden requirement: temperature must transform as T → γT under Lorentz boosts. This is Ott's 1963 result, vindicated by machine verification.

The requirement is not optional. Under Landsberg (T → T):
- The Clausius ratio becomes frame-dependent
- Different observers derive different field equations
- The Unruh relation is violated
- Entropy becomes observer-dependent
- Thermodynamics contradicts general covariance

None of these are acceptable. Ott is not one choice among many—it is the unique transformation compatible with thermodynamic gravity.

Jacobson's derivation was always implicitly using Ott. We have made it explicit.

---

## References

[1] T. Jacobson, "Thermodynamics of Spacetime: The Einstein Equation of State," Phys. Rev. Lett. **75**, 1260 (1995). arXiv:gr-qc/9504004

[2] H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," Z. Physik **175**, 70-104 (1963). doi:10.1007/BF01375397

[3] T. Padmanabhan, "Thermodynamical Aspects of Gravity: New Insights," Rep. Prog. Phys. **73**, 046901 (2010). arXiv:0911.5004

[4] W.G. Unruh, "Notes on black-hole evaporation," Phys. Rev. D **14**, 870 (1976).

[5] T. Jacobson, "Entanglement Equilibrium and the Einstein Equation," Phys. Rev. Lett. **116**, 201101 (2016). arXiv:1505.04753

[6] C. Liu, "Einstein and Relativistic Thermodynamics in 1952," BJHS **25**, 185-206 (1992).

---

## Appendix: The Lean 4 Formalization

The complete machine-verified proofs are in `Jacobson.lean`. The formalization:

- Imports the Ott temperature transformation module
- Defines the Clausius ratio and its transformations
- Proves invariance under Ott, failure under Landsberg
- Establishes uniqueness of the Ott transformation
- Connects to Unruh effect consistency
- Includes physical applications (Carnot, Wien, etc.)

All proofs compile without errors. The logical structure is:

1. `jacobson_1995_requires_ott`: Landsberg breaks the derivation
2. `jacobson_1995_with_ott`: Ott saves the derivation  
3. `jacobson_uniquely_determines_ott`: Ott is uniquely determined
4. `jacobson_complete`: All three in one theorem

Dependencies: Mathlib for real analysis, custom Lorentz factor library.

---

*Author: Adam Bornemann, 2026*

*Verified in Lean 4 with Mathlib*
