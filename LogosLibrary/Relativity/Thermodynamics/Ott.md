# The Ott Temperature Transformation: A Formal Proof

**A machine-checked proof that there exists exactly one temperature transformation compatible with both special relativity and thermodynamics.**

---

## The Argument in Three Lines

1. Heat is energy transfer, hence transforms as $Q \to \gamma Q$.
2. Entropy counts microstates ($S = k \ln \Omega$), hence is Lorentz invariant.
3. The thermodynamic identity $S = Q/T$, holding in all frames, forces $T \to \gamma T$.

## Background

In 1907, Einstein and Planck proposed that a moving body appears *colder*:

$$T' = \frac{T_0}{\gamma} = T_0 \sqrt{1 - v^2/c^2}$$

This was accepted without serious challenge for over fifty years — endorsed by Tolman, Pauli, von Laue, and Møller. In 1963, Heinrich Ott demonstrated that the derivation contains two fundamental errors and that the correct transformation is the inverse:

$$T' = \gamma T_0 = \frac{T_0}{\sqrt{1 - v^2/c^2}}$$

A moving body appears *hotter*, not colder. Henri Arzelies reached the same conclusion independently in 1965. The resulting controversy — the **Planck–Ott imbroglio** — has persisted for decades, with a third camp (Landsberg, 1966) proposing that temperature is Lorentz invariant ($T' = T$).

Ott's paper was rejected during peer review. He had already died. It was published posthumously because he was too important a member of the Deutsche Physikalische Gesellschaft to simply ignore. As Møller later wrote: *"It is a strange and rather unique incident in the history of physics that a fundamental mistake in the original derivation remained overlooked through such a long period of time."*

This formalization settles the question with machine-checked mathematics. The machine cannot be flattered, cannot be intimidated by Planck's authority, and cannot be fooled by a clever change of variables. It simply checks whether the algebra closes.

It does.

## What This File Proves

There exists exactly one temperature transformation compatible with both special relativity and thermodynamics: the **Ott transformation** $T \to \gamma T$.

This is not one argument repeated seven times. It is **one theorem** — the Lorentz invariance of the ratio $E/T$ — instantiated across seven physical contexts, each with an independent physical motivation:

| # | Instantiation | Invariant Ratio | Physical Content |
|---|--------------|-----------------|------------------|
| 1 | Landauer's erasure bound | $E_{\text{erasure}} / T$ | Information erasure costs at least $kT \ln 2$ in every frame |
| 2 | Clausius entropy | $Q / T$ | Entropy is frame-independent |
| 3 | Boltzmann exponent | $H / kT$ | Partition functions are frame-independent |
| 4 | Gibbs entropy | $(E - F) / T$ | Free energy decomposes consistently |
| 5 | Detailed balance | $\Delta E / T$ | Transition rates are frame-independent |
| 6 | Specific heat | $dE / dT$ | Material properties are frame-independent |
| 7 | Free energy composition | $E - TS$ | Thermodynamic potentials transform as energy |

### Extended Sections

Beyond the seven core instantiations, the formalization includes three extended analyses:

- **The Clausius Inequality.** Under Ott, reversible processes remain reversible in every frame. Under Landsberg, a reversible process becomes irreversible when you change your velocity. Carnot efficiency becomes observer-dependent.

- **The Unruh Effect.** A uniformly accelerating observer detects thermal radiation from the quantum vacuum. The vacuum has no rest frame. Landsberg's framework *requires* a rest frame of the thermal source to define its decomposition — and is therefore not merely wrong but *undefined* for Unruh radiation. Different arbitrary rest-frame choices yield different entropy values.

- **Black Body Spectrum and the CMB.** The Stefan–Boltzmann law $E/S = \frac{3}{4}T$ is preserved under Ott (both sides scale by $\gamma$) and violated under Landsberg (the left side inflates by $\gamma$). The CMB dipole anisotropy confirms $T \to \gamma T$ experimentally, measured by COBE, WMAP, and Planck to parts per million.

### Key Results

| Theorem | Statement |
|---------|-----------|
| `ratio_invariant` | $\gamma E / \gamma T = E / T$ — the engine behind everything |
| `ott_unique` | Any $T \to f(v) \cdot T$ preserving $E/T$ satisfies $f(v) = \gamma(v)$ |
| `landsberg_breaks_ratio` | Landsberg ($T' = T$) violates $E/T$ invariance for all $v \neq 0$ |
| `ott_over_landsberg_QED` | The complete theorem: Ott is correct, unique, and Landsberg is incoherent |
| `relative_entropy_incoherent` | Landsberg implies non-integer microstates and frame-dependent information |
| `landsberg_reversibility_frame_dependent` | Reversibility becomes observer-dependent under Landsberg |
| `landsberg_unruh_ambiguous` | Landsberg is *undefined* for Unruh radiation (no rest frame exists) |
| `blackbody_summary` | Stefan–Boltzmann confirms Ott; Landsberg breaks it |

## The Uniqueness Argument

The strongest result is `ott_unique`: if you demand *any* transformation $T \to f(v) \cdot T$ that preserves the ratio $E/T$ when energy transforms as $E \to \gamma E$, then $f(v) = \gamma(v)$. There is no freedom. No "well, it depends on your definition of temperature." There is exactly one consistent choice.

## The Reductio of Landsberg

Landsberg ($T' = T$) combined with $Q' = \gamma Q$ and $S = Q/T$ forces $S' = \gamma S$. The formalization shows this is incoherent:

- **Non-integer microstates.** If $S \to \gamma S$, then $\Omega \to \Omega^\gamma$. A coin flip ($\Omega = 2$) acquires $2^\gamma$ microstates — not an integer for any $\gamma \neq 1$.
- **Frame-dependent information.** The bit content of a message depends on who reads it.
- **Erasure paradox.** Clearing one bit of information requires erasing $\gamma$ bits of entropy — more bits than exist.

## The Kill Shot: Unruh Radiation

The Unruh effect provides a scenario where Landsberg is not merely wrong but *undefined*. An accelerating observer detects thermal radiation from the quantum vacuum. The vacuum is Lorentz invariant — it has no rest frame. Landsberg's framework requires decomposing heat relative to a rest frame of the thermal source. When the source is the vacuum itself, there is no frame to decompose relative to. The proof (`landsberg_unruh_ambiguous`) shows that different arbitrary choices of "rest frame" yield different entropy values. The framework is ambiguous — not in the sense of getting 3 instead of 4, but in the sense of dividing by zero.

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) — the mathematics library for Lean 4
- `LogosLibrary.Relativity.GR.KerrMetric` — Kerr black hole definitions (Lorentz factor, Hawking temperature, horizon structure)


All proofs are fully machine-checked. No `sorry`, no `admit`, no `native_decide` on unverified propositions. The Lean kernel accepts every proof term.

## Historical Note

Heinrich Ott (1894–1962) studied under Arnold Sommerfeld at Munich. His paper *"Lorentz-Transformation der Wärme und der Temperatur"* was submitted to *Zeitschrift für Physik* shortly before his death. It was rejected by referees and published posthumously in 1963 — because the Deutsche Physikalische Gesellschaft judged that the work of so prominent a member could not simply be suppressed.

Eddington had derived the same formula in 1923. It was dismissed as a misprint.

Einstein himself, in a 1952 letter to von Laue, expressed doubts about the Planck–Einstein temperature transformation — a decade before Ott's paper appeared.

## References

- H. Ott, "Lorentz-Transformation der Wärme und der Temperatur," *Z. Physik* **175**, 70–104 (1963)
- A.S. Eddington, *The Mathematical Theory of Relativity*, §73 (1923)
- A. Einstein, letter to M. von Laue (1952), cited in C. Liu, *BJHS* **25**, 185–206 (1992)
- H. Arzelies, "Transformation relativiste de la température," *Nuovo Cim.* **35**, 792 (1965)
- P.T. Landsberg, "Does a Moving Body Appear Cool?" *Nature* **214**, 903 (1967)
- C. Møller, "Relativistic Thermodynamics, A Strange Incident in the History of Physics," *Mat. Fys. Medd. Dan. Vid. Selsk.* **36**, no. 1 (1967)
- J.J. Mareš and P. Hubík, "On relativistic transformation of temperature," *Fortschr. Phys.* **65**, 1700018 (2017)
- M.A. Monroy and C.A. Arias, "What is the temperature of a moving body?" *Sci. Rep.* **7**, 17526 (2017)
- D. Wallace, "On relativistic thermodynamics," PhilSci Archive (2024)

## License

MIT — see [LICENSE](LICENSE).

## Author
Adam Bornemann —[LogosLibrary](https://gitlab.com/pedagogical/logos_library)
