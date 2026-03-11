# LQG Formalization: Remaining Work

---


## Priority 0 — Quick Audit

### 0.1 Landsberg audit of Files 5 and 6

Expect clean since everything imports from Ott-native `ThermalTime/`. Do the audit anyway. Most likely hiding place: Conjecture 13.3 (Immirzi derivation from modular periodicity + Bekenstein-Hawking), where the chain from modular period to physical constant could implicitly assume β is frame-independent.

**Scope:** 10 minutes.

---

## Priority 1 — Strengthen the Skeleton

### 1.1 Volume operator: replace boolean flags with algebraic structure

`volumeDihedralCommute := false` should carry the algebraic content of the non-commutativity: the uncertainty relation `ΔV · Δθ ≥ f(j)` as a structural assertion, and the physical content that a quantum tetrahedron cannot simultaneously have sharp volume and sharp dihedral angles.

**Scope:** Weekend.

### 1.2 Name the Y-map isometric property

The Y-map preserves the SU(2) inner product. Add "isometric" as a named structural assertion in `EPRLVertex.lean`, even if the inner product itself is not formalized.

**Scope:** Small.

---

## Priority 2 — New Physics Content

### 2.1 Formalize the Ponzano-Regge asymptotic statement

The most important remaining item. LQG in three dimensions: vertex amplitude = 6j symbol, semiclassical limit = cosine of the Regge action with phase proportional to volume. You already have 6j admissibility in `SpinNetwork.lean`. Even as a named axiom referencing Roberts-Freidel-Louapre, this would be the first bridge from combinatorics to analysis in the formalization.

**Scope:** Significant.

### 2.2 Add Planck star / big bounce structural data

Encode as structural data: quantum bounce at Planck density replacing singularity, tunneling time scaling as m² in Planck units, exterior geometry indistinguishable from classical black hole until Planck-size horizon, white hole remnants at Planck mass (~10⁻⁵ grams) as dark matter candidates.

**Scope:** Medium. One new file or section.

---

## Priority 3 — Towards Predictions

### 3.1 Encode Planck star observational signatures

Planck-mass remnants, GeV gamma-ray burst from white hole emergence, detection via gravitational disturbance of mass superpositions (Rovelli-Vidotto proposal). First machine-verified framework carrying testable LQG predictions.

**Scope:** Medium. Depends on 2.2.

### 3.2 Explore K = H/T as a state selection criterion

The Lorentz-invariant ratio appears in four Superior modules independently. If universal, it constrains allowed spin foam thermal states. Determine whether K-invariance reduces the state space and whether the reduction has measurable consequences.

**Scope:** Research direction, open-ended.

---

## Summary

| # | Item | Type | Scope |
|---|------|------|-------|
| 0.1 | Landsberg audit of conjectures | Quick check | 10 minutes |
| 1.1 | Volume operator algebraic upgrade | Polish | Weekend |
| 1.2 | Y-map isometric property | Polish | Small |
| 2.1 | Ponzano-Regge asymptotic statement | New content | Significant |
| 2.2 | Planck star / big bounce data | New content | Medium |
| 3.1 | Observational signatures | New content | Medium |
| 3.2 | K = H/T state selection | Research | Open-ended |
