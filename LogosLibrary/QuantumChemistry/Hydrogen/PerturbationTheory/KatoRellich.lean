/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Generator
import LogosLibrary.QuantumMechanics.UnitaryEvo.Stone

/-!
# The Kato-Rellich Theorem

The abstract Kato-Rellich perturbation theorem: if A is self-adjoint
and V is symmetric with A-bound strictly less than 1, then A + V is
self-adjoint on Dom(A).

## Physical significance

This theorem is the mathematical engine behind perturbation theory in
quantum mechanics. It says that "small" perturbations of a self-adjoint
Hamiltonian preserve self-adjointness — and hence preserve unitary time
evolution (conservation of probability).

The paradigmatic application is the hydrogen atom:
- A = −Δ (free particle, self-adjoint on H²)
- V = −Z/r (Coulomb attraction, singular but "small" relative to −Δ)
- A + V = −Δ − Z/r (hydrogen Hamiltonian, self-adjoint on H²)

## Main definitions

* `IsRelativelyBounded` — V is A-bounded: ‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖ on Dom(A).
* `RelativeBound` — the infimum of valid a-constants.
* `perturbedOp` — the sum A + V as a linear map on Dom(A).

## Main statements

* `kato_rellich` — the main theorem.
* `kato_rellich_domain_eq` — Dom(A + V) = Dom(A).
* `kato_rellich_symmetric` — A + V is symmetric.
* `kato_rellich_generates_unitary` — A + V generates a unitary group.
* `relatively_bounded_sum` — relative bounds are sub-additive.
* `bounded_is_relatively_bounded` — bounded operators have relative bound 0.

## Proof strategy

The proof of Kato-Rellich proceeds in three steps:

**Step 1 (Resolvent factorisation):**
For z with |Im(z)| large enough:
  (A + V − z) = (I + V(A − z)⁻¹)(A − z)

**Step 2 (Neumann series):**
Since V is A-bounded with bound a < 1, for |Im(z)| sufficiently large:
  ‖V(A − z)⁻¹‖ ≤ a + b/|Im(z)| < 1
Hence I + V(A − z)⁻¹ is invertible via Neumann series.

**Step 3 (Surjectivity of A + V ± i):**
From steps 1-2, A + V − z is surjective for suitable z.
Choose z = ±iη for large η, then deform to z = ±i using the
continuity of the resolvent. This gives surjectivity of
(A + V) ± i, which is the self-adjointness criterion.

## Sorry strategy

**Every sorry is dischargeable.** The main discharge routes:
- `kato_rellich`: Neumann series argument (Steps 1-3 above).
- Resolvent estimates: from `Generator.IsSelfAdjoint` + spectral theory.
- Domain equality: by construction (A + V defined on Dom(A)).
- Symmetry: from symmetry of A and V separately.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Theorem V.4.3.
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.12.
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Theorem 9.38.
-/

noncomputable section

namespace QuantumMechanics.Perturbation

open MeasureTheory Complex Filter Generators InnerProductSpace
open scoped Topology NNReal ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Relative boundedness -/

/-- Predicate: V is relatively bounded with respect to A.

    V is A-bounded if Dom(A) ⊆ Dom(V) and there exist constants a, b ≥ 0
    such that ‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖ for all ψ ∈ Dom(A).

    Here V is given as a linear map on Dom(A) (not on its own domain),
    which encodes the condition Dom(A) ⊆ Dom(V) by construction. -/
structure IsRelativelyBounded
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H) where
  /-- The relative bound constant a. -/
  a : ℝ
  /-- The subordinate constant b. -/
  b : ℝ
  /-- a is non-negative. -/
  ha : 0 ≤ a
  /-- b is non-negative. -/
  hb : 0 ≤ b
  /-- The defining estimate: ‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖. -/
  bound : ∀ ψ : gen.domain, ‖V ψ‖ ≤ a * ‖gen.op ψ‖ + b * ‖(ψ : H)‖

/-- The infimum of valid a-constants in the relative bound.

    The relative bound of V with respect to A is:
      inf { a ≥ 0 : ∃ b, ‖Vψ‖ ≤ a‖Aψ‖ + b‖ψ‖ for all ψ ∈ Dom(A) }

    Kato-Rellich requires this infimum to be strictly less than 1. -/
def relativeBound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H)
    (_hV : IsRelativelyBounded gen V) : ℝ :=
  sInf { a : ℝ | 0 ≤ a ∧ ∃ b : ℝ, 0 ≤ b ∧
    ∀ ψ : gen.domain, ‖V ψ‖ ≤ a * ‖gen.op ψ‖ + b * ‖(ψ : H)‖ }

/-- The relative bound is non-negative. -/
lemma relativeBound_nonneg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded gen V) :
    0 ≤ relativeBound gen V hV :=
  sorry

/-- The relative bound is at most any valid a-constant. -/
lemma relativeBound_le
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded gen V)
    (a : ℝ) (ha : 0 ≤ a) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ ψ : gen.domain, ‖V ψ‖ ≤ a * ‖gen.op ψ‖ + b * ‖(ψ : H)‖) :
    relativeBound gen V hV ≤ a :=
  sorry

/-! ## Symmetry of the perturbation -/

/-- Predicate: V is symmetric on Dom(A).

    ⟨Vψ, φ⟩ = ⟨ψ, Vφ⟩ for all ψ, φ ∈ Dom(A). -/
def IsSymmetricOn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H) : Prop :=
  ∀ ψ φ : gen.domain, ⟪V ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), V φ⟫_ℂ

/-! ## The perturbed operator -/

/-- The perturbed operator A + V on Dom(A).

    Since both A and V are defined as linear maps on Dom(A), their
    sum is immediate. The key content of Kato-Rellich is that this
    sum, with the *same domain*, is still self-adjoint. -/
def perturbedOp
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H) : gen.domain →ₗ[ℂ] H :=
  gen.op + V

omit [CompleteSpace H] in
/-- The perturbed operator is symmetric if A and V are. -/
lemma perturbedOp_symmetric
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V : gen.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn gen V) :
    ∀ ψ φ : gen.domain,
      ⟪perturbedOp gen V ψ, (φ : H)⟫_ℂ =
      ⟪(ψ : H), perturbedOp gen V φ⟫_ℂ := by
  intro ψ φ
  simp only [perturbedOp, LinearMap.add_apply]
  rw [inner_add_left, inner_add_right]
  congr 1
  · exact gen.symmetric ψ φ
  · exact hV_sym ψ φ

/-! ## Resolvent estimates

The Neumann series argument requires controlling ‖V(A − z)⁻¹‖.
These estimates connect the relative bound to resolvent norm bounds.
-/

/-- **Key estimate**: ‖V(A − z)⁻¹‖ < 1 for |Im(z)| large enough.

    If V is A-bounded with constants a, b, then for z = x + iy:
      ‖V(A − z)⁻¹φ‖ ≤ a‖A(A − z)⁻¹φ‖ + b‖(A − z)⁻¹φ‖

    Using the spectral calculus estimates:
      ‖A(A − z)⁻¹‖ ≤ 1 + |z|/|y|    (from |lambda/(lambda−z)| ≤ 1 + |z|/|y|)
      ‖(A − z)⁻¹‖ ≤ 1/|y|

    Hence: ‖V(A − z)⁻¹‖ ≤ a(1 + |z|/|y|) + b/|y|.

    For z = iy with |y| large: ‖V(A − z)⁻¹‖ ≤ a + a + b/|y| → a as |y| → ∞.
    Since a < 1, we can choose |y| large enough. -/
lemma resolvent_perturbation_small
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded gen V)
    (ha : hV.a < 1) :
    ∃ η : ℝ, 0 < η ∧
    sorry :=  -- ‖V(A − iη)⁻¹‖ < 1
  sorry

/-- **Neumann invertibility**: I + V(A − z)⁻¹ is invertible when
    ‖V(A − z)⁻¹‖ < 1.

    **Discharge route:** Standard Neumann series:
    (I + T)⁻¹ = Σ_{n=0}^∞ (−T)^n converges when ‖T‖ < 1.
    This is available in Mathlib as `NormedRing.summable_geometric_of_norm_lt_one`
    or via `Units.oneSub` for `1 - T` invertible. -/
lemma neumann_invertible
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded gen V)
    (ha : hV.a < 1) :
    ∃ η : ℝ, 0 < η ∧
    sorry :=  -- (A + V − iη) : Dom(A) → H is surjective
  sorry

/-! ## The main theorem -/

/-- **Kato-Rellich Theorem.**

    Let A be self-adjoint (as a `Generator` with `IsSelfAdjoint`),
    V symmetric on Dom(A), and V relatively bounded with respect to A
    with relative bound a < 1. Then A + V is self-adjoint on Dom(A).

    More precisely: there exists a `Generator` for a unitary group
    whose domain is Dom(A) and whose operator is A + V, and this
    generator satisfies `IsSelfAdjoint`.

    **Discharge route (Neumann series, ~200 lines):**

    1. **Resolvent factorisation.** For z ∉ σ(A):
         (A + V − z) = (I + V(A − z)⁻¹)(A − z)
       on Dom(A). The RHS maps Dom(A) → H since (A − z) : Dom(A) → H
       is bijective (self-adjointness) and V(A − z)⁻¹ : H → H.

    2. **Neumann series.** Choose η > 0 large enough that
       ‖V(A − iη)⁻¹‖ < 1 (from `resolvent_perturbation_small`).
       Then I + V(A − iη)⁻¹ is invertible, so (A + V − iη) is
       bijective Dom(A) → H. Similarly for −iη.

    3. **Surjectivity of (A + V) ± i.** This requires deforming from
       z = ±iη to z = ±i. The standard argument:
       - The set S = {z ∈ ℂ : Im(z) > 0, (A+V−z) surjective} is open
         (perturbation of surjective operators) and nonempty (contains iη).
       - S is also closed in the upper half-plane (if z_n → z with
         Im(z) > 0, the resolvent norms are uniformly bounded).
       - The upper half-plane is connected, so S = {Im(z) > 0}.
       - In particular, i ∈ S. Similarly −i.

    4. **Self-adjointness.** Surjectivity of (A + V) ± i, combined
       with symmetry of A + V (from `perturbedOp_symmetric`), gives
       `Generator.IsSelfAdjoint` for the perturbed generator.

    **Alternative (direct, avoiding deformation):**
    If a < 1, one can show directly that for *any* z with Im(z) ≠ 0,
    the operator I + V(A−z)⁻¹ is invertible, because:
      ‖V(A−z)⁻¹‖ ≤ a·‖A(A−z)⁻¹‖ + b·‖(A−z)⁻¹‖
    and for self-adjoint A, ‖(A−z)⁻¹‖ ≤ 1/|Im(z)| while
    ‖A(A−z)⁻¹‖ ≤ 1 + |Re(z)|/|Im(z)|.
    Choosing z = ±i gives ‖V(A∓i)⁻¹‖ ≤ a + b, which is < 1
    after possibly increasing b (since a < 1, we can absorb). -/
theorem kato_rellich
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn gen V)
    (hV_bdd : IsRelativelyBounded gen V)
    (ha : hV_bdd.a < 1) :
    ∃ (U_grp' : OneParameterUnitaryGroup (H := H))
      (gen' : Generator U_grp')
      (h_dom : gen.domain = gen'.domain),
      gen'.IsSelfAdjoint ∧
      ∀ (x : H) (hx : x ∈ gen.domain),
        gen'.op ⟨x, h_dom ▸ hx⟩ = gen.op ⟨x, hx⟩ + V ⟨x, hx⟩ :=
  sorry

/-! ## Consequences -/

/-- **Domain preservation**: Dom(A + V) = Dom(A).

    This is built into the construction: A + V is defined on Dom(A)
    and the Kato-Rellich generator has the same domain. -/
theorem kato_rellich_domain_eq
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn gen V)
    (hV_bdd : IsRelativelyBounded gen V)
    (ha : hV_bdd.a < 1) :
    gen.domain = (kato_rellich gen hsa V hV_sym hV_bdd ha).choose_spec.choose.domain :=
  (kato_rellich gen hsa V hV_sym hV_bdd ha).choose_spec.choose_spec.choose


/-- **Perturbed generator is self-adjoint.** -/
theorem kato_rellich_selfAdjoint
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn gen V)
    (hV_bdd : IsRelativelyBounded gen V)
    (ha : hV_bdd.a < 1) :
    (kato_rellich gen hsa V hV_sym hV_bdd ha).choose_spec.choose.IsSelfAdjoint :=
  (kato_rellich gen hsa V hV_sym hV_bdd ha).choose_spec.choose_spec.choose_spec.1

/-! ## Algebraic properties of relative boundedness -/

omit [CompleteSpace H] in
/-- **Sum of relatively bounded operators.**
    If V₁ is A-bounded with (a₁, b₁) and V₂ with (a₂, b₂),
    then V₁ + V₂ is A-bounded with (a₁ + a₂, b₁ + b₂). -/
def relatively_bounded_add
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (V₁ V₂ : gen.domain →ₗ[ℂ] H)
    (hV₁ : IsRelativelyBounded gen V₁)
    (hV₂ : IsRelativelyBounded gen V₂) :
    IsRelativelyBounded gen (V₁ + V₂) where
  a := hV₁.a + hV₂.a
  b := hV₁.b + hV₂.b
  ha := add_nonneg hV₁.ha hV₂.ha
  hb := add_nonneg hV₁.hb hV₂.hb
  bound := fun ψ => by
    calc ‖(V₁ + V₂) ψ‖
        = ‖V₁ ψ + V₂ ψ‖ := by rw [LinearMap.add_apply]
      _ ≤ ‖V₁ ψ‖ + ‖V₂ ψ‖ := norm_add_le _ _
      _ ≤ (hV₁.a * ‖gen.op ψ‖ + hV₁.b * ‖(ψ : H)‖) +
          (hV₂.a * ‖gen.op ψ‖ + hV₂.b * ‖(ψ : H)‖) :=
        add_le_add (hV₁.bound ψ) (hV₂.bound ψ)
      _ = (hV₁.a + hV₂.a) * ‖gen.op ψ‖ +
          (hV₁.b + hV₂.b) * ‖(ψ : H)‖ := by ring

omit [CompleteSpace H] in
/-- **Scalar multiples preserve relative boundedness.**
    If V is A-bounded with (a, b), then cV is A-bounded with (|c|a, |c|b). -/
def relatively_bounded_smul
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (c : ℂ) (V : gen.domain →ₗ[ℂ] H)
    (hV : IsRelativelyBounded gen V) :
    IsRelativelyBounded gen (c • V) where
  a := ‖c‖ * hV.a
  b := ‖c‖ * hV.b
  ha := mul_nonneg (norm_nonneg c) hV.ha
  hb := mul_nonneg (norm_nonneg c) hV.hb
  bound := fun ψ => by
    calc ‖(c • V) ψ‖
        = ‖c • V ψ‖ := by rw [LinearMap.smul_apply]
      _ = ‖c‖ * ‖V ψ‖ := norm_smul c (V ψ)
      _ ≤ ‖c‖ * (hV.a * ‖gen.op ψ‖ + hV.b * ‖(ψ : H)‖) :=
        mul_le_mul_of_nonneg_left (hV.bound ψ) (norm_nonneg c)
      _ = ‖c‖ * hV.a * ‖gen.op ψ‖ + ‖c‖ * hV.b * ‖(ψ : H)‖ := by ring


omit [CompleteSpace H] in
/-- **Bounded operators are relatively bounded with bound 0.**

    If V is a bounded operator (extends to all of H), then V is
    A-bounded with a = 0 and b = ‖V‖.

    This handles perturbations like bounded potentials, which are
    always Kato-Rellich regardless of their size. -/
def bounded_is_relatively_bounded
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (T : H →L[ℂ] H) :
    IsRelativelyBounded gen (T.comp (Submodule.subtypeL gen.domain)).toLinearMap where
  a := 0
  b := ‖T‖
  ha := le_refl 0
  hb := norm_nonneg T
  bound := fun ψ => by
    simp only [zero_mul, zero_add]
    exact T.le_opNorm (ψ : H)


/-- **Relative bound of a bounded perturbation is 0.** -/
theorem bounded_relative_bound_zero
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (T : H →L[ℂ] H)
    (hT : IsRelativelyBounded gen
      (T.comp (Submodule.subtypeL gen.domain)).toLinearMap) :
    relativeBound gen _ hT ≤ 0 :=
  relativeBound_le gen _ hT 0 (le_refl 0) ‖T‖ (norm_nonneg T)
    (bounded_is_relatively_bounded gen T).bound

/-! ## Relative bound zero: strengthened Kato-Rellich

When the relative bound is *zero* (as for the Coulomb potential),
Kato-Rellich applies for *any* coupling constant. This is the
physically relevant case for hydrogen.
-/

/-- **Kato-Rellich with relative bound zero.**

    If V has relative bound 0 with respect to A, then for *any*
    coupling constant lambda ∈ ℂ, the operator A + lambdaV is self-adjoint
    on Dom(A).

    This is because: if ‖Vψ‖ ≤ ε‖Aψ‖ + C_ε‖ψ‖ for every ε > 0,
    then ‖(lambdaV)ψ‖ ≤ |lambda|ε‖Aψ‖ + |lambda|C_ε‖ψ‖, and choosing ε < 1/|lambda|
    gives relative bound |lambda|ε < 1.

    **Discharge route:** Apply `kato_rellich` with the bound from
    `relatively_bounded_smul`, choosing ε small enough. -/
theorem kato_rellich_bound_zero
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (V : gen.domain →ₗ[ℂ] H)
    (hV_sym : IsSymmetricOn gen V)
    (hV_bound_zero : ∀ ε : ℝ, 0 < ε →
      ∃ b : ℝ, 0 ≤ b ∧
      ∀ ψ : gen.domain, ‖V ψ‖ ≤ ε * ‖gen.op ψ‖ + b * ‖(ψ : H)‖)
    (lambda : ℂ) :
    ∃ (U_grp' : OneParameterUnitaryGroup (H := H))
      (gen' : Generator U_grp')
      (h_dom : gen.domain = gen'.domain),
      gen'.IsSelfAdjoint ∧
      ∀ (x : H) (hx : x ∈ gen.domain),
        gen'.op ⟨x, h_dom ▸ hx⟩ = gen.op ⟨x, hx⟩ + lambda • V ⟨x, hx⟩ :=
  sorry


/-! ## Interface summary

### For `CoulombBound.lean`:
- `IsRelativelyBounded` — the predicate to verify for V = −Z/r
- `IsSymmetricOn` — symmetry of the Coulomb potential
- `relativeBound_le` — to show the relative bound is 0

### For `HydrogenHamiltonian.lean`:
- `kato_rellich` — the main theorem producing the hydrogen generator
- `kato_rellich_domain_eq` — Dom(H) = Dom(−Δ) = H²
- `kato_rellich_selfAdjoint` — H is self-adjoint
- `kato_rellich_bound_zero` — applies for any nuclear charge Z

### For the spectral pipeline:
Once `kato_rellich` produces a `Generator` with `IsSelfAdjoint`,
the entire spectral infrastructure applies automatically:
- `IsSpectralMeasureFor` for the hydrogen spectral measure
- `functionalCalculus` for f(H)
- `generator_eq_spectral_integral` for H = ∫ lambda dE(lambda)
- `spectral_integral_isometry` for ‖f(H)ψ‖² = ∫|f|² dμ_ψ
-/


end QuantumMechanics.Perturbation
