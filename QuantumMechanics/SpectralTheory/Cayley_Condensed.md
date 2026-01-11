# The Cayley Transform — Definition Reference

**Author:** Adam Bornemann  
**Created:** 1-9-2026  
**Updated:** 1-10-2026

Von Neumann's Bridge from Unbounded to Bounded Spectral Theory (1929-1932)

---

## Table of Contents

1. [Unitary Operators: Preliminaries](#unitary-operators-preliminaries)
2. [The Cayley Transform](#the-cayley-transform)
3. [Isometry Property](#isometry-property)
4. [Surjectivity](#surjectivity)
5. [Unitarity](#unitarity)
6. [The Eigenvalue -1 Correspondence](#the-eigenvalue--1-correspondence)
7. [The Inverse Cayley Transform](#the-inverse-cayley-transform)
8. [Consequences of Unitarity](#consequences-of-unitarity)
9. [Spectral Correspondence](#spectral-correspondence)
10. [Möbius Map Algebra](#möbius-map-algebra)
11. [Bounded Below Correspondence](#bounded-below-correspondence)
12. [Normal Operators: Bounded Below ⟺ Invertible](#normal-operators-bounded-below--invertible)
13. [Point Spectrum & Approximate Eigenvalue Correspondence](#point-spectrum--approximate-eigenvalue-correspondence)
14. [Main Theorems](#main-theorems)
15. [Spectral Connection: Bridge to Functional Calculus](#spectral-connection-bridge-to-functional-calculus)
16. [Summary Counts](#summary-counts)

---

## Unitary Operators: Preliminaries

### Definitions

```lean
def Unitary (U : H →L[ℂ] H) : Prop :=
  U.adjoint * U = 1 ∧ U * U.adjoint = 1
```

### Lemmas

```lean
lemma Unitary.inner_map_map {U : H →L[ℂ] H} (hU : Unitary U) (x y : H) :
    ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ

lemma Unitary.norm_map {U : H →L[ℂ] H} (hU : Unitary U) (x : H) : 
    ‖U x‖ = ‖x‖

lemma Unitary.injective {U : H →L[ℂ] H} (hU : Unitary U) : 
    Function.Injective U

lemma Unitary.surjective {U : H →L[ℂ] H} (hU : Unitary U) : 
    Function.Surjective U

lemma Unitary.isUnit {U : H →L[ℂ] H} (hU : Unitary U) : 
    IsUnit U
```

---

## The Cayley Transform

### Definitions

```lean
noncomputable def cayleyTransform {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • Resolvent.resolvent_at_neg_i gen hsa
```

### Lemmas

```lean
lemma cayleyTransform_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    let ψ := Resolvent.resolvent_at_neg_i gen hsa φ
    let hψ := Resolvent.resolvent_solution_mem_plus gen hsa φ
    cayleyTransform gen hsa φ = gen.op ⟨ψ, hψ⟩ - I • ψ
```

---

## Isometry Property

### Theorems

```lean
theorem cayleyTransform_isometry {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ φ : H, ‖cayleyTransform gen hsa φ‖ = ‖φ‖
```

---

## Surjectivity

### Theorems

```lean
theorem cayleyTransform_surjective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Function.Surjective (cayleyTransform gen hsa)
```

---

## Unitarity

### Theorems

```lean
theorem cayleyTransform_unitary {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    Unitary (cayleyTransform gen hsa)
```

---

## The Eigenvalue -1 Correspondence

### Theorems

```lean
theorem cayley_neg_one_eigenvalue_iff {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = -φ) ↔
    (∃ ψ : gen.domain, (ψ : H) ≠ 0 ∧ gen.op ψ = 0)
```

---

## The Inverse Cayley Transform

### Definitions

```lean
noncomputable def inverseCayleyOp (U : H →L[ℂ] H)
    (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) :
    LinearMap.range (ContinuousLinearMap.id ℂ H - U) →ₗ[ℂ] H
```

### Lemmas

```lean
lemma one_minus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ

lemma one_plus_cayley_apply {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩

lemma range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ∀ ψ : H, ψ ∈ gen.domain →
      ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ = (2 * I) • ψ
```

### Theorems

```lean
theorem inverse_cayley_relation {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (2 * I) • gen.op ⟨ψ, hψ⟩ = I • ((ContinuousLinearMap.id ℂ H + U) φ)

theorem inverse_cayley_formula {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    let U := cayleyTransform gen hsa
    (ContinuousLinearMap.id ℂ H - U) φ = (2 * I) • ψ ∧
    (ContinuousLinearMap.id ℂ H + U) φ = (2 : ℂ) • gen.op ⟨ψ, hψ⟩

theorem inverse_cayley_domain {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ψ = ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - U) φ)

theorem cayley_bijection {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    ((-I) / 2) • ((ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa) φ) = ψ ∧
    ((1 : ℂ) / 2) • ((ContinuousLinearMap.id ℂ H + cayleyTransform gen hsa) φ) = gen.op ⟨ψ, hψ⟩

theorem inverseCayleyOp_symmetric (U : H →L[ℂ] H)
    (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) :
    ∀ ψ φ : LinearMap.range (ContinuousLinearMap.id ℂ H - U),
      ⟪inverseCayleyOp U hU h_one h_neg_one ψ, (φ : H)⟫_ℂ =
      ⟪(ψ : H), inverseCayleyOp U hU h_one h_neg_one φ⟫_ℂ
```

---

## Consequences of Unitarity

### Lemmas

```lean
lemma cayleyTransform_comp_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).comp (cayleyTransform gen hsa).adjoint =
    ContinuousLinearMap.id ℂ H

lemma cayleyTransform_adjoint_comp {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H

lemma cayleyTransform_isUnit {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    IsUnit (cayleyTransform gen hsa)

lemma cayleyTransform_adjoint_comp' {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (cayleyTransform gen hsa).adjoint.comp (cayleyTransform gen hsa) =
    ContinuousLinearMap.id ℂ H
```

### Theorems

```lean
theorem cayleyTransform_norm_one {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ‖cayleyTransform gen hsa‖ = 1
```

---

## Spectral Correspondence

### Theorems

```lean
theorem cayley_maps_resolvent {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) :
    let w := (z - I) * (z + I)⁻¹
    IsUnit (cayleyTransform gen hsa - w • ContinuousLinearMap.id ℂ H)

theorem cayley_eigenvalue_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) (μ : ℝ) :
    (∃ ψ : H, ∃ hψ : ψ ∈ gen.domain, ψ ≠ 0 ∧ gen.op ⟨ψ, hψ⟩ = μ • ψ) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform gen hsa φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ)
```

---

## Möbius Map Algebra

### Lemmas

```lean
lemma real_add_I_ne_zero (μ : ℝ) : 
    (↑μ : ℂ) + I ≠ 0

lemma mobius_norm_one (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1

lemma one_sub_mobius (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ = 2 * I / (↑μ + I)

lemma one_add_mobius (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) + (↑μ - I) * (↑μ + I)⁻¹ = 2 * ↑μ / (↑μ + I)

lemma mobius_coeff_identity (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    let w := (↑μ - I) * (↑μ + I)⁻¹
    I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ

lemma one_sub_mobius_ne_zero (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹ ≠ 0

lemma one_sub_mobius_norm_pos (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹‖ > 0

lemma cayleyTransform_apply_resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    cayleyTransform gen hsa (gen.op ⟨ψ, hψ⟩ + I • ψ) = gen.op ⟨ψ, hψ⟩ - I • ψ

lemma cayley_shift_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (ψ : H) (hψ : ψ ∈ gen.domain) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    let φ := gen.op ⟨ψ, hψ⟩ + I • ψ
    (U - w • ContinuousLinearMap.id ℂ H) φ = ((1 : ℂ) - w) • (gen.op ⟨ψ, hψ⟩ - ↑μ • ψ)
```

---

## Bounded Below Correspondence

### Lemmas

```lean
lemma cayley_shift_injective {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0)
    (hC : ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖) :
    let U := cayleyTransform gen hsa
    let w := (↑μ - I) * (↑μ + I)⁻¹
    Function.Injective (U - w • ContinuousLinearMap.id ℂ H)

lemma self_adjoint_norm_sq_add {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖^2 = ‖gen.op ⟨ψ, hψ⟩‖^2 + ‖ψ‖^2

lemma cayley_spectrum_backward {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (h_unit : IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)) :
    ∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖

lemma cayley_shift_bounded_below_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0)
    (c : ℝ) (hc_pos : c > 0)
    (hc_bound : ∀ φ, ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ ≥ c * ‖φ‖) :
    ∃ C > 0, ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - μ • ψ‖ ≥ C * ‖ψ‖

lemma mobius_norm_eq_one (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    ‖(↑μ - I) * (↑μ + I)⁻¹‖ = 1
```

---

## Normal Operators: Bounded Below ⟺ Invertible

### Definitions

```lean
def ContinuousLinearMap.IsNormal (T : H →L[ℂ] H) : Prop :=
  T.adjoint.comp T = T.comp T.adjoint
```

### Lemmas

```lean
lemma unitary_sub_scalar_isNormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hU : U.adjoint * U = 1 ∧ U * U.adjoint = 1) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint

lemma dense_range_of_orthogonal_trivial {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : F →L[ℂ] F)
    (h : ∀ y, (∀ x, ⟪T x, y⟫_ℂ = 0) → y = 0) :
    Dense (Set.range T)

lemma unitary_sub_scalar_isNormal' {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ) :
    (U - w • 1).adjoint * (U - w • 1) = (U - w • 1) * (U - w • 1).adjoint

lemma surjective_of_isClosed_range_of_dense {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (hClosed : IsClosed (Set.range T))
    (hDense : Dense (Set.range T)) :
    Function.Surjective T

lemma isUnit_bounded_below [Nontrivial H] {T : H →L[ℂ] H} (hT : IsUnit T) :
    ∃ c > 0, ∀ φ, ‖T φ‖ ≥ c * ‖φ‖

lemma normal_bounded_below_surjective {T : H →L[ℂ] H}
    (hT : T.adjoint.comp T = T.comp T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    Function.Surjective T

lemma normal_bounded_below_isUnit [Nontrivial H] {T : H →L[ℂ] H}
    (hT : T.adjoint * T = T * T.adjoint)
    (c : ℝ) (hc_pos : c > 0) (hc_bound : ∀ φ, ‖T φ‖ ≥ c * ‖φ‖) :
    IsUnit T
```

---

## Point Spectrum & Approximate Eigenvalue Correspondence

### Lemmas

```lean
lemma unitary_not_isUnit_approx_eigenvalue [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬IsUnit (U - w • ContinuousLinearMap.id ℂ H)) :
    ∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε

lemma unitary_not_approx_eigenvalue_isUnit [Nontrivial H] {U : H →L[ℂ] H} (hU : Unitary U) (w : ℂ)
    (h_not : ¬∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ < ε) :
    IsUnit (U - w • ContinuousLinearMap.id ℂ H)

lemma approx_eigenvalue_norm_lower_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (ψ : H) (hψ : ψ ∈ gen.domain) (hψ_ne : ψ ≠ 0)
    (h_norm : ‖gen.op ⟨ψ, hψ⟩ + I • ψ‖ = 1)
    (δ : ℝ) (hδ_pos : 0 ≤ δ) (hδ_small : δ^2 < 1 + μ^2)
    (h_approx : ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≤ δ) :
    ‖ψ‖ ≥ (Real.sqrt (1 + μ^2 - δ^2) - |μ| * δ) / (1 + μ^2)

lemma cayley_approx_eigenvalue_backward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) →
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖)

lemma cayley_approx_eigenvalue_forward {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ C > 0, ∃ ψ, ∃ hψ : ψ ∈ gen.domain, ‖ψ‖ ≠ 0 ∧ ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ < C * ‖ψ‖) →
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε)
```

---

## Main Theorems

### Theorems

```lean
theorem cayley_spectrum_correspondence {U_grp : OneParameterUnitaryGroup (H := H)} [Nontrivial H]
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (μ : ℝ) :
    (∃ C : ℝ, C > 0 ∧ ∀ ψ (hψ : ψ ∈ gen.domain), ‖gen.op ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) ↔
    IsUnit (cayleyTransform gen hsa - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)

theorem generator_domain_eq_range_one_minus_cayley {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    (gen.domain : Set H) = LinearMap.range (ContinuousLinearMap.id ℂ H - cayleyTransform gen hsa)
```

---

## Spectral Connection: Bridge to Functional Calculus

### Definitions

```lean
def cayleyImage (B : Set ℝ) : Set ℂ :=
  {w : ℂ | ∃ μ ∈ B, w = (↑μ - I) * (↑μ + I)⁻¹}

noncomputable def spectralMeasure_from_unitary
    (E_U : Set ℂ → (H →L[ℂ] H)) : Set ℝ → (H →L[ℂ] H) :=
  fun B => E_U (cayleyImage B)

def SpectralMeasuresCompatible {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ B : Set ℝ, E_A B = E_U (cayleyImage B)
```

### Axioms

```lean
axiom exists_compatible_spectral_measures {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ∃ (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H)),
      SpectralMeasuresCompatible gen hsa E_A E_U
```

### Theorems

```lean
theorem spectralMeasure_cayley_correspondence {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (E_A : Set ℝ → (H →L[ℂ] H)) (E_U : Set ℂ → (H →L[ℂ] H))
    (hcompat : SpectralMeasuresCompatible gen hsa E_A E_U)
    (B : Set ℝ) :
    E_A B = E_U (cayleyImage B)
```

---

## Summary Counts

| Category   | Count |
|------------|-------|
| **Definitions** | 7 |
| **Lemmas**      | 39 |
| **Theorems**    | 15 |
| **Axioms**      | 1 |
| **Total**       | **62** |

### Breakdown by Definition

1. `Unitary`
2. `cayleyTransform`
3. `inverseCayleyOp`
4. `ContinuousLinearMap.IsNormal`
5. `cayleyImage`
6. `spectralMeasure_from_unitary`
7. `SpectralMeasuresCompatible`

### Breakdown by Theorem

1. `cayleyTransform_isometry`
2. `cayleyTransform_surjective`
3. `cayleyTransform_unitary`
4. `cayley_neg_one_eigenvalue_iff`
5. `inverse_cayley_relation`
6. `inverse_cayley_formula`
7. `inverse_cayley_domain`
8. `cayley_bijection`
9. `inverseCayleyOp_symmetric`
10. `cayleyTransform_norm_one`
11. `cayley_maps_resolvent`
12. `cayley_eigenvalue_correspondence`
13. `cayley_spectrum_correspondence`
14. `generator_domain_eq_range_one_minus_cayley`
15. `spectralMeasure_cayley_correspondence`
