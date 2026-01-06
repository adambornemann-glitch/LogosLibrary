/-
Author: Adam Bornemann
Created: 10/10/2025
Updated: 12/26/2025

================================================================================
STONE'S THEOREM: CORE STRUCTURES AND DEFINITIONS
================================================================================

This file establishes the mathematical foundations for Stone's theorem using
the unbounded operator machinery proven to work in Robertson's theorem.

Key theorem: Bijective correspondence between strongly continuous one-parameter
unitary groups U(t) and self-adjoint operators A via U(t) = exp(itA).

Strategy: Use the domain-tracking approach from Robertson that successfully
handles unbounded operators with Submodule domains.

References:
  - Reed & Simon, "Methods of Modern Mathematical Physics" Vol. 1, Ch. VIII
  - Hall, B.C. "Quantum Theory for Mathematicians" Ch. 9-10
  - Our own Robertson.Core for the unbounded operator pattern
-/

-- Import Completed Bochner file which has the Generator machinery as well
import LogosLibrary.QuantumMechanics.Evolution.Bochner

namespace StonesTheorem.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology  StonesTheorem.Bochner Stone.Generators
open scoped BigOperators Topology
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-!
### The Resolvent (For Self-Adjoint Generators)

For self-adjoint A and z ∉ ℝ, the resolvent R_z = (A - zI)^{-1} exists
as a BOUNDED operator on H.

This is magic: unbounded operator → family of bounded operators!
-/

/--
The solution chosen by `resolvent_at_i` satisfies the defining equation.

**Statement:** For any φ ∈ H, the element `Classical.choose (hsa.2 φ)` returned by
the self-adjointness property satisfies:
1. It's in the domain: `ψ ∈ gen.domain`
2. It solves the equation: `(A - iI)ψ = φ`

**Purpose:**
This is the extraction lemma that unpacks the existential quantifier in
`IsSelfAdjoint gen`. It's the bridge between:
- The abstract existence claim: "∀ φ, ∃ ψ ∈ domain, (A - iI)ψ = φ"
- The concrete chosen value: `Classical.choose (hsa.2 φ)`

**Usage Pattern:**
```lean
have h := resolvent_at_i_spec gen hsa φ
-- Now h.1 : chosen element ∈ domain
-- And h.2 : (A - iI)(chosen element) = φ
```

**Why Separate from Uniqueness:**
- `resolvent_at_i_spec`: Existence (unpacks `Classical.choose_spec`)
- `resolvent_at_i_unique`: Uniqueness (proven via eigenvalue contradiction)
Together they justify using `Classical.choose` to define the resolvent as a function.

**Technical Note:**
The `.2` in `hsa.2` selects the second component of the conjunction in
`IsSelfAdjoint`, which gives Range(A - iI) = H. The `.1` would give Range(A + iI) = H.
-/
lemma resolvent_at_i_spec {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    ∃ (ψ : gen.domain), gen.op ψ - I • (ψ : H) = φ := by
  obtain ⟨ψ, hψ, h_eq⟩ := hsa.2 φ
  exact ⟨⟨ψ, hψ⟩, h_eq⟩

/--
Uniqueness of solutions to (A - iI)ψ = φ.

**Statement:** If ψ₁ and ψ₂ both satisfy (A - iI)ψ = φ for the same φ, then ψ₁ = ψ₂.

**Proof Strategy:**
1. Subtract equations: (A - iI)(ψ₁ - ψ₂) = 0
2. So A(ψ₁ - ψ₂) = i(ψ₁ - ψ₂), making i an eigenvalue with eigenvector ψ₁ - ψ₂
3. Take inner product: ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ = i‖ψ₁ - ψ₂‖²
4. But A is symmetric, so ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ ∈ ℝ
5. A purely imaginary number (i‖ψ₁ - ψ₂‖²) equals a real number only if both = 0
6. Therefore ‖ψ₁ - ψ₂‖² = 0, giving ψ₁ = ψ₂

**Key Insight:** Self-adjoint operators cannot have non-real eigenvalues. This is
the fundamental obstruction that makes (A - zI) invertible for z ∉ ℝ.

**Why This Matters:**
- Makes `resolvent_at_i` well-defined (Classical.choose gives THE unique solution)
- Proves injectivity of (A - iI), which combined with surjectivity gives invertibility
- The same argument works for ANY z with Im(z) ≠ 0, giving the full resolvent

**Physical Meaning:**
A quantum system with Hamiltonian H cannot have complex energy eigenvalues
(energy must be real). This is equivalent to H being self-adjoint.
-/
lemma resolvent_at_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁ = φ)
    (h₂ : gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by

  have h_diff : gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁ - (gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂) = 0 := by
    rw [h₁, h₂]
    simp

  -- First, show ψ₁ - ψ₂ ∈ domain (Submodule is closed under subtraction)
  have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂

-- ψ₁ - ψ₂ is in the domain
  have h_sub_domain : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂

  -- Rewrite as (A - iI)(ψ₁ - ψ₂) = 0
  have h_factor : gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) - I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub (⟨ψ₁, hψ₁⟩ : gen.domain) (⟨ψ₂, hψ₂⟩ : gen.domain)
    simp only at op_sub
    calc gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) - I • (ψ₁ - ψ₂)
        = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - gen.op (⟨ψ₂, hψ₂⟩ : gen.domain)) - I • (ψ₁ - ψ₂) := by exact congrFun (congrArg HSub.hSub op_sub) (I • (ψ₁ - ψ₂))
      _ = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - gen.op (⟨ψ₂, hψ₂⟩ : gen.domain)) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op (⟨ψ₁, hψ₁⟩ : gen.domain) - I • ψ₁) - (gen.op (⟨ψ₂, hψ₂⟩ : gen.domain) - I • ψ₂) := by abel
      _ = 0 := h_diff

  -- So A(ψ₁ - ψ₂) = i(ψ₁ - ψ₂)
  have h_eigen : gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) = I • (ψ₁ - ψ₂) := by
    exact sub_eq_zero.mp h_factor

  -- Take inner product with (ψ₁ - ψ₂)
  have h_inner : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]
    rfl

  -- Simplify: conj(I) = -I
  have h_inner' : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = -I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner]
    simp only [Complex.conj_I]

  -- But A is symmetric, so ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ is real
  have h_sym : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)⟫_ℂ := by
    have := gen.symmetric (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain) (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)
    simp only at this
    expose_names
    exact this

  -- So ⟨A(ψ₁ - ψ₂), ψ₁ - ψ₂⟩ is real (equals its own conjugate)
  have h_real : (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im = 0 := by
    have eq_conj : ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ := by
      calc ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ
          = ⟪ψ₁ - ψ₂, gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain)⟫_ℂ := h_sym
        _ = (starRingEnd ℂ) ⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ :=
            (inner_conj_symm (ψ₁ - ψ₂) (gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain))).symm
    -- z = conj(z) means Im(z) = -Im(z), so Im(z) = 0
    have h_parts := Complex.ext_iff.mp eq_conj
    simp only [Complex.conj_im] at h_parts
    linarith [h_parts.2]

  -- But we also have it equals -I * ‖ψ₁ - ψ₂‖², which has imaginary part -‖ψ₁ - ψ₂‖²
  have h_imag : (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im = -(‖ψ₁ - ψ₂‖ ^ 2) := by
    rw [h_inner']
    rw [mul_comm, Complex.mul_im]
    simp only [Complex.neg_re, Complex.neg_im,
              Complex.I_re, Complex.I_im, mul_zero, neg_zero]
    -- Now: (↑‖ψ₁ - ψ₂‖ ^ 2).re * -1 + 0 = -‖ψ₁ - ψ₂‖ ^ 2
    norm_cast
    ring_nf
    simp

  -- Combining: ‖ψ₁ - ψ₂‖² = 0
  have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
    have h_eq : -(‖ψ₁ - ψ₂‖ ^ 2) = (0 : ℝ) := by
      calc -(‖ψ₁ - ψ₂‖ ^ 2) = (⟪gen.op (⟨ψ₁ - ψ₂, h_sub_domain⟩ : gen.domain), ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
        _ = 0 := h_real
    linarith

  -- Therefore ψ₁ = ψ₂
  have : ‖ψ₁ - ψ₂‖ = 0 := by
    exact sq_eq_zero_iff.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)


/-
FIXED resolvent_at_i section

Key fix: The IsSelfAdjoint definition uses nested existentials:
  ∃ (ψ : H) (hψ : ψ ∈ gen.domain), gen.op ⟨ψ, hψ⟩ - I • ψ = φ

This requires TWO applications of Classical.choose to fully unpack.
The original code incorrectly used .1/.2 on existentials.
-/

-- Assume all the imports and namespace setup from your file
-- namespace StonesTheorem.Resolvent

/-!
### Helper Lemmas for Unpacking Nested Existentials

These lemmas extract the witness and proofs from IsSelfAdjoint
in a way that's compatible with the resolvent_at_i definition.
-/

/-- Extract the domain membership proof for the resolvent solution.

    Given hsa.2 φ : ∃ (ψ : H) (hψ : ψ ∈ gen.domain), gen.op ⟨ψ, hψ⟩ - I • ψ = φ

    We need to apply Classical.choose twice:
    - First choose gives us ψ : H
    - Second choose gives us hψ : ψ ∈ gen.domain
-/
lemma resolvent_solution_mem {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.2 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.2 φ))

/-- Extract the defining equation for the resolvent solution.

    This states that the chosen ψ actually satisfies (A - iI)ψ = φ.

    Crucially, this uses resolvent_solution_mem for the domain proof,
    ensuring definitional equality with the term in Classical.choose_spec.
-/
lemma resolvent_solution_eq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.2 φ), resolvent_solution_mem gen hsa φ⟩ -
    I • Classical.choose (hsa.2 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.2 φ))

/-!
### The Resolvent Operator (Fixed Version)
-/

/--
The resolvent operator R_i = (A - iI)⁻¹ at z = i.

For a self-adjoint generator A, this is the bounded linear operator
that inverts (A - iI). For each φ ∈ H, it returns the unique ψ ∈ domain(A)
satisfying (A - iI)ψ = φ.
-/
noncomputable def resolvent_at_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where

  toFun φ := Classical.choose (hsa.2 φ)

  map_add' := fun φ₁ φ₂ => by
    -- Goal: R(φ₁ + φ₂) = R(φ₁) + R(φ₂)
    -- Strategy: Both sides satisfy (A - iI)·(?) = φ₁ + φ₂, use uniqueness

    -- Abbreviations for readability
    let R₁ := Classical.choose (hsa.2 φ₁)
    let R₂ := Classical.choose (hsa.2 φ₂)
    let R_sum := Classical.choose (hsa.2 (φ₁ + φ₂))

    -- Domain membership for individual solutions
    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem gen hsa (φ₁ + φ₂)

    -- The defining equations
    have h₁_eq : gen.op ⟨R₁, h₁_mem⟩ - I • R₁ = φ₁ := resolvent_solution_eq gen hsa φ₁
    have h₂_eq : gen.op ⟨R₂, h₂_mem⟩ - I • R₂ = φ₂ := resolvent_solution_eq gen hsa φ₂
    have h_sum_eq : gen.op ⟨R_sum, h_sum_mem⟩ - I • R_sum = φ₁ + φ₂ :=
      resolvent_solution_eq gen hsa (φ₁ + φ₂)

    -- The sum R₁ + R₂ is in the domain
    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem

    -- Show (A - iI)(R₁ + R₂) = φ₁ + φ₂
    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂) = φ₁ + φ₂ := by
      -- Use linearity of gen.op
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      -- The subtype addition: need to show the op values match
      have op_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ = gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩ := by
        -- This should follow from linearity, but we need subtype ext
        convert op_add using 1
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ - I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - I • (R₁ + R₂) := by rw [op_eq]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) - (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ - I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ - I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]

    -- Apply uniqueness
    exact (resolvent_at_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm

  map_smul' := fun c φ => by
    -- Goal: R(c • φ) = c • R(φ)

    let R_φ := Classical.choose (hsa.2 φ)
    let R_scaled := Classical.choose (hsa.2 (c • φ))

    -- Domain membership
    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem gen hsa (c • φ)

    -- Defining equations
    have h_eq : gen.op ⟨R_φ, h_mem⟩ - I • R_φ = φ := resolvent_solution_eq gen hsa φ
    have h_scaled_eq : gen.op ⟨R_scaled, h_scaled_mem⟩ - I • R_scaled = c • φ :=
      resolvent_solution_eq gen hsa (c • φ)

    -- c • R(φ) is in domain
    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem

    -- Show (A - iI)(c • R(φ)) = c • φ
    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      have op_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ = c • gen.op ⟨R_φ, h_mem⟩ := by
        convert op_smul using 1
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ - I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ - I • (c • R_φ) := by rw [op_eq]
        _ = c • gen.op ⟨R_φ, h_mem⟩ - c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ - I • R_φ) := by rw [smul_sub]
        _ = c • φ := by rw [h_eq]

    -- Apply uniqueness
    exact (resolvent_at_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm

  cont := by
    -- Prove continuity via Lipschitz bound ‖R(φ)‖ ≤ ‖φ‖
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.2 φ)) := by
      intro φ₁ φ₂

      let ψ₁ := Classical.choose (hsa.2 φ₁)
      let ψ₂ := Classical.choose (hsa.2 φ₂)

      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem gen hsa φ₂
      have h₁_eq := resolvent_solution_eq gen hsa φ₁
      have h₂_eq := resolvent_solution_eq gen hsa φ₂

      -- (A - iI)(ψ₁ - ψ₂) = φ₁ - φ₂
      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem

      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ =
                     gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩ := by
          convert op_sub using 1
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ - I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - I • (ψ₁ - ψ₂) := by rw [op_eq]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) - (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ - I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]

      -- Key estimate: ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖
      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂

        -- Key identity: ‖(A - iI)Δψ‖² = ‖A(Δψ)‖² + ‖Δψ‖²
        have key_expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
                          ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          -- Expand ‖x - y‖² = ‖x‖² + ‖y‖² - 2 Re⟨x, y⟩
          have expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
              ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖I • Δψ‖ ^ 2 -
              2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
            have h1 : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ)
              rw [this]; norm_cast
            have h2 : ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 = (⟪gen.op ⟨Δψ, h_sub_mem⟩, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩)
              rw [this]; norm_cast
            have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              rw [this]; norm_cast
            have h_cross : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re +
                           (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                           2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
              have h_eq : (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                          (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                        rw [inner_conj_symm]
                  _ = (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]; ring
            rw [h1, inner_sub_left, inner_sub_right, inner_sub_right]
            simp only [Complex.sub_re]
            rw [h2, h3, ← h_cross]
            ring

          -- ‖iΔψ‖ = ‖Δψ‖
          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by
            rw [norm_smul]; simp

          -- Re⟨A(Δψ), iΔψ⟩ = 0 (because A is symmetric)
          have cross_zero : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re = 0 := by
            rw [inner_smul_right]
            have h_real : (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric ⟨Δψ, h_sub_mem⟩ ⟨Δψ, h_sub_mem⟩
              have h_conj : ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                            (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                calc ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ
                    = ⟪Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ := h_sym
                  _ = (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                      rw [inner_conj_symm]
              have := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at this
              linarith [this.2]
            -- i * (real number) has re = 0
            have h1 : I * ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                      I * (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).re := by
              conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ]
              rw [h_real]; simp
            rw [h1, mul_comm]
            simp

          rw [expand, norm_I_smul, cross_zero]
          ring

        -- Therefore ‖(A - iI)Δψ‖² ≥ ‖Δψ‖²
        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 := by
          rw [key_expand]
          have : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 := sq_nonneg _
          linarith

        -- Take square roots
        have le_norm : ‖Δψ‖ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := by
          have h_nonneg_left : 0 ≤ ‖Δψ‖ := norm_nonneg _
          have h_nonneg_right : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := norm_nonneg _
          by_contra h_not
          push_neg at h_not
          have : ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖)]
          linarith

        -- Substitute back: ‖(A - iI)Δψ‖ = ‖φ₁ - φ₂‖
        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ - I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]

      -- Convert to edist
      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound

    exact lip.continuous


/-
The resolvent operator R_{-i} = (A + iI)⁻¹ at z = -i.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at -i is the bounded linear operator
that inverts (A + iI). For each φ ∈ H, it returns the unique ψ ∈ domain(A)
satisfying:
  (A + iI)ψ = φ

**Relation to R_i:**
This is the "conjugate" of `resolvent_at_i`. While R_i inverts (A - iI), this
inverts (A + iI). Together they demonstrate that the resolvent exists on both
sides of the real axis.

**Construction:**
Uses the first component `hsa.1` of `IsSelfAdjoint`, which guarantees
Range(A + iI) = H (compare to `hsa.2` which gives Range(A - iI) = H).

The proof of boundedness uses the same key identity:
  ‖(A + iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
giving ‖R_{-i}‖ ≤ 1.

**Why Both Resolvents?:**
Having both R_i and R_{-i} proves that A has resolvent in both upper and lower
half-planes. This bilateral surjectivity is characteristic of self-adjoint operators
(symmetric operators may fail on one or both sides).
-/

/-- Extract domain membership for the (A + iI) resolvent solution -/
lemma resolvent_solution_mem_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    Classical.choose (hsa.1 φ) ∈ gen.domain :=
  Classical.choose (Classical.choose_spec (hsa.1 φ))

/-- Extract the defining equation for the (A + iI) resolvent solution -/
lemma resolvent_solution_eq_plus {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) (φ : H) :
    gen.op ⟨Classical.choose (hsa.1 φ), resolvent_solution_mem_plus gen hsa φ⟩ +
    I • Classical.choose (hsa.1 φ) = φ :=
  Classical.choose_spec (Classical.choose_spec (hsa.1 φ))

/-- Uniqueness for (A + iI): if (A + iI)ψ₁ = (A + iI)ψ₂, then ψ₁ = ψ₂ -/
lemma resolvent_at_neg_i_unique {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (_ : Generator.IsSelfAdjoint gen)
    (φ ψ₁ ψ₂ : H)
    (hψ₁ : ψ₁ ∈ gen.domain) (hψ₂ : ψ₂ ∈ gen.domain)
    (h₁ : gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁ = φ)
    (h₂ : gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂ = φ) :
    ψ₁ = ψ₂ := by
  -- (A + iI)(ψ₁ - ψ₂) = 0
  have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem hψ₁ hψ₂

  have h_diff : gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁ - (gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂) = 0 := by
    rw [h₁, h₂]; simp

  have h_factor : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = 0 := by
    have op_sub := gen.op.map_sub ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩
    have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩ := by
      convert op_sub using 1
    calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
        = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + I • (ψ₁ - ψ₂) := by rw [op_eq]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ - gen.op ⟨ψ₂, hψ₂⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
      _ = (gen.op ⟨ψ₁, hψ₁⟩ + I • ψ₁) - (gen.op ⟨ψ₂, hψ₂⟩ + I • ψ₂) := by abel
      _ = 0 := h_diff

  -- So A(ψ₁ - ψ₂) = -i(ψ₁ - ψ₂)
  have h_eigen : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = -I • (ψ₁ - ψ₂) := by
    have := add_eq_zero_iff_eq_neg.mp h_factor
    rw [← neg_smul] at this
    exact this

  -- Inner product argument
  have h_inner : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = (starRingEnd ℂ) (-I) * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_eigen, inner_smul_left, inner_self_eq_norm_sq_to_K]
    exact rfl

  have h_inner' : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = I * ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner]; simp only [map_neg, Complex.conj_I, neg_neg]

  -- But A is symmetric, so the inner product is real
  have h_sym : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ = ⟪ψ₁ - ψ₂, gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩⟫_ℂ :=
    gen.symmetric ⟨ψ₁ - ψ₂, h_sub_mem⟩ ⟨ψ₁ - ψ₂, h_sub_mem⟩

  have h_real : (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im = 0 := by
    have eq_conj : ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ =
                   (starRingEnd ℂ) ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ := by
      calc ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ
          = ⟪ψ₁ - ψ₂, gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩⟫_ℂ := h_sym
        _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ :=
            (inner_conj_symm (ψ₁ - ψ₂) (gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩)).symm
    have h_parts := Complex.ext_iff.mp eq_conj
    simp only [Complex.conj_im] at h_parts
    linarith [h_parts.2]

  -- i * ‖ψ₁ - ψ₂‖² has imaginary part ‖ψ₁ - ψ₂‖²
  have h_imag : (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im = ‖ψ₁ - ψ₂‖ ^ 2 := by
    rw [h_inner', mul_comm, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, mul_zero]
    norm_cast; ring_nf

  -- Contradiction: Im = 0 but also Im = ‖ψ₁ - ψ₂‖²
  have : ‖ψ₁ - ψ₂‖ ^ 2 = 0 := by
    calc ‖ψ₁ - ψ₂‖ ^ 2 = (⟪gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩, ψ₁ - ψ₂⟫_ℂ).im := h_imag.symm
      _ = 0 := h_real

  have : ‖ψ₁ - ψ₂‖ = 0 := sq_eq_zero_iff.mp this
  exact sub_eq_zero.mp (norm_eq_zero.mp this)



/--
The resolvent operator R_{-i} = (A + iI)⁻¹ at z = -i.
-/
noncomputable def resolvent_at_neg_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H where

  toFun φ := Classical.choose (hsa.1 φ)

  map_add' := fun φ₁ φ₂ => by
    let R₁ := Classical.choose (hsa.1 φ₁)
    let R₂ := Classical.choose (hsa.1 φ₂)
    let R_sum := Classical.choose (hsa.1 (φ₁ + φ₂))

    have h₁_mem : R₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
    have h₂_mem : R₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
    have h_sum_mem : R_sum ∈ gen.domain := resolvent_solution_mem_plus gen hsa (φ₁ + φ₂)

    have h₁_eq : gen.op ⟨R₁, h₁_mem⟩ + I • R₁ = φ₁ := resolvent_solution_eq_plus gen hsa φ₁
    have h₂_eq : gen.op ⟨R₂, h₂_mem⟩ + I • R₂ = φ₂ := resolvent_solution_eq_plus gen hsa φ₂
    have h_sum_eq : gen.op ⟨R_sum, h_sum_mem⟩ + I • R_sum = φ₁ + φ₂ :=
      resolvent_solution_eq_plus gen hsa (φ₁ + φ₂)

    have h_add_mem : R₁ + R₂ ∈ gen.domain := gen.domain.add_mem h₁_mem h₂_mem

    have h_add_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂) = φ₁ + φ₂ := by
      have op_add := gen.op.map_add ⟨R₁, h₁_mem⟩ ⟨R₂, h₂_mem⟩
      have op_eq : gen.op ⟨R₁ + R₂, h_add_mem⟩ = gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩ := by
        convert op_add using 1
      calc gen.op ⟨R₁ + R₂, h_add_mem⟩ + I • (R₁ + R₂)
          = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + I • (R₁ + R₂) := by rw [op_eq]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + gen.op ⟨R₂, h₂_mem⟩) + (I • R₁ + I • R₂) := by rw [smul_add]
        _ = (gen.op ⟨R₁, h₁_mem⟩ + I • R₁) + (gen.op ⟨R₂, h₂_mem⟩ + I • R₂) := by abel
        _ = φ₁ + φ₂ := by rw [h₁_eq, h₂_eq]

    exact (resolvent_at_neg_i_unique gen hsa (φ₁ + φ₂) (R₁ + R₂) R_sum
      h_add_mem h_sum_mem h_add_eq h_sum_eq).symm

  map_smul' := fun c φ => by
    let R_φ := Classical.choose (hsa.1 φ)
    let R_scaled := Classical.choose (hsa.1 (c • φ))

    have h_mem : R_φ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ
    have h_scaled_mem : R_scaled ∈ gen.domain := resolvent_solution_mem_plus gen hsa (c • φ)

    have h_eq : gen.op ⟨R_φ, h_mem⟩ + I • R_φ = φ := resolvent_solution_eq_plus gen hsa φ
    have h_scaled_eq : gen.op ⟨R_scaled, h_scaled_mem⟩ + I • R_scaled = c • φ :=
      resolvent_solution_eq_plus gen hsa (c • φ)

    have h_smul_mem : c • R_φ ∈ gen.domain := gen.domain.smul_mem c h_mem

    have h_smul_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ) = c • φ := by
      have op_smul := gen.op.map_smul c ⟨R_φ, h_mem⟩
      have op_eq : gen.op ⟨c • R_φ, h_smul_mem⟩ = c • gen.op ⟨R_φ, h_mem⟩ := by
        convert op_smul using 1
      calc gen.op ⟨c • R_φ, h_smul_mem⟩ + I • (c • R_φ)
          = c • gen.op ⟨R_φ, h_mem⟩ + I • (c • R_φ) := by rw [op_eq]
        _ = c • gen.op ⟨R_φ, h_mem⟩ + c • (I • R_φ) := by rw [smul_comm]
        _ = c • (gen.op ⟨R_φ, h_mem⟩ + I • R_φ) := by rw [smul_add]
        _ = c • φ := by rw [h_eq]

    exact (resolvent_at_neg_i_unique gen hsa (c • φ) (c • R_φ) R_scaled
      h_smul_mem h_scaled_mem h_smul_eq h_scaled_eq).symm

  cont := by
    have lip : LipschitzWith 1 (fun φ => Classical.choose (hsa.1 φ)) := by
      intro φ₁ φ₂

      let ψ₁ := Classical.choose (hsa.1 φ₁)
      let ψ₂ := Classical.choose (hsa.1 φ₂)

      have h₁_mem : ψ₁ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₁
      have h₂_mem : ψ₂ ∈ gen.domain := resolvent_solution_mem_plus gen hsa φ₂
      have h₁_eq := resolvent_solution_eq_plus gen hsa φ₁
      have h₂_eq := resolvent_solution_eq_plus gen hsa φ₂

      have h_sub_mem : ψ₁ - ψ₂ ∈ gen.domain := gen.domain.sub_mem h₁_mem h₂_mem

      have h_diff : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂) = φ₁ - φ₂ := by
        have op_sub := gen.op.map_sub ⟨ψ₁, h₁_mem⟩ ⟨ψ₂, h₂_mem⟩
        have op_eq : gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ = gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩ := by
          convert op_sub using 1
        calc gen.op ⟨ψ₁ - ψ₂, h_sub_mem⟩ + I • (ψ₁ - ψ₂)
            = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + I • (ψ₁ - ψ₂) := by rw [op_eq]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ - gen.op ⟨ψ₂, h₂_mem⟩) + (I • ψ₁ - I • ψ₂) := by rw [smul_sub]
          _ = (gen.op ⟨ψ₁, h₁_mem⟩ + I • ψ₁) - (gen.op ⟨ψ₂, h₂_mem⟩ + I • ψ₂) := by abel
          _ = φ₁ - φ₂ := by rw [h₁_eq, h₂_eq]

      have bound : ‖ψ₁ - ψ₂‖ ≤ ‖φ₁ - φ₂‖ := by
        let Δψ := ψ₁ - ψ₂

        -- Key identity: ‖(A + iI)Δψ‖² = ‖A(Δψ)‖² + ‖Δψ‖²
        have key_expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
                          ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖Δψ‖ ^ 2 := by
          have expand : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
              ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 + ‖I • Δψ‖ ^ 2 +
              2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
            have h1 : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ)
              rw [this]; norm_cast
            have h2 : ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 =
                      (⟪gen.op ⟨Δψ, h_sub_mem⟩, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨Δψ, h_sub_mem⟩)
              rw [this]; norm_cast
            have h3 : ‖I • Δψ‖ ^ 2 = (⟪I • Δψ, I • Δψ⟫_ℂ).re := by
              have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • Δψ)
              rw [this]; norm_cast
            have h_cross : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re +
                           (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                           2 * (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
              have h_eq : (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re =
                          (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                calc (⟪I • Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ).re
                    = ((starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by
                        rw [inner_conj_symm]
                  _ = (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re := by simp only [Complex.conj_re]
              rw [h_eq]; ring
            rw [h1, inner_add_left, inner_add_right, inner_add_right]
            simp only [Complex.add_re]
            rw [h2, h3, ← h_cross]
            ring

          have norm_I_smul : ‖I • Δψ‖ = ‖Δψ‖ := by rw [norm_smul]; simp

          have cross_zero : (⟪gen.op ⟨Δψ, h_sub_mem⟩, I • Δψ⟫_ℂ).re = 0 := by
            rw [inner_smul_right]
            have h_real : (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).im = 0 := by
              have h_sym := gen.symmetric ⟨Δψ, h_sub_mem⟩ ⟨Δψ, h_sub_mem⟩
              have h_conj : ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                            (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                calc ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ
                    = ⟪Δψ, gen.op ⟨Δψ, h_sub_mem⟩⟫_ℂ := h_sym
                  _ = (starRingEnd ℂ) ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ := by
                      rw [inner_conj_symm]
              have := Complex.ext_iff.mp h_conj
              simp only [Complex.conj_im] at this
              linarith [this.2]
            have h1 : I * ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ =
                      I * (⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ).re := by
              conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨Δψ, h_sub_mem⟩, Δψ⟫_ℂ]
              rw [h_real]; simp
            rw [h1, mul_comm]
            simp

          rw [expand, norm_I_smul, cross_zero]
          ring

        have le_sq : ‖Δψ‖ ^ 2 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 := by
          rw [key_expand]
          have : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩‖ ^ 2 := sq_nonneg _
          linarith

        have le_norm : ‖Δψ‖ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := by
          have h_nonneg_left : 0 ≤ ‖Δψ‖ := norm_nonneg _
          have h_nonneg_right : 0 ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := norm_nonneg _
          by_contra h_not
          push_neg at h_not
          have : ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ ^ 2 < ‖Δψ‖ ^ 2 := by
            nlinarith [sq_nonneg (‖Δψ‖ - ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖)]
          linarith

        calc ‖ψ₁ - ψ₂‖ = ‖Δψ‖ := rfl
          _ ≤ ‖gen.op ⟨Δψ, h_sub_mem⟩ + I • Δψ‖ := le_norm
          _ = ‖φ₁ - φ₂‖ := by rw [h_diff]

      rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal bound

    exact lip.continuous

/--
The resolvent operator R_i = (A - iI)⁻¹ is bounded with norm ≤ 1.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at i satisfies the uniform bound:
  ∀ φ ∈ H: ‖R_i(φ)‖ ≤ ‖φ‖

This proves ‖R_i‖ ≤ 1 as a bounded operator on H.

**Proof Strategy:**
The key identity for any ψ in the domain of A is:
  ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

This follows from expanding the norm and using that the cross term vanishes:
  Re⟨Aψ, iψ⟩ = Re(i·⟨Aψ, ψ⟩) = 0

since ⟨Aψ, ψ⟩ ∈ ℝ by symmetry of A.

From the identity: ‖(A - iI)ψ‖² ≥ ‖ψ‖², so ‖(A - iI)ψ‖ ≥ ‖ψ‖.

For φ = (A - iI)ψ, we have ψ = R_i(φ), giving:
  ‖R_i(φ)‖ = ‖ψ‖ ≤ ‖(A - iI)ψ‖ = ‖φ‖

**Why This Matters:**
- The bound ‖R_i‖ ≤ 1 is sharp (equality holds for certain states)
- This is a special case of the general bound ‖R_z‖ ≤ 1/|Im(z)|
- The bounded resolvent is THE defining characteristic separating self-adjoint
  from merely symmetric operators
- Essential for proving the spectral theorem via functional calculus

**Physical Interpretation:**
In quantum mechanics with Hamiltonian H, the resolvent (E - H)⁻¹ represents
the system's response to energy probes. The bound says probing at complex
energy i produces a bounded response - no resonances at non-real energies.

**Comparison with R_{-i}:**
The conjugate resolvent `resolvent_at_neg_i` inverts (A + iI) and satisfies
the identical bound ‖R_{-i}‖ ≤ 1 by the same argument (using -i instead of i).
-/
lemma resolvent_at_i_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen) :
    ‖resolvent_at_i gen hsa‖ ≤ 1 := by
  have h_bound : ∀ φ : H, ‖resolvent_at_i gen hsa φ‖ ≤ ‖φ‖ := by
    intro φ

    -- ψ = R_i(φ) = Classical.choose (hsa.2 φ)
    let ψ := resolvent_at_i gen hsa φ
    have h_mem : ψ ∈ gen.domain := resolvent_solution_mem gen hsa φ
    have h_eq : gen.op ⟨ψ, h_mem⟩ - I • ψ = φ := resolvent_solution_eq gen hsa φ

    -- Key: ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²
    have key_expand : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 = ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 + ‖ψ‖ ^ 2 := by
      have expand : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 =
          ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 + ‖I • ψ‖ ^ 2 - 2 * (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
        have h_inner : (⟪gen.op ⟨ψ, h_mem⟩ - I • ψ, gen.op ⟨ψ, h_mem⟩ - I • ψ⟫_ℂ).re =
            ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, h_mem⟩ - I • ψ)
          rw [this]; norm_cast
        rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
        simp only [Complex.sub_re]
        have h2 : ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 = (⟪gen.op ⟨ψ, h_mem⟩, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gen.op ⟨ψ, h_mem⟩)
          rw [this]; norm_cast
        have h3 : ‖I • ψ‖ ^ 2 = (⟪I • ψ, I • ψ⟫_ℂ).re := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (I • ψ)
          rw [this]; norm_cast
        rw [h2, h3]
        have h_cross : (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re + (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re =
                      2 * (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
          have h_eq : (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re = (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by
            calc (⟪I • ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ).re
                = ((starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by rw [inner_conj_symm]
              _ = (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re := by simp only [Complex.conj_re]
          rw [h_eq]; ring
        rw [h_cross.symm]; ring

      have norm_I_smul : ‖I • ψ‖ = ‖ψ‖ := by rw [norm_smul]; simp

      have cross_zero : (⟪gen.op ⟨ψ, h_mem⟩, I • ψ⟫_ℂ).re = 0 := by
        rw [inner_smul_right]
        have h_real : (⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ).im = 0 := by
          have h_sym := gen.symmetric ⟨ψ, h_mem⟩ ⟨ψ, h_mem⟩
          have h_conj : ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ := by
            calc ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ
                = ⟪ψ, gen.op ⟨ψ, h_mem⟩⟫_ℂ := h_sym
              _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ := by rw [inner_conj_symm]
          have := Complex.ext_iff.mp h_conj
          simp only [Complex.conj_im] at this
          linarith [this.2]
        have h1 : I * ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ = I * (⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ).re := by
          conv_lhs => rw [← Complex.re_add_im ⟪gen.op ⟨ψ, h_mem⟩, ψ⟫_ℂ]
          rw [h_real]; simp
        rw [h1, mul_comm]; simp

      rw [expand, norm_I_smul, cross_zero]; ring

    have le_sq : ‖ψ‖ ^ 2 ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 := by
      rw [key_expand]; have : 0 ≤ ‖gen.op ⟨ψ, h_mem⟩‖ ^ 2 := sq_nonneg _; linarith

    have le_norm : ‖ψ‖ ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := by
      by_contra h_not; push_neg at h_not
      have : ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ ^ 2 < ‖ψ‖ ^ 2 := by
        have h1 : 0 ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := norm_nonneg _
        have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖ψ‖ - ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖)]
      linarith

    calc ‖ψ‖
        ≤ ‖gen.op ⟨ψ, h_mem⟩ - I • ψ‖ := le_norm
      _ = ‖φ‖ := by rw [h_eq]

  apply ContinuousLinearMap.opNorm_le_bound
  · norm_num
  · intro φ
    calc ‖resolvent_at_i gen hsa φ‖
        ≤ ‖φ‖ := h_bound φ
      _ = 1 * ‖φ‖ := by ring


/--
Lower bound estimate for (A - zI) when Im(z) ≠ 0.

**The Foundation of Everything:**
For any z ∈ ℂ with Im(z) ≠ 0 and any ψ in the domain of A, we have:
  ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖

**Why This Matters:**
1. Proves (A - zI) is injective for all z ∉ ℝ
2. Shows Range(A - zI) is closed (bounded below)
3. Gives explicit bound on resolvent: ‖R_z‖ ≤ 1/|Im(z)|
4. Distinguishes self-adjoint from symmetric operators

**Proof Strategy:**
Write z = x + iy where x = Re(z), y = Im(z) ≠ 0. Then:
  (A - zI)ψ = (A - xI)ψ - iy·ψ

Expand the norm squared using the key identity:
  ‖(A - xI)ψ - iy·ψ‖² = ‖(A - xI)ψ‖² + |y|²‖ψ‖² + 2Re⟨(A-xI)ψ, -iy·ψ⟩

The cross term vanishes because:
- Re⟨(A-xI)ψ, -iy·ψ⟩ = -Im(y)·Re⟨(A-xI)ψ, ψ⟩
- But ⟨(A-xI)ψ, ψ⟩ ∈ ℝ (A-xI is symmetric)
- So the cross term is purely imaginary times real = has zero real part

Therefore: ‖(A - zI)ψ‖² ≥ |y|²‖ψ‖²

**Physical Interpretation:**
In quantum mechanics, this says you can't have resonances exactly on the real energy axis
for self-adjoint Hamiltonians. The imaginary part provides a "gap" that prevents collapse
onto the spectrum.
-/
lemma lower_bound_estimate {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (z : ℂ) (_ : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    ‖gen.op ⟨ψ, hψ⟩ - z • ψ‖ ≥ |z.im| * ‖ψ‖ := by
  -- Decompose z = x + iy
  set x := z.re
  set y := z.im

  -- Rewrite (A - zI)ψ = (A - xI)ψ - iy·ψ
  have h_decomp : gen.op ⟨ψ, hψ⟩ - z • ψ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by
    have hz_eq : z = x + y * I := by simp [x, y]
    calc gen.op ⟨ψ, hψ⟩ - z • ψ
        = gen.op ⟨ψ, hψ⟩ - (x + y * I) • ψ := by rw [hz_eq]
      _ = gen.op ⟨ψ, hψ⟩ - (x • ψ + (y * I) • ψ) := by rw [add_smul]; exact rfl
      _ = (gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by abel

  rw [h_decomp]

  -- Expand ‖(A - xI)ψ - iy·ψ‖²
  have h_expand : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 =
                ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
                2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
    have h_formula : ∀ (a b : H), ‖a - b‖^2 = ‖a‖^2 + ‖b‖^2 - 2 * (⟪a, b⟫_ℂ).re := by
      intro a b
      have h_inner : (⟪a - b, a - b⟫_ℂ).re = ‖a - b‖ ^ 2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a - b)
        rw [this]; norm_cast
      rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
      simp only [Complex.sub_re]
      have h1 : (⟪a, a⟫_ℂ).re = ‖a‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) a
        rw [this]; norm_cast
      have h2 : (⟪b, b⟫_ℂ).re = ‖b‖^2 := by
        have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) b
        rw [this]; norm_cast
      rw [h1, h2]
      have h_cross : (⟪a, b⟫_ℂ).re + (⟪b, a⟫_ℂ).re = 2 * (⟪a, b⟫_ℂ).re := by
        have : (⟪b, a⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
          calc (⟪b, a⟫_ℂ).re
              = ((starRingEnd ℂ) ⟪a, b⟫_ℂ).re := by rw [inner_conj_symm]
            _ = (⟪a, b⟫_ℂ).re := by simp only [Complex.conj_re]
        rw [this]; ring
      rw [h_cross.symm]; ring

    calc ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2
        = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 - 2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re :=
            h_formula (gen.op ⟨ψ, hψ⟩ - x • ψ) ((y * I) • ψ)
      _ = ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 + 2 * (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
          have : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re =
                 -(⟪gen.op ⟨ψ, hψ⟩ - x • ψ, (y * I) • ψ⟫_ℂ).re := by
            rw [inner_neg_right]; simp only [Complex.neg_re]
          rw [this]; ring

  -- The norm of iy·ψ
  have h_norm_scale : ‖(y * I) • ψ‖ = |y| * ‖ψ‖ := by
    calc ‖(y * I) • ψ‖
        = ‖(y * I : ℂ)‖ * ‖ψ‖ := norm_smul _ _
      _ = |y| * ‖ψ‖ := by simp

  -- The cross term vanishes
  have h_cross_zero : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = 0 := by
    rw [inner_neg_right, inner_smul_right]

    -- First show ⟨(A-xI)ψ, ψ⟩ is real
    have h_real : (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).im = 0 := by
      rw [inner_sub_left]
      have h_Areal : (⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
        -- FIX: pass subtypes, not H elements with proofs
        have h_sym := gen.symmetric ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
        have h_conj : ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
          calc ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ
              = ⟪ψ, gen.op ⟨ψ, hψ⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ :=
                (inner_conj_symm ψ (gen.op ⟨ψ, hψ⟩)).symm
        have h_parts := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]

      have h_xreal : (⟪x • ψ, ψ⟫_ℂ).im = 0 := by
        have h_eq : x • ψ = (x : ℂ) • ψ := (RCLike.real_smul_eq_coe_smul x ψ).symm
        rw [h_eq, inner_smul_left]
        have h_inner_real : (⟪ψ, ψ⟫_ℂ).im = 0 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
          rw [this]; norm_cast
        simp [h_inner_real]

      simp [h_Areal, h_xreal]

    have h_as_real : ⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ = ((⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (⟪gen.op ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ), h_real]
      simp

    rw [h_as_real]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [I_re, mul_zero, zero_mul, neg_zero]

  -- Now: ‖(A-zI)ψ‖² = ‖(A-xI)ψ‖² + |y|²‖ψ‖² ≥ |y|²‖ψ‖²
  have h_sq : ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 ≥ (|y| * ‖ψ‖)^2 := by
    rw [h_expand, h_norm_scale, h_cross_zero]
    simp only [mul_zero, add_zero]
    have : 0 ≤ ‖gen.op ⟨ψ, hψ⟩ - x • ψ‖^2 := sq_nonneg _
    linarith

  -- Take square root
  by_contra h_not
  push_neg at h_not
  have h1 : 0 ≤ ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖ := norm_nonneg _
  have h2 : 0 ≤ |y| * ‖ψ‖ := by
    apply mul_nonneg
    · exact abs_nonneg _
    · exact norm_nonneg _
  nlinarith [sq_nonneg (|y| * ‖ψ‖ - ‖(gen.op ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖), h_sq, h_not, h1, h2]


/-!
### Neumann Series Machinery

For a bounded linear operator T with ‖T‖ < 1, the series Σₙ Tⁿ converges
to (I - T)⁻¹. This is the operator-theoretic analogue of 1/(1-x) = Σ xⁿ.
-/

--namespace NeumannSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/--
Powers of operators satisfy ‖Tⁿ‖ ≤ ‖T‖ⁿ.

This is the submultiplicativity of operator norm applied inductively.
-/
lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := by
          apply mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]

/--
When ‖T‖ < 1, the powers Tⁿ converge to zero in operator norm.

Proof: ‖Tⁿ‖ ≤ ‖T‖ⁿ → 0 since ‖T‖ < 1.
-/
lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_norm]
    exact hT
  have h_bound : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => opNorm_pow_le T n
  have h_nonneg : ∀ n, 0 ≤ ‖T^n‖ := fun n => norm_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom h_nonneg h_bound

/--
Partial sums of the Neumann series: Sₙ = I + T + T² + ... + T^(n-1)
-/
noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  Finset.sum (Finset.range n) (fun k => T^k)

/--
Telescoping identity: (I - T) * Sₙ = I - Tⁿ

This is the key algebraic identity for Neumann series.
-/
lemma neumannPartialSum_mul (T : E →L[ℂ] E) (n : ℕ) :
    (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
    ContinuousLinearMap.id ℂ E - T^n := by
  induction n with
  | zero =>
    simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
    simp only [mul_zero]
    ext x : 1
    simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
  | succ n ih =>
    simp only [neumannPartialSum] at ih ⊢
    rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [ih]
    -- Goal: I - T^n + (I - T) * T^n = I - T^(n+1)
    have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
    rw [h_id_eq]
    rw [sub_mul, one_mul]
    rw [← pow_succ']
    -- Goal: 1 - T^n + (T^n - T^(n+1)) = 1 - T^(n+1)
    abel

/--
When ‖T‖ < 1, the Neumann partial sums form a Cauchy sequence in operator norm.
-/
lemma neumannPartialSum_cauchy (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    CauchySeq (neumannPartialSum T) := by
  apply cauchySeq_of_summable_dist
  -- Need: Summable (fun n => dist (S_n) (S_{n+1}))
  -- dist(S_n, S_{n+1}) = ‖T^n‖ ≤ ‖T‖^n
  have h_bound : ∀ n, dist (neumannPartialSum T n) (neumannPartialSum T (n + 1)) ≤ ‖T‖^n := by
    intro n
    simp only [neumannPartialSum, dist_eq_norm, Finset.sum_range_succ]
    rw [← norm_neg, neg_sub, add_sub_cancel_left]
    exact opNorm_pow_le T n
  apply Summable.of_nonneg_of_le
  · intro n; exact dist_nonneg
  · exact h_bound
  · exact summable_geometric_of_lt_one (norm_nonneg _) hT

/--
The Neumann series: limit of partial sums when ‖T‖ < 1.
-/
noncomputable def neumannSeries (T : E →L[ℂ] E) (_ /-hT-/ : ‖T‖ < 1) : E →L[ℂ] E :=
  limUnder atTop (neumannPartialSum T)

/--
The Neumann series satisfies (I - T) * S = I.
-/
lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E := by
  -- neumannSeries is the limit of partial sums
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) := by
    exact (neumannPartialSum_cauchy T hT).tendsto_limUnder

  -- (I - T) * Sₙ → (I - T) * S by continuity of multiplication
  have h_mul_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 ((ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT)) := by
    exact Tendsto.const_mul (ContinuousLinearMap.id ℂ E - T) h_lim

  -- But (I - T) * Sₙ = I - Tⁿ by telescoping
  have h_eq : ∀ n, (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n =
      ContinuousLinearMap.id ℂ E - T^n := neumannPartialSum_mul T

  -- And Tⁿ → 0
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h

  -- So I - Tⁿ → I - 0 = I
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E - 0)) := by
    exact Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim

  simp only [sub_zero] at h_sub_lim

  -- Combine: (I - T) * S = lim (I - T) * Sₙ = lim (I - Tⁿ) = I
  have h_eq_lim : Tendsto (fun n => (ContinuousLinearMap.id ℂ E - T) * neumannPartialSum T n)
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_eq]
    exact h_sub_lim

  exact tendsto_nhds_unique h_mul_lim h_eq_lim

/--
The Neumann series satisfies S * (I - T) = I.
-/
lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E := by
  -- First prove the telescoping identity for right multiplication
  have h_telescope : ∀ n, neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T) =
      ContinuousLinearMap.id ℂ E - T^n := by
    intro n
    induction n with
    | zero =>
      simp only [neumannPartialSum, Finset.range_zero, Finset.sum_empty, pow_zero]
      simp only [zero_mul]
      ext x : 1
      simp_all only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
    Pi.sub_apply, id_eq, ContinuousLinearMap.one_apply, sub_self]
    | succ n ih =>
      simp only [neumannPartialSum] at ih ⊢
      rw [Finset.sum_range_succ]
      rw [add_mul]
      rw [ih]
      have h_id_eq : ContinuousLinearMap.id ℂ E = (1 : E →L[ℂ] E) := rfl
      rw [h_id_eq]
      rw [mul_sub, mul_one]
      rw [← pow_succ]
      abel

  -- neumannSeries is the limit of partial sums
  have h_lim : Tendsto (neumannPartialSum T) atTop (𝓝 (neumannSeries T hT)) :=
    (neumannPartialSum_cauchy T hT).tendsto_limUnder

  -- Sₙ * (I - T) → S * (I - T) by continuity
  have h_mul_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T))) := by
    exact Tendsto.mul_const (ContinuousLinearMap.id ℂ E - T) h_lim

  -- Tⁿ → 0
  have h_pow_lim : Tendsto (fun n => T^n) atTop (𝓝 0) := by
    have h := opNorm_pow_tendsto_zero T hT
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h

  -- I - Tⁿ → I
  have h_sub_lim : Tendsto (fun n => ContinuousLinearMap.id ℂ E - T^n) atTop
      (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    have := Tendsto.const_sub (ContinuousLinearMap.id ℂ E) h_pow_lim
    simp only [sub_zero] at this
    exact this

  -- Combine
  have h_eq_lim : Tendsto (fun n => neumannPartialSum T n * (ContinuousLinearMap.id ℂ E - T))
      atTop (𝓝 (ContinuousLinearMap.id ℂ E)) := by
    simp only [h_telescope]
    exact h_sub_lim

  exact tendsto_nhds_unique h_mul_lim h_eq_lim

/--
When ‖T‖ < 1, the operator (I - T) is invertible with inverse given by the Neumann series.
-/
lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) := by
  refine ⟨⟨ContinuousLinearMap.id ℂ E - T, neumannSeries T hT, ?_, ?_⟩, rfl⟩
  · exact neumannSeries_mul_left T hT
  · exact neumannSeries_mul_right T hT


/-- For z near i, we can construct R_z from R_i via Neumann series -/
lemma resolvent_near_i {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im > 0) (h_close : ‖z - I‖ < 1) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ

  -- Setup
  let R := resolvent_at_i gen hsa
  let lambda_val := z - I

  -- Key bound: ‖λ·R‖ < 1, enabling Neumann series
  have h_op_bound : ‖lambda_val • R‖ < 1 := by
    calc ‖lambda_val • R‖
        = ‖lambda_val‖ * ‖R‖ := norm_smul lambda_val R
      _ ≤ ‖lambda_val‖ * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact resolvent_at_i_bound gen hsa
          · exact norm_nonneg _
      _ = ‖z - I‖ := by ring
      _ < 1 := h_close

  -- Part 1: Existence via Neumann series
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    -- Strategy: (A - zI) = (A - iI) - (z - i)I
    -- So for ψ in domain: (A - zI)ψ = (A - iI)ψ - (z - i)ψ
    -- Rearranging: (A - zI)ψ = φ iff (A - iI)ψ = φ + (z - i)ψ
    -- iff ψ = R_i(φ + (z - i)ψ) = R_i(φ) + (z - i)R_i(ψ)
    -- iff (I - (z - i)R_i)ψ = R_i(φ)
    -- iff ψ = [I - (z - i)R_i]^{-1} R_i(φ)

    -- The Neumann series gives [I - (z-i)R_i]^{-1}
    let T := lambda_val • R
    let S := neumannSeries T h_op_bound

    -- Solve (I - (z-i)R_i)η = φ first, then ψ = R_i(η) is in domain
    let η := S φ
    let ψ_val := R η  -- This is Classical.choose (hsa.2 η) : H

    have h_ψ_mem : ψ_val ∈ gen.domain := resolvent_solution_mem gen hsa η
    have h_ψ_eq : gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val = η := resolvent_solution_eq gen hsa η

    use ⟨ψ_val, h_ψ_mem⟩

    -- Need: (A - zI)ψ = φ
    -- We have: (A - iI)ψ = η (from resolvent definition)
    -- And: (I - (z-i)R)η = φ (from Neumann series)

    -- (I - T)S = I, so (I - T)(Sφ) = φ, i.e., η - T(η) = φ
    have h_neumann_eq : η - T η = φ := by
      have h_inv := neumannSeries_mul_left T h_op_bound
      calc η - T η
          = (ContinuousLinearMap.id ℂ H - T) η := by simp [T]
        _ = ((ContinuousLinearMap.id ℂ H - T) * S) φ := by simp [η, S]
        _ = ContinuousLinearMap.id ℂ H φ := by rw [h_inv]
        _ = φ := rfl

    -- Now compute (A - zI)ψ
    calc gen.op ⟨ψ_val, h_ψ_mem⟩ - z • ψ_val
        = gen.op ⟨ψ_val, h_ψ_mem⟩ - (I + lambda_val) • ψ_val := by simp [lambda_val]
      _ = gen.op ⟨ψ_val, h_ψ_mem⟩ - I • ψ_val - lambda_val • ψ_val := by rw [add_smul]; abel
      _ = η - lambda_val • ψ_val := by rw [h_ψ_eq]
      _ = η - lambda_val • (R η) := rfl
      _ = η - (lambda_val • R) η := by rfl
      _ = η - T η := rfl
      _ = φ := h_neumann_eq

  -- Part 2: Uniqueness (via lower_bound_estimate at z)
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'

  -- Show ψ = ψ' by showing their difference is zero
  have h_sub_mem : (ψ : H) - (ψ' : H) ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property

  have h_diff : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H)) = 0 := by
    have op_sub := gen.op.map_sub ψ ψ'
    have op_eq : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ = gen.op ψ - gen.op ψ' := by
      convert op_sub using 1
    calc gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H))
        = (gen.op ψ - gen.op ψ') - z • ((ψ : H) - (ψ' : H)) := by rw [op_eq]
      _ = (gen.op ψ - gen.op ψ') - (z • (ψ : H) - z • (ψ' : H)) := by rw [smul_sub]
      _ = (gen.op ψ - z • (ψ : H)) - (gen.op ψ' - z • (ψ' : H)) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ

  -- Apply lower_bound_estimate: since Im(z) > 0, we have ‖(A-zI)(ψ-ψ')‖ ≥ |Im(z)|·‖ψ-ψ'‖
  have h_im_ne : z.im ≠ 0 := ne_of_gt hz

  have h_bound := lower_bound_estimate gen z h_im_ne ((ψ : H) - (ψ' : H)) h_sub_mem

  -- From h_diff: LHS = 0, so |Im(z)|·‖ψ-ψ'‖ ≤ 0
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound

  -- Since |Im(z)| > 0, we get ‖ψ-ψ'‖ = 0
  have h_im_pos : 0 < |z.im| := abs_pos.mpr h_im_ne

  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith

  -- Therefore ψ = ψ'
  have h_eq : (ψ : H) = (ψ' : H) := sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  exact Subtype.ext h_eq.symm

/-
The resolvent operator R_i = (A - iI)⁻¹ is bounded with norm ≤ 1.

**Mathematical Content:**
For a self-adjoint generator A, the resolvent at i satisfies the uniform bound:
  ∀ φ ∈ H: ‖R_i(φ)‖ ≤ ‖φ‖

This proves ‖R_i‖ ≤ 1 as a bounded operator on H.

**Proof Strategy:**
The key identity for any ψ in the domain of A is:
  ‖(A - iI)ψ‖² = ‖Aψ‖² + ‖ψ‖²

This follows from expanding the norm and using that the cross term vanishes:
  Re⟨Aψ, iψ⟩ = Re(i·⟨Aψ, ψ⟩) = 0

since ⟨Aψ, ψ⟩ ∈ ℝ by symmetry of A.

From the identity: ‖(A - iI)ψ‖² ≥ ‖ψ‖², so ‖(A - iI)ψ‖ ≥ ‖ψ‖.

For φ = (A - iI)ψ, we have ψ = R_i(φ), giving:
  ‖R_i(φ)‖ = ‖ψ‖ ≤ ‖(A - iI)ψ‖ = ‖φ‖

**Why This Matters:**
- The bound ‖R_i‖ ≤ 1 is sharp (equality holds for certain states)
- This is a special case of the general bound ‖R_z‖ ≤ 1/|Im(z)|
- The bounded resolvent is THE defining characteristic separating self-adjoint
  from merely symmetric operators
- Essential for proving the spectral theorem via functional calculus

**Physical Interpretation:**
In quantum mechanics with Hamiltonian H, the resolvent (E - H)⁻¹ represents
the system's response to energy probes. The bound says probing at complex
energy i produces a bounded response - no resonances at non-real energies.

**Comparison with R_{-i}:**
The conjugate resolvent `resolvent_at_neg_i` inverts (A + iI) and satisfies
the identical bound ‖R_{-i}‖ ≤ 1 by the same argument (using -i instead of i).
-/
theorem self_adjoint_range_all_z
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃! (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
  intro φ

  -- Part 1: Existence via density argument
  -- Key lemma: orthogonal complement of Range(A - zI) is {0}
  have h_ker_zero : ∀ (χ : H),
      (∀ (ψ : gen.domain), ⟪gen.op ψ - z • (ψ : H), χ⟫_ℂ = 0) → χ = 0 := by
    intro χ h_orth

    -- From orthogonality: ⟪Aψ, χ⟫ = z̄·⟪ψ, χ⟫ for all ψ ∈ domain
    have h_eigen_cond : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
        ⟪gen.op ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by
      intro ψ hψ
      have h := h_orth ⟨ψ, hψ⟩
      simp only at h
      calc ⟪gen.op ⟨ψ, hψ⟩, χ⟫_ℂ
          = ⟪gen.op ⟨ψ, hψ⟩ - z • ψ + z • ψ, χ⟫_ℂ := by simp
        _ = ⟪gen.op ⟨ψ, hψ⟩ - z • ψ, χ⟫_ℂ + ⟪z • ψ, χ⟫_ℂ := by rw [inner_add_left]
        _ = 0 + ⟪z • ψ, χ⟫_ℂ := by rw [h]
        _ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by rw [inner_smul_left]; ring

    set z_bar := (starRingEnd ℂ) z with hz_bar_def

    -- (A - iI) is surjective, so find η ∈ domain with (A - iI)η = (z̄ - i)•χ
    obtain ⟨η, hη_dom, hη_eq⟩ := hsa.2 ((z_bar - I) • χ)

    -- (A + iI) is surjective, so find ξ ∈ domain with (A + iI)ξ = (z̄ + i)•χ
    obtain ⟨ξ, hξ_dom, hξ_eq⟩ := hsa.1 ((z_bar + I) • χ)

    -- From hη_eq: Aη = (z̄ - i)•χ + i•η
    have h_Aη : gen.op ⟨η, hη_dom⟩ = (z_bar - I) • χ + I • η := by
      calc gen.op ⟨η, hη_dom⟩
          = (gen.op ⟨η, hη_dom⟩ - I • η) + I • η := by simp
        _ = (z_bar - I) • χ + I • η := by rw [hη_eq]

    have h_eigen_η : ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ = z_bar * ⟪η, χ⟫_ℂ := h_eigen_cond η hη_dom

    have h_inner_Aη : ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ =
        (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
      calc ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, χ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, χ⟫_ℂ + ⟪I • η, χ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, χ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]; simp

    have h_conj_zbar_minus_I : (starRingEnd ℂ) (z_bar - I) = z + I := by
      simp [hz_bar_def]

    have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I

    have h_relation_η : (z_bar + I) * ⟪η, χ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      have h1 := h_eigen_η
      have h2 := h_inner_Aη
      rw [h_conj_zbar_minus_I, h_conj_I] at h2
      calc (z_bar + I) * ⟪η, χ⟫_ℂ
          = z_bar * ⟪η, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by ring
        _ = ⟪gen.op ⟨η, hη_dom⟩, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by rw [h1]
        _ = ((z + I) * ‖χ‖^2 + (-I) * ⟪η, χ⟫_ℂ) + I * ⟪η, χ⟫_ℂ := by rw [h2]
        _ = (z + I) * ‖χ‖^2 := by ring

    -- Similar for ξ
    have h_Aξ : gen.op ⟨ξ, hξ_dom⟩ = (z_bar + I) • χ - I • ξ := by
      calc gen.op ⟨ξ, hξ_dom⟩
          = (gen.op ⟨ξ, hξ_dom⟩ + I • ξ) - I • ξ := by simp
        _ = (z_bar + I) • χ - I • ξ := by rw [hξ_eq]

    have h_eigen_ξ : ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ = z_bar * ⟪ξ, χ⟫_ℂ := h_eigen_cond ξ hξ_dom

    have h_inner_Aξ : ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ =
        (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
      calc ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ
          = ⟪(z_bar + I) • χ - I • ξ, χ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪(z_bar + I) • χ, χ⟫_ℂ - ⟪I • ξ, χ⟫_ℂ := by rw [inner_sub_left]
        _ = (starRingEnd ℂ) (z_bar + I) * ⟪χ, χ⟫_ℂ - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
            rw [inner_self_eq_norm_sq_to_K]; simp

    have h_conj_zbar_plus_I : (starRingEnd ℂ) (z_bar + I) = z - I := by
      simp [hz_bar_def]; ring

    have h_relation_ξ : (z_bar - I) * ⟪ξ, χ⟫_ℂ = (z - I) * ‖χ‖^2 := by
      have h1 := h_eigen_ξ
      have h2 := h_inner_Aξ
      rw [h_conj_zbar_plus_I, h_conj_I] at h2
      calc (z_bar - I) * ⟪ξ, χ⟫_ℂ
          = z_bar * ⟪ξ, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by ring
        _ = ⟪gen.op ⟨ξ, hξ_dom⟩, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by rw [h1]
        _ = ((z - I) * ‖χ‖^2 - (-I) * ⟪ξ, χ⟫_ℂ) - I * ⟪ξ, χ⟫_ℂ := by rw [h2]
        _ = (z - I) * ‖χ‖^2 := by ring

    -- Key: use symmetry ⟪Aη, ξ⟫ = ⟪η, Aξ⟫
    have h_sym : ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ = ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ :=
      gen.symmetric ⟨η, hη_dom⟩ ⟨ξ, hξ_dom⟩

    have h_LHS : ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪gen.op ⟨η, hη_dom⟩, ξ⟫_ℂ
          = ⟪(z_bar - I) • χ + I • η, ξ⟫_ℂ := by rw [h_Aη]
        _ = ⟪(z_bar - I) • χ, ξ⟫_ℂ + ⟪I • η, ξ⟫_ℂ := by rw [inner_add_left]
        _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, ξ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, ξ⟫_ℂ := by
            rw [inner_smul_left, inner_smul_left]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ + (-I) * ⟪η, ξ⟫_ℂ := by rw [h_conj_zbar_minus_I, h_conj_I]
        _ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by ring

    have h_RHS : ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      calc ⟪η, gen.op ⟨ξ, hξ_dom⟩⟫_ℂ
          = ⟪η, (z_bar + I) • χ - I • ξ⟫_ℂ := by rw [h_Aξ]
        _ = ⟪η, (z_bar + I) • χ⟫_ℂ - ⟪η, I • ξ⟫_ℂ := by rw [inner_sub_right]
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by rw [inner_smul_right, inner_smul_right]

    have h_cancel : (z + I) * ⟪χ, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ := by
      have h : (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
        rw [← h_LHS, ← h_RHS, h_sym]
      calc (z + I) * ⟪χ, ξ⟫_ℂ
          = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by ring
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by rw [h]
        _ = (z_bar + I) * ⟪η, χ⟫_ℂ := by ring

    have h_chi_xi_eq : (z + I) * ⟪χ, ξ⟫_ℂ = (z + I) * ‖χ‖^2 := by
      calc (z + I) * ⟪χ, ξ⟫_ℂ
          = (z_bar + I) * ⟪η, χ⟫_ℂ := h_cancel
        _ = (z + I) * ‖χ‖^2 := h_relation_η

    by_cases h_z_eq_neg_I : z = -I
    · -- Case z = -I
      have h_zbar_eq : z_bar = I := by
        simp only [hz_bar_def, h_z_eq_neg_I, map_neg, Complex.conj_I]; ring
      have h_zbar_minus_I : z_bar - I = 0 := by rw [h_zbar_eq]; ring
      have h_z_minus_I : z - I = -2 * I := by rw [h_z_eq_neg_I]; ring
      rw [h_zbar_minus_I, h_z_minus_I] at h_relation_ξ
      simp only [zero_mul] at h_relation_ξ
      have h_two_I_ne : (-2 : ℂ) * I ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, neg_eq_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true]
      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_relation_ξ.symm
        cases this with
        | inl h => exact absurd h h_two_I_ne
        | inr h => exact h
      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h
      exact norm_eq_zero.mp h_norm_zero

    · -- Case z ≠ -I
      have h_z_plus_i_ne : z + I ≠ 0 := by
        intro h_eq
        apply h_z_eq_neg_I
        calc z = z + I - I := by ring
          _ = 0 - I := by rw [h_eq]
          _ = -I := by ring

      have h_inner_chi_xi : ⟪χ, ξ⟫_ℂ = ‖χ‖^2 := by
        have := mul_left_cancel₀ h_z_plus_i_ne h_chi_xi_eq
        calc ⟪χ, ξ⟫_ℂ = (‖χ‖^2 : ℂ) := this
          _ = ‖χ‖^2 := by norm_cast

      have h_inner_xi_chi : ⟪ξ, χ⟫_ℂ = ‖χ‖^2 := by
        have h1 : ⟪ξ, χ⟫_ℂ = (starRingEnd ℂ) ⟪χ, ξ⟫_ℂ := (inner_conj_symm ξ χ).symm
        rw [h_inner_chi_xi] at h1
        simp at h1
        exact h1

      have h_final : (z_bar - I) * (‖χ‖^2 : ℂ) = (z - I) * ‖χ‖^2 := by
        calc (z_bar - I) * (‖χ‖^2 : ℂ)
            = (z_bar - I) * ⟪ξ, χ⟫_ℂ := by rw [← h_inner_xi_chi]
          _ = (z - I) * ↑‖χ‖^2 := h_relation_ξ

      have h_diff_zero : (z_bar - z) * (‖χ‖^2 : ℂ) = 0 := by
        have : (z_bar - I) * (‖χ‖^2 : ℂ) - (z - I) * ‖χ‖^2 = 0 := by
          rw [h_final]; ring
        calc (z_bar - z) * (‖χ‖^2 : ℂ)
            = (z_bar - I - (z - I)) * ‖χ‖^2 := by ring
          _ = (z_bar - I) * ‖χ‖^2 - (z - I) * ‖χ‖^2 := by ring
          _ = 0 := this

      have h_zbar_minus_z_ne : z_bar - z ≠ 0 := by
        intro h_eq
        have h_zbar_eq_z : z_bar = z := sub_eq_zero.mp h_eq
        have h_im_zero : z.im = 0 := by
          have h1 : ((starRingEnd ℂ) z).im = z.im := by
            rw [hz_bar_def] at h_zbar_eq_z
            exact congrArg Complex.im h_zbar_eq_z
          simp only [Complex.conj_im] at h1
          linarith
        exact hz h_im_zero

      have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
        have := mul_eq_zero.mp h_diff_zero
        cases this with
        | inl h => exact absurd h h_zbar_minus_z_ne
        | inr h => exact h

      have h_norm_zero : ‖χ‖ = 0 := by
        have h : (‖χ‖ : ℂ) = 0 := sq_eq_zero_iff.mp h_norm_sq_zero
        exact Complex.ofReal_eq_zero.mp h

      exact norm_eq_zero.mp h_norm_zero

  -- Part 2: Range is closed
  have h_range_closed : IsClosed (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro u φ_lim hu_range hφ_lim

    have hu_cauchy : CauchySeq u := hφ_lim.cauchySeq
    choose ψ_seq hψ_seq using fun n => Set.mem_range.mp (hu_range n)

    have hψ_cauchy : CauchySeq (fun n => (ψ_seq n : H)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hε_scaled : 0 < |z.im| * ε := mul_pos (abs_pos.mpr hz) hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu_cauchy (|z.im| * ε) hε_scaled
      use N
      intro m hm n hn
      have h_sub_mem : (ψ_seq m : H) - (ψ_seq n : H) ∈ gen.domain :=
        gen.domain.sub_mem (ψ_seq m).property (ψ_seq n).property
      have h_bound := lower_bound_estimate gen z hz ((ψ_seq m : H) - (ψ_seq n : H)) h_sub_mem

      have h_diff : gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
                    z • ((ψ_seq m : H) - (ψ_seq n : H)) = u m - u n := by
        have op_sub := gen.op.map_sub (ψ_seq m) (ψ_seq n)
        have op_eq : gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ =
                     gen.op (ψ_seq m) - gen.op (ψ_seq n) := by
          convert op_sub using 1
        calc gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ - z • ((ψ_seq m : H) - (ψ_seq n : H))
            = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - z • ((ψ_seq m : H) - (ψ_seq n : H)) := by rw [op_eq]
          _ = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - (z • (ψ_seq m : H) - z • (ψ_seq n : H)) := by
              rw [smul_sub]
          _ = (gen.op (ψ_seq m) - z • (ψ_seq m : H)) - (gen.op (ψ_seq n) - z • (ψ_seq n : H)) := by abel
          _ = u m - u n := by rw [hψ_seq m, hψ_seq n]

      rw [h_diff] at h_bound
      have h_ubound : dist (u m) (u n) < |z.im| * ε := hN m hm n hn
      rw [dist_eq_norm] at h_ubound
      have h_chain : |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖ < |z.im| * ε := by
        calc |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖
            ≤ ‖u m - u n‖ := h_bound
          _ < |z.im| * ε := h_ubound
      have h_pos : 0 < |z.im| := abs_pos.mpr hz
      rw [dist_eq_norm]
      exact (mul_lt_mul_left h_pos).mp h_chain

    obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy

    let R := resolvent_at_i gen hsa

    have h_AiI : ∀ n, gen.op (ψ_seq n) - I • (ψ_seq n : H) = u n + (z - I) • (ψ_seq n : H) := by
      intro n
      have h := hψ_seq n
      calc gen.op (ψ_seq n) - I • (ψ_seq n : H)
          = (gen.op (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := by
              rw [sub_smul]; abel
        _ = u n + (z - I) • (ψ_seq n : H) := by rw [h]

    have h_AiI_lim : Tendsto (fun n => gen.op (ψ_seq n) - I • (ψ_seq n : H))
                            atTop (𝓝 (φ_lim + (z - I) • ψ_lim)) := by
      have h1 : Tendsto u atTop (𝓝 φ_lim) := hφ_lim
      have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
        Tendsto.const_smul hψ_lim (z - I)
      have h3 : Tendsto (fun n => u n + (z - I) • (ψ_seq n : H)) atTop
                        (𝓝 (φ_lim + (z - I) • ψ_lim)) := Tendsto.add h1 h2
      convert h3 using 1
      ext n
      exact h_AiI n

    have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
                        R (gen.op ⟨ψ, hψ⟩ - I • ψ) = ψ := by
      intro ψ hψ
      let η := gen.op ⟨ψ, hψ⟩ - I • ψ
      have h_Rη_mem := resolvent_solution_mem gen hsa η
      have h_Rη_eq := resolvent_solution_eq gen hsa η
      exact resolvent_at_i_unique gen hsa η (R η) ψ h_Rη_mem hψ h_Rη_eq rfl

    have h_R_lim : Tendsto (fun n => R (gen.op (ψ_seq n) - I • (ψ_seq n : H)))
                          atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) :=
      R.continuous.tendsto _ |>.comp h_AiI_lim

    have h_R_eq : ∀ n, R (gen.op (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := by
      intro n
      exact h_R_inverse (ψ_seq n : H) (ψ_seq n).property

    have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := by
      convert h_R_lim using 1
      ext n
      exact (h_R_eq n).symm

    have h_ψ_lim_eq : ψ_lim = R (φ_lim + (z - I) • ψ_lim) :=
      tendsto_nhds_unique hψ_lim h_ψ_lim_alt

    have h_ψ_lim_domain : ψ_lim ∈ gen.domain := by
      rw [h_ψ_lim_eq]
      exact resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)

    have h_eq : gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim = φ_lim := by
      have h_AiI_ψ_lim : gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                          resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
                         I • R (φ_lim + (z - I) • ψ_lim) = φ_lim + (z - I) • ψ_lim :=
        resolvent_solution_eq gen hsa (φ_lim + (z - I) • ψ_lim)

      have h_op_eq : gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ =
                     gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                            resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ := by
        congr 1
        exact Subtype.ext h_ψ_lim_eq

      calc gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
          = gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                  resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
          z • R (φ_lim + (z - I) • ψ_lim) := by
            have h_smul : z • ψ_lim = z • R (φ_lim + (z - I) • ψ_lim) := by
              rw [h_ψ_lim_eq]
              exact
                congrArg (HSMul.hSMul z)
                  (congrArg (⇑R)
                    (congrArg (HAdd.hAdd φ_lim) (congrArg (HSMul.hSMul (z - I)) h_ψ_lim_eq)))
            rw [h_op_eq, h_smul]
        _ = (gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                    resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
            I • R (φ_lim + (z - I) • ψ_lim)) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          have hz_split : z • R (φ_lim + (z - I) • ψ_lim) =
                          I • R (φ_lim + (z - I) • ψ_lim) + (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
            rw [← add_smul]; congr 1; ring
          rw [hz_split]
          abel
        _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
            rw [h_AiI_ψ_lim]
        _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
        _ = φ_lim := by abel

    exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩

  -- Part 3: Range is dense
  have h_dense : Dense (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
    set S := Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) with hS_def

    let M : Submodule ℂ H := {
      carrier := S
      add_mem' := by
        intro a b ha hb
        obtain ⟨ψa, hψa⟩ := ha
        obtain ⟨ψb, hψb⟩ := hb
        refine ⟨⟨(ψa : H) + (ψb : H), gen.domain.add_mem ψa.property ψb.property⟩, ?_⟩
        have op_add := gen.op.map_add ψa ψb
        simp only [← hψa, ← hψb]
        calc gen.op ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
            = (gen.op ψa + gen.op ψb) - z • ((ψa : H) + (ψb : H)) := by
                congr 1
          _ = (gen.op ψa + gen.op ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
          _ = (gen.op ψa - z • (ψa : H)) + (gen.op ψb - z • (ψb : H)) := by abel
      zero_mem' := ⟨⟨0, gen.domain.zero_mem⟩, by
        simp only [smul_zero, sub_zero]
        exact gen.op.map_zero⟩
      smul_mem' := by
        intro c a ha
        obtain ⟨ψ, hψ⟩ := ha
        refine ⟨⟨c • (ψ : H), gen.domain.smul_mem c ψ.property⟩, ?_⟩
        have op_smul := gen.op.map_smul c ψ
        simp only [← hψ]
        calc gen.op ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
            = c • gen.op ψ - z • (c • (ψ : H)) := by
                congr 1
          _ = c • gen.op ψ - c • (z • (ψ : H)) := by rw [smul_comm z c]
          _ = c • (gen.op ψ - z • (ψ : H)) := by rw [smul_sub]
    }

    have hM_eq : (M : Set H) = S := rfl

    have h_M_orth : Mᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro χ hχ
      apply h_ker_zero χ
      intro ψ
      have h_mem : gen.op ψ - z • (ψ : H) ∈ M := ⟨ψ, rfl⟩
      exact Submodule.inner_right_of_mem_orthogonal h_mem hχ

    have h_M_top : M.topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      rw [h_M_orth]
      exact Submodule.bot_orthogonal_eq_top

    have h_M_dense : Dense (M : Set H) := by
      rw [dense_iff_closure_eq]
      have h_coe : closure (M : Set H) = (M.topologicalClosure : Set H) :=
        (Submodule.topologicalClosure_coe M).symm
      rw [h_coe, h_M_top]
      rfl

    rw [← hM_eq]
    exact h_M_dense

  -- Combine closed + dense = univ
  have h_eq_univ : Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H)) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure

  -- Existence
  have h_exists : ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ := by
    have : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at this
    exact Set.mem_range.mp this

  -- Uniqueness
  obtain ⟨ψ, hψ⟩ := h_exists
  use ψ, hψ
  intro ψ' hψ'

  have h_sub_mem : (ψ : H) - (ψ' : H) ∈ gen.domain :=
    gen.domain.sub_mem ψ.property ψ'.property

  have h_diff : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H)) = 0 := by
    have op_sub := gen.op.map_sub ψ ψ'
    have op_eq : gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ = gen.op ψ - gen.op ψ' := by
      convert op_sub using 1
    calc gen.op ⟨(ψ : H) - (ψ' : H), h_sub_mem⟩ - z • ((ψ : H) - (ψ' : H))
        = (gen.op ψ - gen.op ψ') - z • ((ψ : H) - (ψ' : H)) := by rw [op_eq]
      _ = (gen.op ψ - gen.op ψ') - (z • (ψ : H) - z • (ψ' : H)) := by rw [smul_sub]
      _ = (gen.op ψ - z • (ψ : H)) - (gen.op ψ' - z • (ψ' : H)) := by abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ

  have h_bound := lower_bound_estimate gen z hz ((ψ : H) - (ψ' : H)) h_sub_mem
  rw [h_diff] at h_bound
  simp only [norm_zero, ge_iff_le] at h_bound

  have h_im_pos : 0 < |z.im| := abs_pos.mpr hz

  have h_norm_zero : ‖(ψ : H) - (ψ' : H)‖ = 0 := by
    by_contra h_ne
    have h_pos : 0 < ‖(ψ : H) - (ψ' : H)‖ := by
      cases' (norm_nonneg ((ψ : H) - (ψ' : H))).lt_or_eq with h h
      · exact h
      · exact absurd h.symm h_ne
    have : 0 < |z.im| * ‖(ψ : H) - (ψ' : H)‖ := mul_pos h_im_pos h_pos
    linarith

  rw [norm_sub_rev] at h_norm_zero
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero))


/--
Resolvent operator (when it exists).

For self-adjoint generator A and Im(z) ≠ 0, this is well-defined and bounded.
-/
noncomputable def resolvent {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ)
    (hz : z.im ≠ 0) (hsa : Generator.IsSelfAdjoint gen) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun φ =>
        let ψ : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
        (ψ : H)

      map_add' := fun φ₁ φ₂ => by
        have h₁ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₁).exists
        have h₂ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ₂).exists
        have h_sum_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists

        have h_add_mem : ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                         ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H) ∈ gen.domain :=
          gen.domain.add_mem
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain).property
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain).property

        have h_add_eq : gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                                ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ -
                        z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                             ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) = φ₁ + φ₂ := by
          have op_add := gen.op.map_add
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain)
            (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)
          have op_eq : gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                               ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ =
                       gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                       gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) := by
            convert op_add using 1
          calc gen.op ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                       ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ -
               z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                    ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H))
              = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)) -
                z • (((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by rw [op_eq]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) +
                 gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain)) -
                (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by rw [smul_add]
            _ = (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H)) +
                (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) -
                 z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H)) := by abel
            _ = φ₁ + φ₂ := by rw [h₁, h₂]

        have h_eq : (Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists : gen.domain) =
                    ⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
                     ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).unique h_sum_eq h_add_eq

        calc ((Classical.choose (self_adjoint_range_all_z gen hsa z hz (φ₁ + φ₂)).exists : gen.domain) : H)
            = (⟨((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
               ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H), h_add_mem⟩ : gen.domain) := by rw [h_eq]
          _ = ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₁).exists : gen.domain) : H) +
              ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ₂).exists : gen.domain) : H) := rfl

      map_smul' := fun c φ => by
        simp only [RingHom.id_apply]

        have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
        have h_scaled_eq := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists

        have h_smul_mem : c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H) ∈ gen.domain :=
          gen.domain.smul_mem c (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain).property

        have h_smul_eq : gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ -
                         z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) = c • φ := by
          have op_smul := gen.op.map_smul c (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain)
          have op_eq : gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ =
                       c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) := by
            convert op_smul using 1
          calc gen.op ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ -
               z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H))
              = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                z • (c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [op_eq]
            _ = c • gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                c • (z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [smul_comm z c]
            _ = c • (gen.op (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) -
                z • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)) := by rw [smul_sub]
            _ = c • φ := by rw [h]

        have h_eq : (Classical.choose (self_adjoint_range_all_z gen hsa z hz (c • φ)).exists : gen.domain) =
                    ⟨c • ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H), h_smul_mem⟩ :=
          (self_adjoint_range_all_z gen hsa z hz (c • φ)).unique h_scaled_eq h_smul_eq

        have h_val := congrArg (↑· : gen.domain → H) h_eq
        simp only at h_val
        exact h_val
    }
    (1 / |z.im|)
    (by
      intro φ

      have h := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists
      have h_mem := (Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain).property

      have h_bound := lower_bound_estimate gen z hz
        ((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H) h_mem
      rw [h] at h_bound

      have h_im_pos : 0 < |z.im| := abs_pos.mpr hz

      calc ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)‖
          = (1 / |z.im|) * (|z.im| * ‖((Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists : gen.domain) : H)‖) := by field_simp
        _ ≤ (1 / |z.im|) * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_bound
            positivity
    )

/--
Resolvent identity: R(z) - R(w) = (z - w)R(z)R(w)

This fundamental identity relates resolvents at different points.
-/
theorem resolvent_identity {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent gen z hz hsa - resolvent gen w hw hsa =
    (z - w) • ((resolvent gen z hz hsa).comp (resolvent gen w hw hsa)) := by
  ext φ

  -- Let ψ_w = R_w(φ), so (A - wI)ψ_w = φ
  let ψ_w_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa w hw φ).exists
  let ψ_w := (ψ_w_sub : H)
  have h_w_domain : ψ_w ∈ gen.domain := ψ_w_sub.property
  have h_w_eq : gen.op ψ_w_sub - w • ψ_w = φ := Classical.choose_spec (self_adjoint_range_all_z gen hsa w hw φ).exists

  -- Let ψ_z = R_z(φ), so (A - zI)ψ_z = φ
  let ψ_z_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
  let ψ_z := (ψ_z_sub : H)
  have h_z_domain : ψ_z ∈ gen.domain := ψ_z_sub.property
  have h_z_eq : gen.op ψ_z_sub - z • ψ_z = φ := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists

  -- Let η = R_z(ψ_w), so (A - zI)η = ψ_w
  let η_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ_w).exists
  let η := (η_sub : H)
  have h_η_domain : η ∈ gen.domain := η_sub.property
  have h_η_eq : gen.op η_sub - z • η = ψ_w := Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ_w).exists

  have h_Rz : resolvent gen z hz hsa φ = ψ_z := rfl
  have h_Rw : resolvent gen w hw hsa φ = ψ_w := rfl
  have h_Rz_ψw : resolvent gen z hz hsa ψ_w = η := rfl

  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.comp_apply]
  rw [h_Rz, h_Rw, h_Rz_ψw]

  -- Key: (A - zI)ψ_w = φ + (w - z)ψ_w
  have h_Az_ψw : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = φ + (w - z) • ψ_w := by
    have h_Aw : gen.op ⟨ψ_w, h_w_domain⟩ = φ + w • ψ_w := by
      have h_eq : gen.op ⟨ψ_w, h_w_domain⟩ = gen.op ψ_w_sub := rfl
      calc gen.op ⟨ψ_w, h_w_domain⟩
          = (gen.op ψ_w_sub - w • ψ_w) + w • ψ_w := by abel
        _ = φ + w • ψ_w := by rw [h_w_eq]
    calc gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w
        = (φ + w • ψ_w) - z • ψ_w := by rw [h_Aw]
      _ = φ + (w - z) • ψ_w := by rw [sub_smul]; abel

  -- ψ_z + (w - z)η is in domain and solves (A - zI)x = φ + (w - z)ψ_w
  have h_sum_domain : ψ_z + (w - z) • η ∈ gen.domain := by
    apply gen.domain.add_mem h_z_domain
    exact gen.domain.smul_mem (w - z) h_η_domain

  have h_sum_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η) = φ + (w - z) • ψ_w := by
    have op_add := gen.op.map_add ψ_z_sub ((w - z) • η_sub)
    have h_smul_mem : (w - z) • η ∈ gen.domain := gen.domain.smul_mem (w - z) h_η_domain
    have op_eq : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ =
                 gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩ := by
      convert op_add using 1
    have op_smul := gen.op.map_smul (w - z) η_sub
    have op_smul_eq : gen.op ⟨(w - z) • η, h_smul_mem⟩ = (w - z) • gen.op η_sub := by
      convert op_smul using 1
    calc gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η)
        = (gen.op ψ_z_sub + gen.op ⟨(w - z) • η, h_smul_mem⟩) - z • (ψ_z + (w - z) • η) := by rw [op_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - z • (ψ_z + (w - z) • η) := by rw [op_smul_eq]
      _ = (gen.op ψ_z_sub + (w - z) • gen.op η_sub) - (z • ψ_z + z • ((w - z) • η)) := by rw [smul_add]
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - z • ((w - z) • η)) := by abel
      _ = (gen.op ψ_z_sub - z • ψ_z) + ((w - z) • gen.op η_sub - (w - z) • (z • η)) := by rw [smul_comm z (w - z) η]
      _ = (gen.op ψ_z_sub - z • ψ_z) + (w - z) • (gen.op η_sub - z • η) := by rw [← smul_sub]
      _ = φ + (w - z) • ψ_w := by rw [h_z_eq, h_η_eq]

  -- Both ψ_w and ψ_z + (w-z)η solve (A - zI)x = φ + (w-z)ψ_w
  -- By uniqueness they are equal
  let target := φ + (w - z) • ψ_w

  have h_ψw_solves : gen.op ⟨ψ_w, h_w_domain⟩ - z • ψ_w = target := h_Az_ψw
  have h_sum_solves : gen.op ⟨ψ_z + (w - z) • η, h_sum_domain⟩ - z • (ψ_z + (w - z) • η) = target := h_sum_eq

  have h_eq_vals : ψ_w = ψ_z + (w - z) • η := by
    have h1 : (⟨ψ_w, h_w_domain⟩ : gen.domain) = (⟨ψ_z + (w - z) • η, h_sum_domain⟩ : gen.domain) :=
      (self_adjoint_range_all_z gen hsa z hz target).unique h_ψw_solves h_sum_solves
    exact congrArg Subtype.val h1

  -- ψ_z - ψ_w = ψ_z - (ψ_z + (w - z)η) = -(w-z)η = (z-w)η
  calc ψ_z - ψ_w
      = ψ_z - (ψ_z + (w - z) • η) := by rw [h_eq_vals]
    _ = -((w - z) • η) := by abel
    _ = (-(w - z)) • η := by rw [neg_smul]
    _ = (z - w) • η := by ring_nf


/--
Bound on resolvent norm: ‖R_z‖ ≤ 1/|Im(z)|

This shows the resolvent is bounded with an explicit bound.
-/
theorem resolvent_bound {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent gen z hz hsa‖ ≤ 1 / |z.im| := by
  -- Prove pointwise bound: ‖R_z(φ)‖ ≤ (1/|Im(z)|) · ‖φ‖
  have h_pointwise : ∀ φ : H, ‖resolvent gen z hz hsa φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
    intro φ

    -- ψ := R_z(φ) is the unique element satisfying (A - zI)ψ = φ
    let ψ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ).exists
    let ψ := (ψ_sub : H)

    -- ψ is in the domain
    have h_domain : ψ ∈ gen.domain := ψ_sub.property

    -- (A - zI)ψ = φ
    have h_eq : gen.op ψ_sub - z • ψ = φ :=
      Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ).exists

    -- From lower_bound_estimate: ‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖
    have h_lower := lower_bound_estimate gen z hz ψ h_domain

    -- Substituting (A - zI)ψ = φ: ‖φ‖ ≥ |Im(z)| · ‖ψ‖
    rw [h_eq] at h_lower

    -- Rearrange: ‖ψ‖ ≤ ‖φ‖ / |Im(z)|
    have h_im_pos : 0 < |z.im| := abs_pos.mpr hz

    have h_ψ_bound : ‖ψ‖ ≤ ‖φ‖ / |z.im| := by
      have h_mul : |z.im| * ‖ψ‖ ≤ ‖φ‖ := h_lower
      calc ‖ψ‖
          = (|z.im|)⁻¹ * (|z.im| * ‖ψ‖) := by field_simp
        _ ≤ (|z.im|)⁻¹ * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_mul
            exact inv_nonneg.mpr (abs_nonneg _)
        _ = ‖φ‖ / |z.im| := by rw [inv_mul_eq_div]

    -- resolvent gen z hz hsa φ = ψ by definition
    have h_res_eq : resolvent gen z hz hsa φ = ψ := rfl

    calc ‖resolvent gen z hz hsa φ‖
        = ‖ψ‖ := by rw [h_res_eq]
      _ ≤ ‖φ‖ / |z.im| := h_ψ_bound
      _ = (1 / |z.im|) * ‖φ‖ := by ring

  -- Convert pointwise bound to operator norm bound
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg
    · norm_num
    · exact abs_nonneg _
  · exact h_pointwise

/-- **Resolvent Adjoint Identity**

For a self-adjoint generator A and z with Im(z) ≠ 0, the adjoint of the resolvent
satisfies:
  R(z)* = R(z̄)

**Proof:**
Let ξ = R(z)ψ and η = R(z̄)φ. Then:
- (A - zI)ξ = ψ, so Aξ = ψ + zξ
- (A - z̄I)η = φ, so Aη = φ + z̄η


**Significance:**
This identity is essential for proving that the Yosida approximants (after symmetrization)
are self-adjoint, which in turn ensures exp(itA_n) is unitary.
-/
theorem resolvent_adjoint {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    (resolvent gen z hz hsa).adjoint =
    resolvent gen (starRingEnd ℂ z) (by simp only [Complex.conj_im, neg_ne_zero]; exact hz) hsa := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ

  -- By definition of adjoint: ⟨T*φ, ψ⟩ = ⟨φ, Tψ⟩
  rw [ContinuousLinearMap.adjoint_inner_left]
  -- Goal: ⟨φ, R(z)ψ⟩ = ⟨R(z̄)φ, ψ⟩

  -- Set up notation
  set z_bar := (starRingEnd ℂ) z with hz_bar_def
  have hz_bar : z_bar.im ≠ 0 := by rw [hz_bar_def]; simp only [Complex.conj_im, neg_ne_zero]; exact hz

  -- Let ξ = R(z)ψ, so (A - zI)ξ = ψ
  let ξ_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z hz ψ).exists
  let ξ := (ξ_sub : H)
  have hξ_domain : ξ ∈ gen.domain := ξ_sub.property
  have hξ_eq : gen.op ξ_sub - z • ξ = ψ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz ψ).exists
  have hξ_def : resolvent gen z hz hsa ψ = ξ := rfl

  -- Let η = R(z̄)φ, so (A - z̄I)η = φ
  let η_sub : gen.domain := Classical.choose (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  let η := (η_sub : H)
  have hη_domain : η ∈ gen.domain := η_sub.property
  have hη_eq : gen.op η_sub - z_bar • η = φ :=
    Classical.choose_spec (self_adjoint_range_all_z gen hsa z_bar hz_bar φ).exists
  have hη_def : resolvent gen z_bar hz_bar hsa φ = η := rfl

  -- Rewrite goal using these definitions
  rw [hξ_def, hη_def]
  -- Goal: ⟨φ, ξ⟩ = ⟨η, ψ⟩

  -- From hξ_eq: Aξ = ψ + z•ξ
  have hAξ : gen.op ξ_sub = ψ + z • ξ := by
    calc gen.op ξ_sub = (gen.op ξ_sub - z • ξ) + z • ξ := by abel
      _ = ψ + z • ξ := by rw [hξ_eq]

  -- From hη_eq: Aη = φ + z̄•η
  have hAη : gen.op η_sub = φ + z_bar • η := by
    calc gen.op η_sub = (gen.op η_sub - z_bar • η) + z_bar • η := by abel
      _ = φ + z_bar • η := by rw [hη_eq]

  -- Key calculation using symmetry of A
  -- ⟨Aη, ξ⟩ = ⟨η, Aξ⟩
  have h_sym : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪η, gen.op ξ_sub⟫_ℂ := gen.symmetric η_sub ξ_sub

  -- Expand LHS: ⟨Aη, ξ⟩ = ⟨φ + z̄•η, ξ⟩ = ⟨φ, ξ⟩ + z•⟨η, ξ⟩
  have h_LHS : ⟪gen.op η_sub, ξ⟫_ℂ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪gen.op η_sub, ξ⟫_ℂ
        = ⟪φ + z_bar • η, ξ⟫_ℂ := by rw [hAη]
      _ = ⟪φ, ξ⟫_ℂ + ⟪z_bar • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = ⟪φ, ξ⟫_ℂ + (starRingEnd ℂ) z_bar • ⟪η, ξ⟫_ℂ := by rw [inner_smul_left]; exact rfl
      _ = ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by simp [hz_bar_def]

  -- Expand RHS: ⟨η, Aξ⟩ = ⟨η, ψ + z•ξ⟩ = ⟨η, ψ⟩ + z•⟨η, ξ⟩
  have h_RHS : ⟪η, gen.op ξ_sub⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    calc ⟪η, gen.op ξ_sub⟫_ℂ
        = ⟪η, ψ + z • ξ⟫_ℂ := by rw [hAξ]
      _ = ⟪η, ψ⟫_ℂ + ⟪η, z • ξ⟫_ℂ := by rw [inner_add_right]
      _ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by rw [inner_smul_right] ; exact rfl

  -- From h_sym, h_LHS, h_RHS: ⟨φ, ξ⟩ + z•⟨η, ξ⟩ = ⟨η, ψ⟩ + z•⟨η, ξ⟩
  have h_cancel : ⟪φ, ξ⟫_ℂ + z • ⟪η, ξ⟫_ℂ = ⟪η, ψ⟫_ℂ + z • ⟪η, ξ⟫_ℂ := by
    rw [← h_LHS, ← h_RHS, h_sym]

  -- Cancel z•⟨η, ξ⟩ from both sides
  exact add_right_cancel h_cancel

end StonesTheorem.Resolvent
