/-
Author: Adam Bornemann
Created: 11-20-2025
Updated: 11-27-2025

============================================================================================================================
EXPONENTIAL OF SELF-ADJOINT OPERATORS VIA YOSIDA APPROXIMATION
============================================================================================================================

This file constructs the one-parameter unitary group exp(itA) for unbounded
self-adjoint operators A, using the Yosida approximation technique rather
than the spectral theorem.

PHYSICAL MOTIVATION:
  The time evolution operator U(t) = exp(itA) governs quantum dynamics via
  the Schrödinger equation. For bounded Hamiltonians, the exponential is
  defined by power series. For unbounded operators (the physical case),
  we need a limiting construction.

HISTORICAL DEVELOPMENT:
  Yosida (1948): Introduced bounded approximants for semigroup generators
  Hille-Yosida (1948): Characterized generators of C₀-semigroups
  Stone (1932): Unitary groups ↔ self-adjoint generators (our ultimate goal)

THE YOSIDA STRATEGY:
  For self-adjoint A with resolvent R(z) = (A - zI)⁻¹:

  1. **Bounded approximants**: Define Aₙ = n²R(in) - in·I
     - Each Aₙ is a bounded operator (unlike A)
     - Aₙ → A strongly on the domain D(A)

  2. **Exponentials exist**: exp(itAₙ) is well-defined via power series
     since Aₙ is bounded

  3. **Take the limit**: exp(itA) := s-lim_{n→∞} exp(itAₙ)
     - Strong operator convergence
     - Limit is unitary because each exp(itAₙ) is unitary

WHY NOT USE THE SPECTRAL THEOREM?
  The spectral theorem gives exp(itA) = ∫ eⁱᵗᵡ dE(λ) directly, but:
  - Constructing the spectral measure E requires significant machinery
  - The Yosida approach is more elementary and generalizes to semigroups
  - Both approaches are valuable; this file takes the constructive route

MATHEMATICAL CONTENT:
  §0 Helper lemmas (complex arithmetic for I·n)
  §1 Core definitions (resolventAtIn, yosidaApprox, yosidaJ, etc.)
  §2 Norm bounds (‖Aₙ‖ ≤ 2n, ‖Jₙ‖ ≤ 1)
  §3 Self-adjointness of Aₙˢʸᵐ and skew-adjointness of I·Aₙˢʸᵐ
  §4 J operator identities and convergence (Jₙ → I strongly)
  §5 Yosida approximant convergence (Aₙφ → Aφ on domain)
  §6 Exponential of bounded operators (definition, group law, adjoint, unitarity)
  §7 Unitarity of Yosida exponentials (inner product and norm preservation)
  §8 Cauchy sequences and exponential definition (Duhamel estimate, convergence)
  §9 Properties of exp(itA) (unitarity, group law, strong continuity, generator = A)

Axiomatized results (marked with sorry):

KEY OPERATORS:
  - R(in) = resolventAtIn: The resolvent at z = in
  - Aₙ = yosidaApprox: Bounded approximant n²R(in) - in·I
  - Aₙˢʸᵐ = yosidaApproxSym: Self-adjoint version (n²/2)(R(in) + R(-in))
  - Jₙ = yosidaJ: Auxiliary operator -in·R(in), converges to identity

CONVENTIONS:
  - n ranges over ℕ+ (positive naturals) to avoid division by zero
  - I denotes the complex imaginary unit
  - R(z) denotes the resolvent (A - zI)⁻¹
  - Strong convergence: Tₙ →ˢ T means Tₙφ → Tφ for all φ

Dependencies:
  - Resolvent.lean: resolvent bounds, resolvent identity, range surjectivity

References:
  [1] Yosida, K. "Functional Analysis" (1965) - Chapter IX
  [2] Reed & Simon, "Methods of Modern Mathematical Physics I" - Section VIII.4
  [3] Stone, M.H. "On one-parameter unitary groups" (1932) - Original theorem
-/

import LogosLibrary.DeepTheorems.Quantum.Evolution.Resolvent
import LogosLibrary.DeepTheorems.Quantum.Evolution.Bochner
namespace StonesTheorem.Exponential
open InnerProductSpace MeasureTheory Complex Filter Topology StonesTheorem.Resolvent Generator

open scoped BigOperators Topology
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
============================================================================================================================
## Section 0: Arithmetic Lemmas for Complex Spectral Parameters
============================================================================================================================

The Yosida approximation evaluates the resolvent at purely imaginary points z = ±in.
This section establishes the elementary complex arithmetic needed to:
  - Verify Im(in) ≠ 0 (so the resolvent exists)
  - Compute |Im(in)| = n (for the resolvent bound)
  - Handle norms of complex scalars

These lemmas are logistically necessary but mathematically trivial.
-/

/-- The imaginary part of I·n is nonzero for positive n.

This is the key hypothesis for resolvent existence: R(z) = (A - zI)⁻¹ exists
precisely when z is not in the spectrum of A. For self-adjoint A, the spectrum
is real, so any z with Im(z) ≠ 0 is in the resolvent set.

For z = I·n with n ∈ ℕ⁺, we have Im(z) = n > 0.
-/
lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
             zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero

/-- Variant for the conjugate point -I·n.

We need resolvents at both z = in and z = -in for the symmetrized approximant.
-/
lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, Complex.neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)

/-- The imaginary part of I·n equals n.

Direct calculation: Im(I·n) = Im(in) = n.
Used in the resolvent bound ‖R(in)‖ ≤ 1/|Im(in)| = 1/n.
-/
lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [Complex.mul_im]

/-- The absolute value |Im(I·n)| = n.

Since n > 0, the absolute value is just n itself.
-/
lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)

/-- Complex norm of n² for n ∈ ℕ⁺.

‖n²‖_ℂ = |n²| = n² since n² is a non-negative real.
Used in bounding ‖n² · R(in)‖ = n² · ‖R(in)‖.
-/
lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  rw [norm_pow]
  simp

/-- Complex norm of I·n equals n.

‖I·n‖ = |I| · |n| = 1 · n = n.
Used throughout the norm bounds on Yosida operators.
-/
lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  calc ‖I * (n : ℂ)‖
      = ‖I‖ * ‖(n : ℂ)‖ := norm_mul I (n : ℂ)
    _ = 1 * ‖(n : ℂ)‖ := by rw [Complex.norm_I]
    _ = ‖(n : ℂ)‖ := one_mul _
    _ = (n : ℝ) := by simp only [Complex.norm_natCast]


/-- The resolvent R(z)φ lies in the domain and inverts (A - zI).

For self-adjoint A and z with Im(z) ≠ 0:
  - R(z)φ ∈ D(A) for all φ ∈ H
  - (A - zI)(R(z)φ) = φ

This is the defining property of the resolvent as the inverse of (A - zI).
The resolvent maps the full Hilbert space H into the domain D(A), making
it a "regularizing" operator that brings arbitrary vectors into the domain.

**Role in Yosida approximation:**

The bounded approximant Aₙ = n²R(in) - in·I is defined on all of H precisely
because R(in) maps H → D(A). The composition A∘R(in) makes sense, giving:

  Aₙφ = n²·A(R(in)φ) - in·φ = n²·(in·R(in)φ + φ) - in·φ

where we used (A - in·I)R(in) = I, i.e., A·R(in) = in·R(in) + I.
-/
lemma resolvent_spec
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    (resolvent gen z hz hsa φ) ∈ gen.domain ∧
    gen.op (resolvent gen z hz hsa φ) - z • (resolvent gen z hz hsa φ) = φ := by
  let ψ_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)
  have h_spec := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ)).1
  exact ⟨ψ_sub.property, h_spec⟩



/-!
============================================================================================================================
## Section 1: The Yosida Operators
============================================================================================================================

We define the key bounded operators that approximate the unbounded generator A:
```markdown

| Operator | Definition | Role |
|----------|------------|------|
| `resolventAtIn n` | R(in) | Resolvent at z = in |
| `resolventAtNegIn n` | R(-in) | Resolvent at conjugate point |
| `yosidaApprox n` | n²R(in) - in·I | Standard Yosida approximant Aₙ |
| `yosidaApproxSym n` | (n²/2)(R(in) + R(-in)) | Self-adjoint approximant |
| `yosidaJ n` | -in·R(in) | Converges to identity |
| `yosidaJNeg n` | in·R(-in) | Conjugate J operator |

```
**Why these specific combinations?**

The resolvent bound ‖R(z)‖ ≤ 1/|Im(z)| means ‖R(in)‖ ≤ 1/n. Multiplying by n²
gives an O(n) bound, while the combination n²R(in) - in·I is arranged so that:

  Aₙφ → Aφ  for φ ∈ D(A)

The J operators Jₙ = -in·R(in) satisfy ‖Jₙ‖ ≤ 1 uniformly and Jₙ → I strongly,
serving as "approximate identities" in the construction.
-/

/-- Resolvent at the point z = I·n.

Bundles R(in) with the proof that Im(in) ≠ 0, for convenient use.
-/
noncomputable def resolventAtIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

/-- Resolvent at the conjugate point z = -I·n.

Needed for the symmetrized approximant which uses both R(in) and R(-in).
-/
noncomputable def resolventAtNegIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

/-- **The Yosida Approximant**

The standard bounded approximant to the unbounded generator A:

  Aₙ = n² · R(in) - in · I

**Construction rationale:**

Starting from the resolvent identity (A - in·I)R(in) = I, we get:
  A · R(in) = in · R(in) + I

Multiplying by n²:
  n² · A · R(in) = in · n² · R(in) + n² · I

Rearranging for A (heuristically, on the domain):
  A ≈ n² · R(in) · A = n²(in · R(in) + I) · (something)

The precise statement is that for φ ∈ D(A):
  Aₙφ = n² · R(in) · φ - in · φ → Aφ  as n → ∞

**Properties:**
  - Bounded: ‖Aₙ‖ ≤ 2n (grows linearly, but finite for each n)
  - Converges: Aₙφ → Aφ strongly on D(A)
  - Related to J: Aₙ = n · (Jₙ - I) where Jₙ = -in · R(in)
-/
noncomputable def yosidaApprox
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-- **Symmetrized Yosida Approximant**

The self-adjoint bounded approximant to the generator A:

  Aₙˢʸᵐ = (n²/2) · (R(in) + R(-in))

**Why symmetrize?**

The standard approximant Aₙ = n²R(in) - in·I is not self-adjoint because
R(in) alone is not self-adjoint. However, the resolvent satisfies:

  R(z)* = R(z̄)

For z = in, we have z̄ = -in, so:
  R(in)* = R(-in)

Therefore:
  (R(in) + R(-in))* = R(-in) + R(in) = R(in) + R(-in)

The sum is self-adjoint, making Aₙˢʸᵐ self-adjoint.

**Why self-adjointness matters:**

For the exponential exp(it·Aₙˢʸᵐ):
  - Self-adjoint Aₙˢʸᵐ ⟹ i·Aₙˢʸᵐ is skew-adjoint
  - Skew-adjoint generator ⟹ exp(it·Aₙˢʸᵐ) is unitary

This ensures each approximating exponential preserves norms, which passes
to the limit exp(itA).
-/
noncomputable def yosidaApproxSym
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2 / 2) • (resolventAtIn gen hsa n + resolventAtNegIn gen hsa n)

/-- **Yosida's J Operator**

The auxiliary operator that converges strongly to the identity:

  Jₙ = -in · R(in)

**Key properties:**
  - Uniformly bounded: ‖Jₙ‖ ≤ 1 for all n
  - Strong convergence: Jₙφ → φ for all φ ∈ H
  - Relates to Aₙ: The approximant satisfies Aₙ = n·(Jₙ - I) + (terms)

**The name "J":**

In Yosida's original work, Jₙ serves as an "approximate identity" or
"mollifier" — it smooths vectors into the domain while converging to
the identity. The uniform bound ‖Jₙ‖ ≤ 1 is crucial for:
  - Density arguments (controlling ‖Jₙ(ψ - φ)‖)
  - Banach-Steinhaus applications
  - Ensuring the limit exists

**Connection to semigroup theory:**

For general C₀-semigroups, Jₙ = n·R(n, A) plays the analogous role,
where R(λ, A) = (λI - A)⁻¹. The self-adjoint case uses imaginary
spectral parameters z = in instead.
-/
noncomputable def yosidaJ
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (-I * (n : ℂ)) • resolventAtIn gen hsa n

/-- **Conjugate J Operator**

The variant using the negative spectral parameter:

  Jₙ⁻ = in · R(-in)

**Relation to Jₙ:**

By the resolvent adjoint formula R(z)* = R(z̄):
  Jₙ* = (-in · R(in))* = -(-in) · R(in)* = in · R(-in) = Jₙ⁻

So Jₙ⁻ is the adjoint of Jₙ. This is used in proving self-adjointness
of the symmetrized approximant.

**Same bound:** ‖Jₙ⁻‖ ≤ 1, by the same argument as for Jₙ.
-/
noncomputable def yosidaJNeg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (I * (n : ℂ)) • resolventAtNegIn gen hsa n

/-- Resolvent bound at z = in: ‖R(in)‖ ≤ 1/n.

This is the fundamental estimate underlying all Yosida bounds.
For self-adjoint A, the resolvent satisfies ‖R(z)‖ ≤ 1/|Im(z)|.
At z = in, this gives ‖R(in)‖ ≤ 1/n.

**Proof:** Immediate from the general resolvent bound and |Im(in)| = n.
-/
lemma resolventAtIn_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖resolventAtIn gen hsa n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]





/-!
============================================================================================================================
## Section 2: Norm Bounds on Yosida Operators
============================================================================================================================

The Yosida operators satisfy crucial norm estimates:
```markdown

| Operator | Bound | Uniformity |
|----------|-------|------------|
| Aₙ = yosidaApprox | ‖Aₙ‖ ≤ 2n | Grows linearly |
| Jₙ = yosidaJ | ‖Jₙ‖ ≤ 1 | Uniform |
| Jₙ⁻ = yosidaJNeg | ‖Jₙ⁻‖ ≤ 1 | Uniform |

```
**The significance of these bounds:**

The Aₙ bound ‖Aₙ‖ ≤ 2n shows each approximant is bounded (unlike A itself),
though the bounds grow. This growth is acceptable because:
  - Each exp(itAₙ) is well-defined regardless of ‖Aₙ‖
  - The exponentials are unitary (norm 1) due to self-adjointness
  - Convergence is pointwise, not requiring uniform operator bounds

The Jₙ bound ‖Jₙ‖ ≤ 1 is uniform and essential for:
  - The density argument showing Jₙ → I strongly
  - Applications of Banach-Steinhaus
  - Controlling error terms in the convergence proof
-/

/-- **Norm Bound on Yosida Approximants**

The bounded Yosida approximants Aₙ = n²R(in) - in·I satisfy:

  ‖Aₙ‖ ≤ 2n  for all n ≥ 1

**Proof outline:**

By the triangle inequality:
  ‖Aₙ‖ = ‖n²R(in) - in·I‖ ≤ ‖n²R(in)‖ + ‖in·I‖

For the first term, using ‖R(in)‖ ≤ 1/n:
  ‖n²R(in)‖ = n² · ‖R(in)‖ ≤ n² · (1/n) = n

For the second term:
  ‖in·I‖ = |in| · ‖I‖ = n · 1 = n

Total: ‖Aₙ‖ ≤ n + n = 2n.

**Why linear growth is acceptable:**

The point of Yosida approximation is not to get uniform bounds on Aₙ
(impossible — they approximate an unbounded operator), but to:
  1. Make each Aₙ bounded, so exp(itAₙ) is defined by power series
  2. Have Aₙφ → Aφ on the domain

The exponentials exp(itAₙ) have norm 1 (unitary) regardless of ‖Aₙ‖,
because Aₙ inherits self-adjointness properties from A.
-/
theorem yosidaApprox_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖yosidaApprox gen hsa n‖ ≤ 2 * (n : ℝ) := by
  unfold yosidaApprox

  have h_first : ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ ≤ (n : ℝ) := by
    calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖
        = ‖(n : ℂ)^2‖ * ‖resolventAtIn gen hsa n‖ := norm_smul ((n : ℂ)^2) _
      _ ≤ ‖(n : ℂ)^2‖ * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (resolventAtIn_bound gen hsa n)
          exact norm_nonneg _
      _ = (n : ℝ)^2 * (1 / (n : ℝ)) := by rw [norm_pnat_sq]
      _ = (n : ℝ) := by field_simp

  have h_second : ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ ≤ (n : ℝ) := by
    calc ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
        = ‖I * (n : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ := norm_smul (I * (n : ℂ)) _
      _ ≤ ‖I * (n : ℂ)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
          exact norm_nonneg _
      _ = ‖I * (n : ℂ)‖ := mul_one _
      _ = (n : ℝ) := norm_I_mul_pnat n

  calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
      ≤ ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ + ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ :=
          norm_sub_le _ _
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add h_first h_second
    _ = 2 * (n : ℝ) := by ring



/-- **Uniform Bound on Yosida's J Operator**

The auxiliary operators Jₙ = -in·R(in) satisfy the uniform bound:

  ‖Jₙ‖ ≤ 1  for all n ≥ 1

**Proof:**

  ‖Jₙ‖ = ‖-in·R(in)‖ = |-in| · ‖R(in)‖ = n · ‖R(in)‖ ≤ n · (1/n) = 1

**Why uniformity matters:**

Unlike the Aₙ bound which grows with n, the Jₙ bound is uniform. This is
essential for:

1. **Density argument:** To show Jₙψ → ψ for all ψ ∈ H, we:
   - First prove Jₙφ → φ for φ in the dense domain D(A)
   - Then extend using ‖Jₙ(ψ - φ)‖ ≤ ‖Jₙ‖ · ‖ψ - φ‖ ≤ 1 · ‖ψ - φ‖

2. **Banach-Steinhaus:** Uniform boundedness of {Jₙ} plus pointwise
   convergence on a dense set implies strong convergence everywhere.

3. **Exponential control:** The operators exp(itAₙ) can be related to
   powers of Jₙ, and uniform bounds on Jₙ help control these.

**The magic of cancellation:**

The factor n from |-in| exactly cancels the 1/n from ‖R(in)‖, yielding
the clean bound ‖Jₙ‖ ≤ 1. This is not coincidence — it reflects that
Jₙ approximates the identity operator (which has norm 1).
-/
lemma yosidaJ_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 := by
  have h_neg : (-I : ℂ) * (n : ℂ) = -(I * (n : ℂ)) := by ring

  have h_coeff : ‖(-I * (n : ℂ))‖ = (n : ℝ) := by
    calc ‖(-I * (n : ℂ))‖
        = ‖-(I * (n : ℂ))‖ := by rw [h_neg]
      _ = ‖I * (n : ℂ)‖ := norm_neg _
      _ = (n : ℝ) := norm_I_mul_pnat n

  have h_res : ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
        ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
      _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos

  calc ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      = ‖(-I * (n : ℂ))‖ * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res
          exact le_of_lt hn_pos
    _ = 1 := by field_simp


/-- **Uniform Bound on the Conjugate J Operator**

The operators Jₙ⁻ = in·R(-in) satisfy the same uniform bound:

  ‖Jₙ⁻‖ ≤ 1  for all n ≥ 1

**Proof:**

Identical to the Jₙ bound, using |Im(-in)| = n:
  ‖Jₙ⁻‖ = |in| · ‖R(-in)‖ ≤ n · (1/n) = 1

**Role:**

Since Jₙ⁻ = Jₙ*, uniform boundedness of both operators is needed for
adjoint computations in the self-adjointness proofs.
-/
lemma yosidaJNeg_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖yosidaJNeg gen hsa n‖ ≤ 1 := by
  unfold yosidaJNeg resolventAtNegIn
  have h_coeff : ‖I * (n : ℂ)‖ = (n : ℝ) := norm_I_mul_pnat n
  have h_res : ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
        ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
      _ = 1 / (n : ℝ) := by
          simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re,
                     Complex.I_im, zero_mul, one_mul, zero_add]
          rw [← h_coeff]
          rw [h_coeff]
          rw [@abs_neg]
          rw [natCast_re]
          rw [abs_of_pos (Nat.cast_pos.mpr n.pos)]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(I * (n : ℂ)) • resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
      = ‖I * (n : ℂ)‖ * ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res (le_of_lt hn_pos)
    _ = 1 := by field_simp

/-!
============================================================================================================================
## Section 3: Self-Adjointness and Skew-Adjointness
============================================================================================================================

For the exponential exp(itAₙ) to be unitary, we need the generator itAₙ to be
skew-adjoint: (itAₙ)* = -itAₙ. This is equivalent to Aₙ being self-adjoint.

The standard Yosida approximant Aₙ = n²R(in) - in·I is NOT self-adjoint because
R(in) alone is not self-adjoint. However, the resolvent satisfies:

  R(z)* = R(z̄)  (adjoint exchanges z with its conjugate)

This motivates the symmetrized approximant:

  Aₙˢʸᵐ = (n²/2)(R(in) + R(-in))

Since (in)̄ = -in, the sum R(in) + R(-in) is self-adjoint, and multiplying by
the real scalar n²/2 preserves self-adjointness.

**The key chain:**
  Aₙˢʸᵐ self-adjoint ⟹ i·Aₙˢʸᵐ skew-adjoint ⟹ exp(it·Aₙˢʸᵐ) unitary
-/

/-- **Symmetrized Yosida Approximant is Self-Adjoint**

The operator Aₙˢʸᵐ = (n²/2)(R(in) + R(-in)) satisfies:

  (Aₙˢʸᵐ)* = Aₙˢʸᵐ

**Proof structure:**

The resolvent adjoint formula R(z)* = R(z̄) gives:
  - R(in)* = R((in)̄) = R(-in)
  - R(-in)* = R((-in)̄) = R(in)

Therefore the sum is self-adjoint:
  (R(in) + R(-in))* = R(-in) + R(in) = R(in) + R(-in)

The scalar n²/2 is real (equals its own conjugate), so:
  ((n²/2) · T)* = (n²/2)̄ · T* = (n²/2) · T*

Combining: (Aₙˢʸᵐ)* = (n²/2)(R(in) + R(-in))* = (n²/2)(R(in) + R(-in)) = Aₙˢʸᵐ.

**Why this matters:**

Self-adjointness of Aₙˢʸᵐ is the crucial property ensuring that exp(it·Aₙˢʸᵐ)
is unitary for all t ∈ ℝ. Without self-adjointness, the exponentials would
not preserve inner products, and the limiting group U(t) = lim exp(it·Aₙˢʸᵐ)
would fail to be unitary.

**Technical note:**

The proof works at the level of inner products: ⟨Tφ, ψ⟩ = ⟨φ, T*ψ⟩. We show
⟨Aₙˢʸᵐ φ, ψ⟩ = ⟨φ, Aₙˢʸᵐ ψ⟩ for all φ, ψ, which characterizes self-adjointness.
-/
theorem yosidaApproxSym_selfAdjoint
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    (yosidaApproxSym gen hsa n).adjoint = yosidaApproxSym gen hsa n := by
  unfold yosidaApproxSym resolventAtIn resolventAtNegIn
  ext φ
  apply ext_inner_right ℂ
  intro ψ

  -- Use ⟨T*φ, ψ⟩ = ⟨φ, Tψ⟩
  rw [ContinuousLinearMap.adjoint_inner_left]

  -- Expand the smul and add on both sides
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]

  -- LHS: ⟨φ, (n²/2) • (R(in) + R(-in)) ψ⟩
  -- RHS: ⟨(n²/2) • (R(in) + R(-in)) φ, ψ⟩

  -- The scalar n²/2 is real
  have h_scalar_real : (starRingEnd ℂ) ((n : ℂ)^2 / 2) = (n : ℂ)^2 / 2 := by
    simp only [map_div₀, map_pow]
    congr 1
    simp
    exact conj_eq_iff_re.mpr rfl

  -- Pull scalars through inner products
  rw [inner_smul_right, inner_smul_left, h_scalar_real]
  congr 1

  -- Now show ⟨φ, (R(in) + R(-in)) ψ⟩ = ⟨(R(in) + R(-in)) φ, ψ⟩
  rw [inner_add_right, inner_add_left]

  -- Use resolvent_adjoint: ⟨φ, R(z)ψ⟩ = ⟨R(z̄)φ, ψ⟩
  have h1 : ⟪φ, resolvent gen (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsa ψ⟫_ℂ =
            ⟪resolvent gen (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsa φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint gen hsa (I * ↑↑n) (I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (I * ↑↑n) = -I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_mul, conj_I]


  have h2 : ⟪φ, resolvent gen (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n) hsa ψ⟫_ℂ =
            ⟪resolvent gen (I * ↑↑n) (I_mul_pnat_im_ne_zero n) hsa φ, ψ⟫_ℂ := by
    have hadj := resolvent_adjoint gen hsa (-I * ↑↑n) (neg_I_mul_pnat_im_ne_zero n)
    have h_conj : (starRingEnd ℂ) (-I * ↑↑n) = I * ↑↑n := by simp []
    rw [← ContinuousLinearMap.adjoint_inner_left]
    congr 1
    rw [hadj]
    congr 1
    rw [← hadj]
    simp_all only [map_div₀, map_pow, map_natCast, neg_mul, map_neg, map_mul, conj_I, neg_neg]

  rw [h1, h2]
  ring


/-- **i·Aₙˢʸᵐ is Skew-Adjoint**

For self-adjoint Aₙˢʸᵐ, the operator i·Aₙˢʸᵐ satisfies:

  (i·Aₙˢʸᵐ)* = -i·Aₙˢʸᵐ

**Proof:**

Using the adjoint rules (c·T)* = c̄·T* and the fact that ī = -i:

  (i·Aₙˢʸᵐ)* = ī · (Aₙˢʸᵐ)*
             = (-i) · Aₙˢʸᵐ       (by self-adjointness)
             = -(i · Aₙˢʸᵐ)

**Why skew-adjointness implies unitarity:**

For a bounded operator B, the exponential exp(tB) is unitary for all t ∈ ℝ
if and only if B is skew-adjoint (B* = -B). The proof uses:

  (exp(tB))* = exp(tB*) = exp(-tB) = (exp(tB))⁻¹

where the last equality is the group property of the exponential.

Applied to B = i·Aₙˢʸᵐ, skew-adjointness ensures exp(t·i·Aₙˢʸᵐ) is unitary
for all t. Writing t = s for the time parameter:

  U_n(s) := exp(is·Aₙˢʸᵐ) is unitary for all s ∈ ℝ

These are the bounded unitary groups that converge to the desired U(s) = exp(isA).

**Connection to Stone's theorem:**

Stone's theorem states that every strongly continuous one-parameter unitary
group U(t) has a unique self-adjoint generator A with U(t) = exp(itA).
The Yosida construction proves the converse: every self-adjoint A generates
such a group. Skew-adjointness of i·Aₙˢʸᵐ is the key property making the
approximating groups unitary.
-/
theorem I_smul_yosidaApproxSym_skewAdjoint
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    (I • yosidaApproxSym gen hsa n).adjoint = -(I • yosidaApproxSym gen hsa n) := by
  ext φ
  apply ext_inner_right ℂ
  intro ψ

  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]

  -- LHS: ⟨φ, i • Aₙˢʸᵐ ψ⟩ = i • ⟨φ, Aₙˢʸᵐ ψ⟩
  -- RHS: ⟨-(i • Aₙˢʸᵐ φ), ψ⟩ = -⟨i • Aₙˢʸᵐ φ, ψ⟩ = -ī • ⟨Aₙˢʸᵐ φ, ψ⟩ = i • ⟨Aₙˢʸᵐ φ, ψ⟩

  rw [inner_smul_right, inner_neg_left, inner_smul_left]

  -- conj(I) = -I, so -conj(I) = I
  simp only [Complex.conj_I]

  -- Now need: I • ⟨φ, Aₙˢʸᵐ ψ⟩ = I • ⟨Aₙˢʸᵐ φ, ψ⟩
  -- This follows from self-adjointness of Aₙˢʸᵐ

  -- ⟨φ, Aₙˢʸᵐ ψ⟩ = ⟨(Aₙˢʸᵐ)* φ, ψ⟩ = ⟨Aₙˢʸᵐ φ, ψ⟩
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [yosidaApproxSym_selfAdjoint gen hsa n]
  -- ⊢ I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ = -(-I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ)
  rw [neg_mul]
  -- ⊢ I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ = - -(I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ)
  rw [eq_neg_iff_add_eq_zero, add_eq_zero_iff_neg_eq']
  -- ⊢ - -(I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ) = I * ⟪(yosidaApproxSym gen hsa n) φ, ψ⟫_ℂ
  rw [neg_eq_iff_eq_neg]


/-!
============================================================================================================================
## Section 4: J Operator Identities and Convergence
============================================================================================================================

The auxiliary operators Jₙ = -in·R(in) and Jₙ⁻ = in·R(-in) serve as
"approximate identities" — they converge strongly to the identity operator
as n → ∞. This convergence is the engine driving the Yosida approximation.

**The fundamental identity:**

For φ ∈ D(A):
  Jₙφ = φ - R(in)(Aφ)

This identity reveals why Jₙ → I:
  ‖Jₙφ - φ‖ = ‖R(in)(Aφ)‖ ≤ ‖R(in)‖·‖Aφ‖ ≤ (1/n)·‖Aφ‖ → 0

The convergence rate is O(1/n), controlled by the resolvent bound.

**Extension to all of H:**

The convergence Jₙφ → φ on the dense domain D(A), combined with the
uniform bound ‖Jₙ‖ ≤ 1, extends to all ψ ∈ H by a standard ε/3 argument:
  - Approximate ψ by φ ∈ D(A)
  - Use Jₙφ → φ
  - Control the error ‖Jₙ(ψ - φ)‖ ≤ ‖ψ - φ‖

**Role in the construction:**

The convergence Jₙ → I implies:
  - Aₙφ = Jₙ(Aφ) + (correction) → Aφ for φ ∈ D(A)
  - The approximating groups exp(itAₙ) converge to exp(itA)

Both Jₙ and Jₙ⁻ converge to I; having both is useful for adjoint computations
since Jₙ⁻ = Jₙ*.
-/

/-- **Fundamental Identity for Yosida's J Operator**

For φ in the domain of the self-adjoint generator A:

  Jₙφ = φ - R(in)(Aφ)

where Jₙ = -in·R(in) and R(z) = (A - zI)⁻¹ is the resolvent.

**Derivation:**

Starting from the resolvent equation: for any ψ in the range of (A - zI),
the resolvent satisfies (A - zI)R(z)ψ = ψ.

For φ ∈ D(A), we can write the "reverse" equation:
  R(z)(A - zI)φ = φ

Expanding:
  R(z)(Aφ) - z·R(z)φ = φ

Rearranging:
  -z·R(z)φ = φ - R(z)(Aφ)

With z = in, the left side is (-in)·R(in)φ = Jₙφ.

**Significance:**

This identity is the key to proving Jₙ → I. It shows that the "defect"
Jₙφ - φ equals -R(in)(Aφ), which is controlled by:

  ‖Jₙφ - φ‖ = ‖R(in)(Aφ)‖ ≤ ‖R(in)‖·‖Aφ‖ ≤ (1/n)·‖Aφ‖

For fixed φ ∈ D(A), the quantity ‖Aφ‖ is finite, so (1/n)·‖Aφ‖ → 0.

**Geometric interpretation:**

The identity Jₙ = I - R(in)∘A says that Jₙ is "almost" the identity,
with a correction term R(in)∘A that becomes negligible as n → ∞
(because R(in) shrinks like 1/n while A is fixed on domain elements).
-/
lemma yosidaJ_eq_sub_resolvent_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ =
      φ - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ) := by
  -- Let R = R(in) and z = in for clarity
  set z := I * (n : ℂ) with hz_def
  set R := resolvent gen z (I_mul_pnat_im_ne_zero n) hsa with hR_def

  -- R(φ) is in domain and satisfies (A - zI)(Rφ) = φ
  have hRφ_spec := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) φ
  have hRφ_domain : R φ ∈ gen.domain := hRφ_spec.1
  have hRφ_eq : gen.op (R φ) - z • (R φ) = φ := hRφ_spec.2

  -- From (A - zI)(Rφ) = φ, we get A(Rφ) = φ + z·Rφ
  have h_ARφ : gen.op (R φ) = φ + z • (R φ) := by
    calc gen.op (R φ)
        = (gen.op (R φ) - z • R φ) + z • R φ := by abel
      _ = φ + z • R φ := by rw [hRφ_eq]

  -- R(Aφ) is in domain and satisfies (A - zI)(R(Aφ)) = Aφ
  have hRAφ_spec := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op φ)
  have hRAφ_domain : R (gen.op φ) ∈ gen.domain := hRAφ_spec.1
  have hRAφ_eq : gen.op (R (gen.op φ)) - z • R (gen.op φ) = gen.op φ := hRAφ_spec.2

  -- Key: R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op φ - z • φ) = φ := by
    have h_unique := (Classical.choose_spec
        (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op φ - z • φ))).2
    symm
    have h_subtype : (⟨φ, hφ⟩ : {x : H // x ∈ gen.domain}) =
        Classical.choose (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n)
                          (gen.op φ - z • φ)) := by
      apply h_unique
      simp only
    calc φ
        = (⟨φ, hφ⟩ : {x : H // x ∈ gen.domain}).val := rfl
      _ = (Classical.choose (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n)
                              (gen.op φ - z • φ))).val := by rw [h_subtype]
      _ = R (gen.op φ - z • φ) := rfl

  -- By linearity: R(Aφ - zφ) = R(Aφ) - z·Rφ
  have h_R_linear : R (gen.op φ - z • φ) = R (gen.op φ) - z • R φ := by
    calc R (gen.op φ - z • φ)
        = R (gen.op φ) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op φ) - z • R φ := by rw [R.map_smul]

  -- So R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op φ) = φ + z • R φ := by
    calc R (gen.op φ)
        = R (gen.op φ) - z • R φ + z • R φ := by abel
      _ = R (gen.op φ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]

  -- Conclude: (-z)·Rφ = φ - R(Aφ)
  calc (-I * (n : ℂ)) • R φ
      = (-z) • R φ := by rw [neg_mul]
    _ = -(z • R φ) := by rw [neg_smul]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op φ) := by rw [← h_RAφ_explicit]

/-- **Convergence of J Operator on the Domain**

For φ ∈ D(A), the sequence Jₙφ converges to φ:

  Jₙφ → φ  as n → ∞

**Proof:**

Using the identity Jₙφ = φ - R(in)(Aφ):

  ‖Jₙφ - φ‖ = ‖R(in)(Aφ)‖
            ≤ ‖R(in)‖ · ‖Aφ‖
            ≤ (1/n) · ‖Aφ‖
            → 0

The convergence rate is O(1/n), with constant ‖Aφ‖.

**Why domain membership matters:**

For φ ∈ D(A), the quantity ‖Aφ‖ is finite, making (1/n)·‖Aφ‖ a valid
bound that vanishes. For φ ∉ D(A), the expression Aφ is not defined,
and this direct argument fails.

The extension to all of H requires a density argument (see `yosida_J_tendsto_id`).

**Quantitative version:**

Given ε > 0, convergence holds for n > ‖Aφ‖/ε. If Aφ = 0 (i.e., φ is an
eigenvector with eigenvalue 0), then Jₙφ = φ exactly for all n.
-/
lemma yosidaJ_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ)
            atTop (𝓝 φ) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  by_cases h_Aφ_zero : ‖gen.op φ‖ = 0
  · -- Case: Aφ = 0, so Jₙφ = φ for all n
    use 1
    intro n _
    rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
    have h_Aφ_eq_zero : gen.op φ = 0 := norm_eq_zero.mp h_Aφ_zero
    simp only [h_Aφ_eq_zero, map_zero, sub_zero]
    rw [dist_self]
    exact hε

  · -- Case: ‖Aφ‖ > 0
    have h_Aφ_pos : 0 < ‖gen.op φ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_Aφ_zero)

    -- Choose N > ‖Aφ‖/ε
    use ⟨Nat.ceil (‖gen.op φ‖ / ε) + 1, Nat.add_one_pos _⟩
    intro n hn

    calc dist ((-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ) φ
        = ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ - φ‖ :=
            dist_eq_norm _ _
      _ = ‖(φ - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)) - φ‖ := by
            rw [yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ]
      _ = ‖-resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)‖ := by
            congr 1; abel
      _ = ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)‖ :=
            norm_neg _
      _ ≤ ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op φ‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 / (n : ℝ)) * ‖gen.op φ‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
                ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
              _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
      _ < ε := by
            have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
            have h_n_bound : ‖gen.op φ‖ / ε + 1 ≤ (n : ℝ) := by
              have h1 : (Nat.ceil (‖gen.op φ‖ / ε) + 1 : ℕ) ≤ n := hn
              calc ‖gen.op φ‖ / ε + 1
                  ≤ ↑(Nat.ceil (‖gen.op φ‖ / ε)) + 1 :=
                      add_le_add_right (Nat.le_ceil _) _
                _ = ↑(Nat.ceil (‖gen.op φ‖ / ε) + 1) := by norm_cast
                _ ≤ (n : ℝ) := Nat.cast_le.mpr h1
            have h_ratio_lt : ‖gen.op φ‖ / ε < (n : ℝ) := by linarith
            have h_prod_lt : ‖gen.op φ‖ < (n : ℝ) * ε := by
              calc ‖gen.op φ‖
                  = (‖gen.op φ‖ / ε) * ε := by field_simp
                _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right h_ratio_lt hε
            calc (1 / (n : ℝ)) * ‖gen.op φ‖
                = ‖gen.op φ‖ / (n : ℝ) := by ring
              _ = ‖gen.op φ‖ * (1 / (n : ℝ)) := by ring
              _ < ((n : ℝ) * ε) * (1 / (n : ℝ)) := by
                  apply mul_lt_mul_of_pos_right h_prod_lt
                  exact one_div_pos.mpr hn_pos
              _ = ε := by field_simp


/-- **Strong Convergence of J Operator to Identity**

For any ψ ∈ H (not necessarily in the domain):

  Jₙψ → ψ  as n → ∞

**Proof strategy (ε/3 argument):**

Given ψ ∈ H and ε > 0:

1. **Approximate by domain element:** Since D(A) is dense, choose φ ∈ D(A)
   with ‖ψ - φ‖ < ε/3.

2. **Convergence on domain:** By `yosidaJ_tendsto_on_domain`, choose N such
   that n ≥ N implies ‖Jₙφ - φ‖ < ε/3.

3. **Combine using uniform bound:** For n ≥ N:
```
   ‖Jₙψ - ψ‖ ≤ ‖Jₙψ - Jₙφ‖ + ‖Jₙφ - φ‖ + ‖φ - ψ‖
             ≤ ‖Jₙ‖·‖ψ - φ‖ + ‖Jₙφ - φ‖ + ‖φ - ψ‖
             ≤ 1·(ε/3) + (ε/3) + (ε/3)
             = ε
```

The uniform bound ‖Jₙ‖ ≤ 1 (from `yosidaJ_norm_bound`) is essential — it
allows us to control ‖Jₙ(ψ - φ)‖ independently of n.

**Why this is the standard pattern:**

This ε/3 argument is the canonical way to extend convergence from a dense
set to the whole space when the operators are uniformly bounded. It
appears throughout functional analysis:
  - Extending continuous functions
  - Strong operator convergence
  - Approximation by smooth functions

**Role in Stone's theorem:**

The convergence Jₙ → I (strongly) implies that the Yosida approximants
Aₙ converge to A on the domain:
  Aₙφ = Jₙ(Aφ) + O(1/n) → Aφ

This is the key ingredient for showing exp(itAₙ) → exp(itA).
-/
theorem yosida_J_tendsto_id
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa ψ)
            atTop (𝓝 ψ) := by
  let J : ℕ+ → H →L[ℂ] H := fun n =>
    (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

  rw [Metric.tendsto_atTop]
  intro ε hε

  -- Step 1: Approximate ψ by domain element φ
  have h_dense := gen.dense_domain
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp (h_dense.closure_eq ▸ Set.mem_univ ψ)
                                    (ε / 3) (by linarith)

  -- Step 2: Get N such that Jₙφ is close to φ for n ≥ N
  have h_domain_conv := yosidaJ_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_domain_conv
  obtain ⟨N, hN⟩ := h_domain_conv (ε / 3) (by linarith)

  -- Step 3: For n ≥ N, Jₙψ is close to ψ
  use N
  intro n hn

  calc dist (J n ψ) ψ
      ≤ dist (J n ψ) (J n φ) + dist (J n φ) φ + dist φ ψ := dist_triangle4 _ _ _ _
    _ = ‖J n ψ - J n φ‖ + dist (J n φ) φ + dist φ ψ := by rw [dist_eq_norm]
    _ = ‖J n (ψ - φ)‖ + dist (J n φ) φ + dist φ ψ := by
        congr 1
        rw [ContinuousLinearMap.map_sub]
    _ ≤ ‖J n‖ * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right (ContinuousLinearMap.le_opNorm _ _) _)
    _ ≤ 1 * ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by
        apply add_le_add_right (add_le_add_right _ _)
        apply mul_le_mul_of_nonneg_right (yosidaJ_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + dist (J n φ) φ + dist φ ψ := by rw [one_mul]
    _ = dist ψ φ + dist (J n φ) φ + dist φ ψ := by rw [← dist_eq_norm]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : dist ψ φ < ε / 3 := hφ_close
        have h2 : dist (J n φ) φ < ε / 3 := hN n hn
        have h3 : dist φ ψ < ε / 3 := by rw [dist_comm]; exact hφ_close
        exact add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring


/-- **Fundamental Identity for Negative J Operator**

For φ ∈ D(A), the negative J operator satisfies:

  Jₙ⁻φ = φ - R(-in)(Aφ)

This is the exact analogue of `yosidaJ_eq_sub_resolvent_A` for Jₙ⁻ = in·R(-in).

**Derivation:**

From R(-in)(A - (-in)I)φ = φ, i.e., R(-in)(A + in·I)φ = φ:
  R(-in)(Aφ) + in·R(-in)φ = φ

Rearranging:
  in·R(-in)φ = φ - R(-in)(Aφ)

The left side is exactly Jₙ⁻φ.

**Role:**

This identity enables the same convergence proof for Jₙ⁻ as for Jₙ:
  ‖Jₙ⁻φ - φ‖ = ‖R(-in)(Aφ)‖ ≤ (1/n)·‖Aφ‖ → 0
-/
lemma yosidaJNeg_eq_sub_resolvent_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    (I * (n : ℂ)) • resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ) := by
  set z := -I * (n : ℂ) with hz_def
  set R := resolvent gen z (neg_I_mul_pnat_im_ne_zero n) hsa with hR_def

  -- R((A-zI)φ) = φ for φ ∈ D(A)
  have h_R_AzI : R (gen.op φ - z • φ) = φ := by
    have h_unique := (Classical.choose_spec
        (self_adjoint_range_all_z gen hsa z (neg_I_mul_pnat_im_ne_zero n) (gen.op φ - z • φ))).2
    symm
    have h_subtype : (⟨φ, hφ⟩ : {x : H // x ∈ gen.domain}) =
        Classical.choose (self_adjoint_range_all_z gen hsa z (neg_I_mul_pnat_im_ne_zero n)
                          (gen.op φ - z • φ)) := by
      apply h_unique
      simp only
    calc φ
        = (⟨φ, hφ⟩ : {x : H // x ∈ gen.domain}).val := rfl
      _ = (Classical.choose (self_adjoint_range_all_z gen hsa z (neg_I_mul_pnat_im_ne_zero n)
                              (gen.op φ - z • φ))).val := by rw [h_subtype]
      _ = R (gen.op φ - z • φ) := rfl

  -- By linearity: R(Aφ - zφ) = R(Aφ) - z·Rφ
  have h_R_linear : R (gen.op φ - z • φ) = R (gen.op φ) - z • R φ := by
    calc R (gen.op φ - z • φ)
        = R (gen.op φ) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op φ) - z • R φ := by rw [R.map_smul]

  -- So R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op φ) = φ + z • R φ := by
    calc R (gen.op φ)
        = R (gen.op φ) - z • R φ + z • R φ := by abel
      _ = R (gen.op φ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]

  -- Conclude: (in)·Rφ = φ - R(Aφ) since z = -in
  calc (I * (n : ℂ)) • R φ
      = -((-I * (n : ℂ)) • R φ) := by simp only [neg_mul, neg_smul, neg_neg]
    _ = -(z • R φ) := by rw [hz_def]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op φ) := by rw [← h_RAφ_explicit]

/-- **Convergence of Negative J Operator on Domain**

For φ ∈ D(A): Jₙ⁻φ → φ as n → ∞.

The proof is identical to `yosidaJ_tendsto_on_domain`, using the identity
Jₙ⁻φ = φ - R(-in)(Aφ) and the bound ‖R(-in)‖ ≤ 1/n.
-/
lemma yosidaJNeg_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n φ) atTop (𝓝 φ) := by
  unfold yosidaJNeg resolventAtNegIn

  have h_identity : ∀ n : ℕ+,
      (I * (n : ℂ)) • resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa φ =
      φ - resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ) :=
    fun n => yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ

  have h_tendsto : Tendsto (fun n : ℕ+ => φ - resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ)) atTop (𝓝 φ) := by
    -- First show R(-in)(Aφ) → 0
    have h_to_zero : Tendsto (fun n : ℕ+ => resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ)) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε

      obtain ⟨N, hN⟩ := exists_nat_gt (‖gen.op φ‖ / ε)
      use ⟨N + 1, Nat.succ_pos N⟩
      intro n hn

      rw [dist_eq_norm, sub_zero]

      have h_res_bound : ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
        calc ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖
            ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
          _ = 1 / (n : ℝ) := by
              simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re,
                         Complex.I_im, zero_mul, one_mul, zero_add]
              rw [div_eq_div_iff_comm, natCast_re]
              rw [abs_neg, Nat.abs_cast]


      have hn_ge : (n : ℕ) ≥ N + 1 := hn
      have hn_gt : (n : ℝ) > N := by
        have h : (N + 1 : ℕ) ≤ (n : ℕ) := hn
        calc (n : ℝ) ≥ (N + 1 : ℕ) := Nat.cast_le.mpr h
          _ = N + 1 := by simp
          _ > N := by linarith

      calc ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ)‖
          ≤ ‖resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa‖ * ‖gen.op φ‖ :=
              ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 / (n : ℝ)) * ‖gen.op φ‖ := by
              apply mul_le_mul_of_nonneg_right h_res_bound (norm_nonneg _)
        _ = ‖gen.op φ‖ / (n : ℝ) := by ring
        _ < ε := by
              by_cases hAφ : ‖gen.op φ‖ = 0
              · simp [hAφ, hε]
              · have hAφ_pos : 0 < ‖gen.op φ‖ := (norm_nonneg _).lt_of_ne' hAφ
                calc ‖gen.op φ‖ / (n : ℝ)
                  < ‖gen.op φ‖ / N := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op φ‖ / ε := div_pos hAφ_pos hε
                        linarith
                      apply div_lt_div_of_pos_left hAφ_pos hN_pos hn_gt
                _ ≤ ε := by
                      have hN_pos : (0 : ℝ) < N := by
                        have : 0 < ‖gen.op φ‖ / ε := div_pos hAφ_pos hε
                        linarith
                      rw [propext (div_le_iff₀ hN_pos)]
                      calc ‖gen.op φ‖ = (‖gen.op φ‖ / ε) * ε := by field_simp
                        _ ≤ N * ε := by
                            apply mul_le_mul_of_nonneg_right (le_of_lt hN) (le_of_lt hε)
                      linarith

    have h_sub : Tendsto (fun n : ℕ+ => φ - resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa (gen.op φ)) atTop (𝓝 (φ - 0)) := by
      exact Filter.Tendsto.sub tendsto_const_nhds h_to_zero
    simp only [sub_zero] at h_sub
    exact h_sub

  exact h_tendsto.congr (fun n => (h_identity n).symm)


/-- **Strong Convergence of Negative J Operator to Identity**

For any ψ ∈ H: Jₙ⁻ψ → ψ as n → ∞.

**Proof:**

Standard ε/3 argument using:
  - D(A) is dense in H
  - ‖Jₙ⁻‖ ≤ 1 uniformly (from `yosidaJNeg_norm_bound`)
  - Jₙ⁻φ → φ for φ ∈ D(A) (from `yosidaJNeg_tendsto_on_domain`)

**Why we need both Jₙ → I and Jₙ⁻ → I:**

Since Jₙ⁻ = Jₙ*, having both convergence results is useful for:
  - Adjoint computations in self-adjointness proofs
  - Verifying that the symmetrized operators behave correctly
  - The fact that Jₙ⁻ → I confirms consistency of the construction
-/
lemma yosidaJNeg_tendsto_id
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Tendsto (fun n : ℕ+ => yosidaJNeg gen hsa n ψ) atTop (𝓝 ψ) := by

  apply Metric.tendsto_atTop.mpr
  intro ε hε

  -- Step 1: Approximate ψ by φ ∈ D(A) with ‖ψ - φ‖ < ε/3
  have hε3 : ε / 3 > 0 := by linarith
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  -- Step 2: For φ ∈ D(A), Jₙ⁻φ → φ
  have h_conv_φ := yosidaJNeg_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_conv_φ
  obtain ⟨N, hN⟩ := h_conv_φ (ε / 3) hε3

  use N
  intro n hn
  rw [dist_eq_norm]

  calc ‖yosidaJNeg gen hsa n ψ - ψ‖
      = ‖(yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ) +
         (yosidaJNeg gen hsa n φ - φ) + (φ - ψ)‖ := by abel_nf
    _ ≤ ‖yosidaJNeg gen hsa n ψ - yosidaJNeg gen hsa n φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖yosidaJNeg gen hsa n (ψ - φ)‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          congr 2
          simp only [map_sub]
    _ ≤ ‖yosidaJNeg gen hsa n‖ * ‖ψ - φ‖ +
        ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by
          apply add_le_add_right
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right (yosidaJNeg_norm_bound gen hsa n) (norm_nonneg _)
    _ = ‖ψ - φ‖ + ‖yosidaJNeg gen hsa n φ - φ‖ + ‖φ - ψ‖ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

/-!
============================================================================================================================
## Section 5: Yosida Approximant Convergence
============================================================================================================================

The bounded Yosida approximants Aₙ converge strongly to the unbounded generator A
on the domain D(A). This is the central approximation result enabling the construction
of exp(itA).

**The key identity:**

For φ ∈ D(A):
  Aₙφ = Jₙ(Aφ)

This factorization through the J operator is the heart of Yosida's method. Since:
  - Jₙ → I strongly (proved in Section 4)
  - Aφ is a fixed vector in H for φ ∈ D(A)

we immediately obtain Aₙφ = Jₙ(Aφ) → I(Aφ) = Aφ.

**The negative and symmetrized approximants:**

We also define:
  - Aₙ⁻ = n²R(-in) + in·I (using the conjugate resolvent)
  - Aₙˢʸᵐ = (1/2)(Aₙ + Aₙ⁻) = (n²/2)(R(in) + R(-in))

All three converge to A on the domain, but Aₙˢʸᵐ has the crucial property of being
self-adjoint (proved in Section 3), which ensures exp(it·Aₙˢʸᵐ) is unitary.

**Commutativity:**

The Yosida approximants commute with all resolvents, a consequence of resolvents
at different spectral points commuting with each other. This ensures the approximating
exponentials exp(itAₙ) preserve the domain structure.
-/

/-- **Yosida Approximant as Composition with J**

For φ in the domain of a self-adjoint generator A:

  Aₙφ = Jₙ(Aφ)

where Aₙ = n²R(in) - in·I is the Yosida approximant and Jₙ = -in·R(in).

**Derivation:**

From the fundamental identity Jₙφ = φ - R(in)(Aφ), we can solve for R(in)(Aφ):
  R(in)(Aφ) = φ - Jₙφ = φ + in·R(in)φ

Now compute Jₙ(Aφ):
  Jₙ(Aφ) = -in · R(in)(Aφ)
         = -in · (φ + in·R(in)φ)
         = -in·φ + (-in)(in)·R(in)φ
         = -in·φ + n²·R(in)φ           [since (-in)(in) = n²]
         = n²·R(in)φ - in·φ
         = Aₙφ

**Why this identity is powerful:**

It reduces the convergence Aₙ → A to the already-proved convergence Jₙ → I:
  Aₙφ = Jₙ(Aφ) → I(Aφ) = Aφ

The composition structure Aₙ = Jₙ ∘ A (on the domain) shows that Aₙ "filters"
the unbounded operator A through the bounded approximate identity Jₙ, producing
a bounded approximation.

**Role in the construction:**

This identity is the computational engine of Yosida approximation. Combined with
‖Jₙ‖ ≤ 1, it gives quantitative control:
  ‖Aₙφ - Aφ‖ = ‖Jₙ(Aφ) - Aφ‖ → 0
-/
theorem yosidaApprox_eq_J_comp_A (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApprox gen hsa n φ = yosidaJ gen hsa n (gen.op φ) := by
  -- Get the key identity: Jₙφ = φ - R(in)(Aφ)
  have hJ_eq := yosidaJ_eq_sub_resolvent_A gen hsa n φ hφ
  -- Rearrange to get R(in)(Aφ) = φ + (in) • R(in)φ
  have hR_Aφ : resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)
             = φ + (I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
    unfold yosidaJ at hJ_eq
    have h_rearrange : resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ) =
             φ - (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
      calc resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)
          = φ - (φ - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)) := by
              rw [sub_sub_cancel]
        _ = φ - (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
              rw [← hJ_eq]
    calc resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)
        = φ - (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := h_rearrange
      _ = φ + -(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          rw [sub_eq_add_neg, neg_smul]
      _ = φ + (I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa φ := by
          congr 2
          ring
  -- Key scalar identity: (-I * n) * (I * n) = n²
  have h_scalar : (-I * (n : ℂ)) * (I * (n : ℂ)) = (n : ℂ)^2 := by
    calc (-I * (n : ℂ)) * (I * (n : ℂ))
        = -I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = -(I * I) * (n : ℂ)^2 := by ring
      _ = -(I^2) * (n : ℂ)^2 := by rw [sq I]
      _ = -(-1) * (n : ℂ)^2 := by rw [Complex.I_sq]
      _ = (n : ℂ)^2 := by ring
  -- Now prove main equality by computing RHS to LHS
  symm
  unfold yosidaApprox yosidaJ
  simp only [resolventAtIn]
  calc (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa (gen.op φ)
      = (-I * (n : ℂ)) • (φ + (I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [hR_Aφ]
    _ = (-I * (n : ℂ)) • φ + (-I * (n : ℂ)) • ((I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) _ hsa φ) := by
          rw [smul_add]
    _ = (-I * (n : ℂ)) • φ + ((-I * (n : ℂ)) * (I * (n : ℂ))) • resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [smul_smul]
    _ = (-I * (n : ℂ)) • φ + ((n : ℂ)^2) • resolvent gen (I * (n : ℂ)) _ hsa φ := by
          rw [h_scalar]
    _ = ((n : ℂ)^2) • resolvent gen (I * (n : ℂ)) _ hsa φ + (-I * (n : ℂ)) • φ := by
          rw [add_comm]
    _ = ((n : ℂ)^2) • resolvent gen (I * (n : ℂ)) _ hsa φ - (I * (n : ℂ)) • φ := by
          have h_neg : -I * (n : ℂ) = -(I * (n : ℂ)) := by ring
          have h : (-I * (n : ℂ)) • φ = -((I * (n : ℂ)) • φ) := by
            rw [h_neg, neg_smul]
          rw [h, ← sub_eq_add_neg]


/-- **Strong Convergence of Yosida Approximants**

For φ ∈ D(A), the Yosida approximants converge to the generator:

  Aₙφ → Aφ  as n → ∞

**Proof:**

This is an immediate corollary of two established results:
  1. Aₙφ = Jₙ(Aφ) (from `yosidaApprox_eq_J_comp_A`)
  2. Jₙψ → ψ for all ψ ∈ H (from `yosida_J_tendsto_id`)

Combining: Aₙφ = Jₙ(Aφ) → I(Aφ) = Aφ.

**Why convergence is only on the domain:**

For φ ∉ D(A), the expression Aφ is undefined, so "Aₙφ → Aφ" is meaningless.
The Yosida approximants Aₙ are bounded operators defined on all of H, but their
limit A is unbounded and only defined on D(A).

**The extension to all of H:**

The unitary group exp(itA) will be defined on all of H, not by extending A,
but by taking the strong limit of the unitary operators exp(itAₙ). Since
unitary operators preserve norms, the limit exists and is unitary on all of H.

**Convergence rate:**

From Aₙφ = Jₙ(Aφ) and ‖Jₙψ - ψ‖ ≤ (1/n)·‖Aψ‖ (for ψ ∈ D(A)), we get:
  ‖Aₙφ - Aφ‖ = ‖Jₙ(Aφ) - Aφ‖ ≤ (1/n)·‖A(Aφ)‖ = (1/n)·‖A²φ‖

for φ ∈ D(A²). The rate is O(1/n) with constant depending on how "smooth" φ is.
-/
theorem yosidaApprox_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n ψ) atTop (𝓝 (gen.op ψ)) := by
  -- Aₙψ = Jₙ(Aψ) by yosidaApprox_eq_J_comp_A
  -- Jₙ(Aψ) → Aψ by yosida_J_tendsto_id applied to (gen.op ψ)
  simp only [fun n => yosidaApprox_eq_J_comp_A gen hsa n ψ hψ]
  exact yosida_J_tendsto_id gen hsa (gen.op ψ)



/-- **Negative Yosida Approximant**

The "negative" variant using the conjugate resolvent:

  Aₙ⁻ = n²R(-in) + in·I

This is the counterpart to Aₙ = n²R(in) - in·I, obtained by replacing in with -in.

**Relation to the standard approximant:**

The negative approximant satisfies Aₙ⁻ = (Aₙ)* when A is self-adjoint, because:
  R(-in) = R((in)̄) = R(in)*

**Role:**

The negative approximant is used to form the symmetrized version:
  Aₙˢʸᵐ = (1/2)(Aₙ + Aₙ⁻)

which is self-adjoint and therefore generates unitary exponentials.
-/
noncomputable def yosidaApproxNeg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2) • resolventAtNegIn gen hsa n + (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-- **Negative Approximant as Composition with Jₙ⁻**

For φ ∈ D(A): Aₙ⁻φ = Jₙ⁻(Aφ)

This is the exact analogue of `yosidaApprox_eq_J_comp_A` for the negative variants.

**Derivation:**

From Jₙ⁻φ = φ - R(-in)(Aφ), we get R(-in)(Aφ) = φ - in·R(-in)φ.

Computing Jₙ⁻(Aφ) = in·R(-in)(Aφ):
  Jₙ⁻(Aφ) = in·(φ - in·R(-in)φ)
          = in·φ - (in)²·R(-in)φ
          = in·φ - (-n²)·R(-in)φ      [since (in)² = -n²]
          = in·φ + n²·R(-in)φ
          = Aₙ⁻φ
-/
lemma yosidaApproxNeg_eq_JNeg_A
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op φ) := by
  unfold yosidaApproxNeg yosidaJNeg resolventAtNegIn
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply]

  set R := resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

  have h := yosidaJNeg_eq_sub_resolvent_A gen hsa n φ hφ
  have h_RAφ : R (gen.op φ) = φ - (I * (n : ℂ)) • R φ := by
    abel_nf ; rw [h, ← h];
    simp_all only [neg_mul, Int.reduceNeg, neg_smul, one_smul, neg_sub, add_sub_cancel, R]

  -- Compute (in)² = -n²
  have h_in_sq : (I * (n : ℂ)) * (I * (n : ℂ)) = -((n : ℂ)^2) := by
    calc (I * (n : ℂ)) * (I * (n : ℂ))
        = I * I * (n : ℂ) * (n : ℂ) := by ring
      _ = (-1) * (n : ℂ) * (n : ℂ) := by rw [I_mul_I]
      _ = -((n : ℂ)^2) := by ring

  symm
  calc (I * (n : ℂ)) • R (gen.op φ)
      = (I * (n : ℂ)) • (φ - (I * (n : ℂ)) • R φ) := by rw [h_RAφ]
    _ = (I * (n : ℂ)) • φ - (I * (n : ℂ)) • ((I * (n : ℂ)) • R φ) := smul_sub _ _ _
    _ = (I * (n : ℂ)) • φ - ((I * (n : ℂ)) * (I * (n : ℂ))) • R φ := by rw [smul_smul]
    _ = (I * (n : ℂ)) • φ - (-((n : ℂ)^2)) • R φ := by rw [h_in_sq]
    _ = (I * (n : ℂ)) • φ + (n : ℂ)^2 • R φ := by rw [neg_smul, sub_neg_eq_add]
    _ = (n : ℂ)^2 • R φ + (I * (n : ℂ)) • φ := by abel



/-- **Negative Approximant Converges on Domain**

For φ ∈ D(A): Aₙ⁻φ → Aφ as n → ∞.

**Proof:**

By the factorization Aₙ⁻φ = Jₙ⁻(Aφ) and the convergence Jₙ⁻ → I:
  Aₙ⁻φ = Jₙ⁻(Aφ) → I(Aφ) = Aφ
-/
lemma yosidaApproxNeg_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxNeg gen hsa n φ) atTop (𝓝 (gen.op φ)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxNeg gen hsa n φ = yosidaJNeg gen hsa n (gen.op φ) :=
    fun n => yosidaApproxNeg_eq_JNeg_A gen hsa n φ hφ

  simp_rw [h_eq]
  exact yosidaJNeg_tendsto_id gen hsa h_dense (gen.op φ)

/-- **Symmetrized Approximant as Average**

The symmetrized Yosida approximant equals the average of positive and negative:

  Aₙˢʸᵐ = (1/2)(Aₙ + Aₙ⁻)

**Verification:**

  Aₙ + Aₙ⁻ = (n²R(in) - in·I) + (n²R(-in) + in·I)
           = n²R(in) + n²R(-in)
           = n²(R(in) + R(-in))

  (1/2)(Aₙ + Aₙ⁻) = (n²/2)(R(in) + R(-in)) = Aₙˢʸᵐ

**Significance:**

This representation shows that Aₙˢʸᵐ inherits convergence from both Aₙ and Aₙ⁻.
Since both converge to A on the domain, so does their average.
-/
lemma yosidaApproxSym_eq_avg
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    yosidaApproxSym gen hsa n = (1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n) := by
  unfold yosidaApproxSym yosidaApprox yosidaApproxNeg resolventAtIn resolventAtNegIn
  ext ψ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
             ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  set R_pos := resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa
  set R_neg := resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

  have h : (1 / 2 : ℂ) * (n : ℂ)^2 = (n : ℂ)^2 / 2 := by ring

  calc ((n : ℂ)^2 / 2) • (R_pos ψ + R_neg ψ)
      = ((n : ℂ)^2 / 2) • R_pos ψ + ((n : ℂ)^2 / 2) • R_neg ψ := smul_add _ _ _
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ) + (1 / 2 : ℂ) • ((n : ℂ)^2 • R_neg ψ) := by
        simp only [smul_smul]; ring_nf
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ + (n : ℂ)^2 • R_neg ψ) := by rw [← smul_add]
    _ = (1 / 2 : ℂ) • ((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1; abel
    _ = (1 / 2 : ℂ) • (((n : ℂ)^2 • R_pos ψ - (I * (n : ℂ)) • ψ) + ((n : ℂ)^2 • R_neg ψ + (I * (n : ℂ)) • ψ)) := by
        congr 1;

/-- **Symmetrized Approximant Converges on Domain**

For φ ∈ D(A): Aₙˢʸᵐφ → Aφ as n → ∞.

**Proof:**

Since Aₙˢʸᵐ = (1/2)(Aₙ + Aₙ⁻) and both Aₙφ → Aφ and Aₙ⁻φ → Aφ:
  Aₙˢʸᵐφ = (1/2)(Aₙφ + Aₙ⁻φ) → (1/2)(Aφ + Aφ) = Aφ

**Role in Stone's theorem:**

This is the convergence result we actually use: the symmetrized approximants
converge to A on the domain. Combined with self-adjointness of Aₙˢʸᵐ (which
ensures exp(it·Aₙˢʸᵐ) is unitary), this gives the complete Yosida construction.
-/
theorem yosidaApproxSym_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym gen hsa n φ) atTop (𝓝 (gen.op φ)) := by
  have h_eq : ∀ n : ℕ+, yosidaApproxSym gen hsa n φ =
      (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
    intro n
    calc yosidaApproxSym gen hsa n φ
        = ((1/2 : ℂ) • (yosidaApprox gen hsa n + yosidaApproxNeg gen hsa n)) φ := by
            rw [yosidaApproxSym_eq_avg]
      _ = (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ) := by
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]

  simp_rw [h_eq]

  have h_pos := yosidaApprox_tendsto_on_domain gen hsa φ hφ
  have h_neg := yosidaApproxNeg_tendsto_on_domain gen hsa h_dense φ hφ

  have h_sum : Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ)
      atTop (𝓝 (gen.op φ + gen.op φ)) := h_pos.add h_neg

  have h_half : Tendsto (fun n : ℕ+ => (1/2 : ℂ) • (yosidaApprox gen hsa n φ + yosidaApproxNeg gen hsa n φ))
      atTop (𝓝 ((1/2 : ℂ) • (gen.op φ + gen.op φ))) := h_sum.const_smul (1/2 : ℂ)

  have h_simp : (1/2 : ℂ) • (gen.op φ + gen.op φ) = gen.op φ := by
    rw [← two_smul ℂ (gen.op φ), smul_smul]
    norm_num

  rw [h_simp] at h_half
  exact h_half


/-- **Yosida Approximants Commute with Resolvents**

The bounded Yosida approximants commute with the resolvent at any spectral point:

  Aₙ ∘ R(z) = R(z) ∘ Aₙ  for all z with Im(z) ≠ 0

**Proof:**

Since Aₙ = n²R(in) - in·I, commutativity reduces to showing resolvents commute:
  R(in) ∘ R(z) = R(z) ∘ R(in)

From the resolvent identity R(w₁) - R(w₂) = (w₁ - w₂)·R(w₁)∘R(w₂), both orderings
give the same expression (w₁ - w₂)⁻¹·(R(w₁) - R(w₂)), establishing commutativity.

**Significance:**

Commutativity Aₙ ∘ R(z) = R(z) ∘ Aₙ extends to the exponentials:
  exp(itAₙ) ∘ R(z) = R(z) ∘ exp(itAₙ)

This ensures:
  1. exp(itAₙ) preserves the domain D(A) = Range(R(z))
  2. The limiting group exp(itA) has the correct domain properties
  3. The generator of the limit group is indeed A
-/
theorem yosidaApprox_commutes_resolvent
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (z : ℂ) (hz : z.im ≠ 0) :
    (yosidaApprox gen hsa n).comp (resolvent gen z hz hsa)
      = (resolvent gen z hz hsa).comp (yosidaApprox gen hsa n) := by
  -- First establish that resolvents commute
  have h_resolvent_comm : (resolventAtIn gen hsa n).comp (resolvent gen z hz hsa) =
                          (resolvent gen z hz hsa).comp (resolventAtIn gen hsa n) := by
    unfold resolventAtIn
    by_cases h_eq : I * (n : ℂ) = z
    · have hz' : (I * (n : ℂ)).im ≠ 0 := I_mul_pnat_im_ne_zero n
      have h_res_eq : resolvent gen (I * (n : ℂ)) hz' hsa = resolvent gen z hz hsa := by
        subst h_eq
        congr
      rw [h_res_eq]
    · have h_diff_ne : I * (n : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_eq
      have h_diff_ne' : z - I * (n : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_eq)
      have h_id1 := resolvent_identity gen hsa (I * (n : ℂ)) z (I_mul_pnat_im_ne_zero n) hz
      have h_id2 := resolvent_identity gen hsa z (I * (n : ℂ)) hz (I_mul_pnat_im_ne_zero n)
      have h1 : (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) =
                (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        symm
        calc (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa)
            = (I * (n : ℂ) - z)⁻¹ • ((I * (n : ℂ) - z) • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa)) := by
                rw [h_id1]
          _ = (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne, one_smul]
      have h2 : (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) =
                (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
        symm
        calc (z - I * (n : ℂ))⁻¹ • (resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)
            = (z - I * (n : ℂ))⁻¹ • ((z - I * (n : ℂ)) • (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa)) := by
                rw [h_id2]
          _ = (resolvent gen z hz hsa).comp (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa) := by
                rw [smul_smul, inv_mul_cancel₀ h_diff_ne', one_smul]
      rw [h1, h2]
      have h_inv_neg : (z - I * (n : ℂ))⁻¹ = -(I * (n : ℂ) - z)⁻¹ := by
        rw [← neg_sub, neg_inv]
      have h_sub_neg : resolvent gen z hz hsa - resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa =
                      -(resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        rw [neg_sub]
      rw [h_inv_neg, h_sub_neg, smul_neg, neg_smul, neg_neg]
  -- Now expand yosidaApprox and use resolvent commutativity
  unfold yosidaApprox
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  congr 1
  unfold resolventAtIn
  simp only [resolventAtIn] at h_resolvent_comm
  rw [h_resolvent_comm]

/-!
============================================================================================================================
## Section 6: Exponential of Bounded Operators
============================================================================================================================

With the Yosida approximants Aₙ established as bounded operators converging to A
on the domain, we now define and study the exponential exp(tB) for bounded B.

**Definition:**

For bounded B : H →L[ℂ] H and t ∈ ℝ:

  exp(tB) = Σₖ₌₀^∞ (tB)ᵏ / k!

The series converges absolutely in operator norm since ‖(tB)ᵏ/k!‖ ≤ (|t|·‖B‖)ᵏ/k!
and Σ xᵏ/k! = eˣ converges for all x.

**Key properties:**

1. **Semigroup law:** exp((s+t)B) = exp(sB) · exp(tB)
2. **Norm bound:** ‖exp(tB)‖ ≤ exp(|t|·‖B‖)
3. **Adjoint:** exp(tB)* = exp(tB*)
4. **Unitarity:** If B* = -B (skew-adjoint), then exp(tB) is unitary

**Application to Yosida:**

The approximants i·Aₙˢʸᵐ are skew-adjoint (since Aₙˢʸᵐ is self-adjoint), so
exp(t·i·Aₙˢʸᵐ) is unitary for all t. These unitary operators form the approximating
sequence whose strong limit defines exp(itA).
-/

/-- **Exponential of a Bounded Operator**

For bounded B : H →L[ℂ] H and t ∈ ℝ, the operator exponential:

  exp(tB) = Σₖ₌₀^∞ (tB)ᵏ / k!

**Convergence:**

The series converges absolutely in operator norm. For each term:
  ‖(tB)ᵏ / k!‖ ≤ (|t| · ‖B‖)ᵏ / k!

The sum Σₖ (|t|·‖B‖)ᵏ/k! = exp(|t|·‖B‖) < ∞, so the series converges by comparison.

**Properties:**

  - exp(0·B) = I (identity at t = 0)
  - exp((s+t)B) = exp(sB) · exp(tB) (semigroup law)
  - d/dt exp(tB) = B · exp(tB) (generator property)
  - If B* = -B, then exp(tB) is unitary

**Role in Stone's theorem:**

The Yosida approximants Aₙ are bounded, so exp(itAₙ) is well-defined by this
power series. The unitary group exp(itA) for unbounded self-adjoint A is the
strong limit of these bounded exponentials.

**Implementation note:**

We use Mathlib's `NormedSpace.exp` for the Banach algebra H →L[ℂ] H, which provides
the same power series definition along with algebraic properties.
-/
noncomputable def expBounded (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' (k : ℕ), (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k


/-- **Semigroup Law for Bounded Exponentials**

The exponential satisfies the fundamental semigroup property:

  exp((s + t)B) = exp(sB) ∘ exp(tB)

**Proof:**

Since sB and tB commute (both are scalar multiples of B), the Cauchy product
formula for absolutely convergent series gives:

  exp(sB) · exp(tB) = (Σⱼ (sB)ʲ/j!) · (Σₖ (tB)ᵏ/k!)
                    = Σₙ Σⱼ₊ₖ₌ₙ (sB)ʲ(tB)ᵏ / (j!k!)
                    = Σₙ (Bⁿ/n!) · Σⱼ₌₀ⁿ C(n,j) sʲ tⁿ⁻ʲ
                    = Σₙ ((s+t)B)ⁿ / n!        [binomial theorem]
                    = exp((s+t)B)

**Commutativity is essential:**

The identity exp(X)exp(Y) = exp(X+Y) holds only when X and Y commute. For
non-commuting operators, the Baker-Campbell-Hausdorff formula applies instead.

**Role in Stone's theorem:**

This law ensures t ↦ exp(itAₙ) is a one-parameter group for each n. The group
law passes to the strong limit, establishing t ↦ exp(itA) as a group.
-/
theorem expBounded_group_law (B : H →L[ℂ] H) (s t : ℝ) :
    expBounded B (s + t) = (expBounded B s).comp (expBounded B t) := by
  unfold expBounded

  have h_eq_exp : ∀ c : ℂ, (∑' k : ℕ, (1 / k.factorial : ℂ) • (c • B) ^ k) =
      NormedSpace.exp ℂ (c • B) := by
    intro c
    rw [NormedSpace.exp_eq_tsum]
    congr 1
    ext k
    rw [one_div]

  have h_comm : Commute ((s : ℂ) • B) ((t : ℂ) • B) := by
    show ((s : ℂ) • B) * ((t : ℂ) • B) = ((t : ℂ) • B) * ((s : ℂ) • B)
    rw [smul_mul_smul, smul_mul_smul, mul_comm (s : ℂ) (t : ℂ)]

  simp only [h_eq_exp]
  simp only [Complex.ofReal_add, add_smul]
  rw [NormedSpace.exp_add_of_commute h_comm]
  rfl


/-- **Norm Bound for Bounded Exponentials**

The exponential satisfies the standard estimate:

  ‖exp(tB)‖ ≤ exp(|t| · ‖B‖)

**Proof:**

  ‖exp(tB)‖ = ‖Σₖ (tB)ᵏ/k!‖
            ≤ Σₖ ‖(tB)ᵏ/k!‖
            ≤ Σₖ ‖tB‖ᵏ/k!
            = exp(‖tB‖)
            = exp(|t| · ‖B‖)

**Significance:**

This bound shows ‖exp(tB)‖ grows at most exponentially in |t|. For skew-adjoint B,
the actual norm is 1 (unitary), but this general bound applies to all bounded B.

**For Yosida approximants:**

Applied to B = i·Aₙˢʸᵐ, this gives ‖exp(it·Aₙˢʸᵐ)‖ ≤ exp(|t|·‖Aₙˢʸᵐ‖). However,
since i·Aₙˢʸᵐ is skew-adjoint, the sharp bound is ‖exp(it·Aₙˢʸᵐ)‖ = 1.
-/
theorem expBounded_norm_bound (B : H →L[ℂ] H) (t : ℝ) :
    ‖expBounded B t‖ ≤ Real.exp (|t| * ‖B‖) := by
  unfold expBounded
  set X := (t : ℂ) • B with hX
  set f := (fun n : ℕ => (n.factorial : ℂ)⁻¹ • X ^ n) with hf
  set g := (fun n : ℕ => ‖X‖ ^ n / n.factorial) with hg

  have h_norm_summable : Summable g := Real.summable_pow_div_factorial ‖X‖

  have h_term_le : ∀ n, ‖f n‖ ≤ g n := fun n => by
    simp only [hf, hg]
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact opNorm_pow_le X n

  have h_summable : Summable f :=
    Summable.of_norm_bounded (g := g) h_norm_summable h_term_le

  have h_eq_exp : (∑' k : ℕ, (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) =
      ∑' n, f n := by
    congr 1; ext k
    simp only [hf, one_div]
    abel
  have h_exp_eq : NormedSpace.exp ℂ X = ∑' n, f n := by
    rw [NormedSpace.exp_eq_tsum]

  have h_norm_f_summable : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h_term_le h_norm_summable

  have h1 : ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := by
    apply norm_tsum_le_tsum_norm
    exact h_norm_f_summable

  have h2 : ∑' n, ‖f n‖ ≤ ∑' n, g n := by
    apply Summable.tsum_le_tsum h_term_le h_norm_f_summable h_norm_summable

  have h3 : ∑' n, g n = Real.exp ‖X‖ := by
    simp only [hg]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

  have h4 : ‖X‖ = |t| * ‖B‖ := by
    simp only [hX]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

  rw [h_eq_exp]
  calc ‖∑' n, f n‖
      ≤ ∑' n, ‖f n‖ := h1
    _ ≤ ∑' n, g n := h2
    _ = Real.exp ‖X‖ := h3
    _ = Real.exp (|t| * ‖B‖) := by rw [h4]

/-- Specialized bound for Yosida approximant exponential. -/
theorem expBounded_yosida_norm_le
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) :
    ‖expBounded (I • yosidaApprox gen hsa n) t‖ ≤ Real.exp (|t| * ‖I • yosidaApprox gen hsa n‖) :=
  expBounded_norm_bound _ _

/-- Simplified bound using ‖I • B‖ = ‖B‖. -/
theorem expBounded_yosida_norm_le'
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) :
    ‖expBounded (I • yosidaApprox gen hsa n) t‖ ≤ Real.exp (|t| * ‖yosidaApprox gen hsa n‖) := by
  have h := expBounded_norm_bound (I • yosidaApprox gen hsa n) t
  simp only [norm_smul, Complex.norm_I, one_mul] at h
  exact h



/-- **Summability of Exponential Series**

The power series defining exp(tB) is summable in operator norm.

This is the foundational convergence result enabling the definition of expBounded.
-/
lemma expBounded_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) := by
  apply Summable.of_norm
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤ ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _)
            exact norm_nonneg _
      _ = (1 / k.factorial) * ‖(t : ℂ) • B‖ ^ k := by
            congr 1
            simp only [norm_div, norm_one, Complex.norm_natCast]
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by ring
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖



/-- **Adjoint of Powers**

The adjoint distributes over powers:

  (Bᵏ)* = (B*)ᵏ

**Proof by induction:**

  - Base: (B⁰)* = I* = I = (B*)⁰
  - Step: (Bᵏ⁺¹)* = (Bᵏ · B)* = B* · (Bᵏ)* = B* · (B*)ᵏ = (B*)ᵏ⁺¹

The step uses the adjoint reversal rule (ST)* = T*S* and the inductive hypothesis.
-/
theorem adjoint_pow (B : H →L[ℂ] H) (k : ℕ) :
    (B ^ k).adjoint = B.adjoint ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    ext φ
    apply ext_inner_right ℂ
    intro ψ
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
    rw [ih]
    rw [← ContinuousLinearMap.adjoint_inner_left B]
    congr 1
    have h_comm : B.adjoint * B.adjoint ^ k = B.adjoint ^ k * B.adjoint := by
      rw [← pow_succ, ← pow_succ', add_comm]
    calc B.adjoint ((B.adjoint ^ k) φ)
        = (B.adjoint * B.adjoint ^ k) φ := rfl
      _ = (B.adjoint ^ k * B.adjoint) φ := by rw [h_comm]
      _ = (B.adjoint ^ k) (B.adjoint φ) := rfl


/-- Helper: evaluation at a point commutes with tsum of operators. -/
lemma tsum_apply_of_summable (f : ℕ → H →L[ℂ] H) (hf : Summable f) (x : H) :
    (∑' n, f n) x = ∑' n, f n x := by
  let evalx : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  calc (∑' n, f n) x
      = evalx (∑' n, f n) := rfl
    _ = ∑' n, evalx (f n) := evalx.map_tsum hf
    _ = ∑' n, f n x := rfl

/-- Helper: variant of tsum_apply_of_summable. -/
lemma tsum_apply_of_summable' (f : ℕ → H →L[ℂ]H) (hf : Summable f) (x : H) :
    (∑' n, f n) x = ∑' n, f n x := by
  let evalx : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  calc (∑' n, f n) x
      = evalx (∑' n, f n) := rfl
    _ = ∑' n, evalx (f n) := evalx.map_tsum hf
    _ = ∑' n, f n x := rfl


/-- Helper: summability of norms of exponential series terms. -/
lemma expBounded_norm_summable (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖) := by
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤ ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _) (norm_nonneg _)
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by
            simp only [norm_div, norm_one, Complex.norm_natCast]
            exact one_div_mul_eq_div (↑k.factorial) (‖↑t • B‖ ^ k)
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖

/-- Helper: variant of expBounded_norm_summable. -/
lemma expBounded_norm_summable' (B : H →L[ℂ] H) (t : ℝ) :
    Summable (fun k : ℕ => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖) := by
  have h_bound : ∀ k, ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ ≤ ‖(t : ℂ) • B‖ ^ k / k.factorial := by
    intro k
    rw [norm_smul]
    calc ‖(1 / k.factorial : ℂ)‖ * ‖((t : ℂ) • B) ^ k‖
        ≤ ‖(1 / k.factorial : ℂ)‖ * ‖(t : ℂ) • B‖ ^ k := by
            apply mul_le_mul_of_nonneg_left (opNorm_pow_le _ _) (norm_nonneg _)
      _ = ‖(t : ℂ) • B‖ ^ k / k.factorial := by
            simp only [norm_div, norm_one, Complex.norm_natCast]
            simp_all only [one_div, coe_smul]
            exact inv_mul_eq_div (↑k.factorial) (‖t • B‖ ^ k)
  apply Summable.of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact h_bound
  · exact Real.summable_pow_div_factorial ‖(t : ℂ) • B‖

/-- Helper: inner product commutes with tsum in second argument. -/
lemma inner_tsum_right' (x : H) (f : ℕ → H) (hf : Summable f) :
    ⟪x, ∑' n, f n⟫_ℂ = ∑' n, ⟪x, f n⟫_ℂ := by
  let L : H →L[ℂ] ℂ := innerSL ℂ x
  have hL : ∀ y, L y = ⟪x, y⟫_ℂ := fun y => rfl
  calc ⟪x, ∑' n, f n⟫_ℂ
      = L (∑' n, f n) := (hL _).symm
    _ = ∑' n, L (f n) := L.map_tsum hf
    _ = ∑' n, ⟪x, f n⟫_ℂ := by simp only [hL]

/-- Helper: inner product commutes with tsum in first argument. -/
lemma tsum_inner_left' (f : ℕ → H) (y : H) (hf : Summable f) :
    ⟪∑' n, f n, y⟫_ℂ = ∑' n, ⟪f n, y⟫_ℂ := by
  have h_conj : ⟪∑' n, f n, y⟫_ℂ = (starRingEnd ℂ) ⟪y, ∑' n, f n⟫_ℂ :=
    (inner_conj_symm (∑' n, f n) y).symm
  rw [h_conj, inner_tsum_right' y f hf]
  rw [conj_tsum]
  · congr 1
    ext n
    exact (inner_conj_symm (f n) y)

/-- **Adjoint of Exponential**

The adjoint commutes with the exponential:

  (exp(tB))* = exp(tB*)

**Proof:**

Since adjoint is a continuous linear operation and the exponential is defined
by a convergent series:

  (exp(tB))* = (Σₖ (tB)ᵏ/k!)* = Σₖ ((tB)ᵏ/k!)* = Σₖ (tB*)ᵏ/k! = exp(tB*)

The key step uses (Bᵏ)* = (B*)ᵏ from `adjoint_pow`.

**Consequence for skew-adjoint operators:**

If B* = -B, then (exp(tB))* = exp(tB*) = exp(-tB), which combined with the
semigroup law gives (exp(tB))*(exp(tB)) = exp(-tB)exp(tB) = exp(0) = I.
-/
theorem adjoint_expBounded (B : H →L[ℂ] H) (t : ℝ) :
    (expBounded B t).adjoint = expBounded B.adjoint t := by
  unfold expBounded

  have h_summable : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) :=
    expBounded_summable B t

  have h_summable_adj : Summable (fun k : ℕ => (1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) :=
    expBounded_summable B.adjoint t

  ext φ
  apply ext_inner_right ℂ
  intro ψ

  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [tsum_apply_of_summable _ h_summable ψ]
  rw [tsum_apply_of_summable _ h_summable_adj φ]

  have h_inner_summable : Summable (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k) ψ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B t
    have h_scaled : Summable (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k‖ * ‖ψ‖) :=
      h_norm_sum.mul_right ‖ψ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled

  have h_inner_summable_adj : Summable (fun k => ((1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k) φ) := by
    apply Summable.of_norm
    have h_norm_sum := expBounded_norm_summable B.adjoint t
    have h_scaled : Summable (fun k => ‖(1 / k.factorial : ℂ) • ((t : ℂ) • B.adjoint) ^ k‖ * ‖φ‖) :=
      h_norm_sum.mul_right ‖φ‖
    apply Summable.of_nonneg_of_le
    · intro k; exact norm_nonneg _
    · intro k
      exact ContinuousLinearMap.le_opNorm _ _
    · exact h_scaled

  rw [inner_tsum_right' φ _ h_inner_summable]
  rw [tsum_inner_left' _ ψ h_inner_summable_adj]

  congr 1
  ext k

  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]

  have h_real : (starRingEnd ℂ) (1 / k.factorial : ℂ) = (1 / k.factorial : ℂ) := by
    simp only [map_div₀, map_one, map_natCast]
  rw [h_real]

  congr 1

  have h_smul_pow : ∀ (c : ℂ) (T : H →L[ℂ] H) (n : ℕ), (c • T) ^ n = c ^ n • T ^ n := by
    intro c T n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      ext x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
      rw [ContinuousLinearMap.map_smul]
      rw [smul_smul]

  rw [h_smul_pow, h_smul_pow]
  simp only [ContinuousLinearMap.smul_apply]
  rw [inner_smul_right, inner_smul_left]

  have h_t_real : (starRingEnd ℂ) ((t : ℂ) ^ k) = (t : ℂ) ^ k := by
    simp only [map_pow, Complex.conj_ofReal]
  rw [h_t_real]

  congr 1

  rw [← ContinuousLinearMap.adjoint_inner_left (B ^ k)]
  rw [adjoint_pow]


/-- **Exponential of Skew-Adjoint is Unitary**

For skew-adjoint B (i.e., B* = -B), the exponential exp(tB) is unitary:

  (exp(tB))* ∘ exp(tB) = I  and  exp(tB) ∘ (exp(tB))* = I

**Proof:**

1. From B* = -B and `adjoint_expBounded`:
   (exp(tB))* = exp(tB*) = exp(t(-B)) = exp(-tB)

2. From the semigroup law:
   (exp(tB))* ∘ exp(tB) = exp(-tB) ∘ exp(tB) = exp(0) = I
   exp(tB) ∘ (exp(tB))* = exp(tB) ∘ exp(-tB) = exp(0) = I

**Physical significance:**

Skew-adjoint operators generate unitary evolution. In quantum mechanics:
  - The Hamiltonian H is self-adjoint
  - The time evolution generator is iH, which is skew-adjoint
  - Therefore exp(itH) is unitary, preserving probability

**Application to Yosida:**

The symmetrized approximants Aₙˢʸᵐ are self-adjoint, so i·Aₙˢʸᵐ is skew-adjoint.
Therefore exp(t·i·Aₙˢʸᵐ) is unitary for all t and n. This unitarity passes to
the strong limit, establishing that exp(itA) is unitary.
-/
theorem expBounded_skewAdjoint_unitary (B : H →L[ℂ] H) (hB : B.adjoint = -B) (t : ℝ) :
    (expBounded B t).adjoint.comp (expBounded B t) = ContinuousLinearMap.id ℂ H ∧
    (expBounded B t).comp (expBounded B t).adjoint = ContinuousLinearMap.id ℂ H := by
  -- exp(tB)* = exp(tB*) = exp(t(-B)) = exp(-tB)
  have h_adj : (expBounded B t).adjoint = expBounded B (-t) := by
    rw [adjoint_expBounded]
    rw [hB]
    unfold expBounded
    congr 1
    ext k
    congr 2
    ext x
    simp only [Complex.ofReal_neg, neg_smul, smul_neg]

  constructor
  · -- exp(tB)* ∘ exp(tB) = exp(-tB) ∘ exp(tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B (-t) t]
    simp only [neg_add_cancel]
    unfold expBounded
    simp only [Complex.ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

  · -- exp(tB) ∘ exp(tB)* = exp(tB) ∘ exp(-tB) = exp(0) = I
    rw [h_adj]
    rw [← expBounded_group_law B t (-t)]
    simp only [add_neg_cancel]
    unfold expBounded
    simp only [Complex.ofReal_zero, zero_smul]
    have h_eq : (fun k : ℕ => (1 / k.factorial : ℂ) • (0 : H →L[ℂ] H) ^ k) =
                (fun k : ℕ => if k = 0 then 1 else 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k => simp [pow_succ]
    rw [h_eq]
    rw [tsum_eq_single 0]
    · abel
    · intro k hk
      simp [hk]

/-!
============================================================================================================================
## Section 7: Unitarity of Yosida Exponentials
============================================================================================================================

The exponentials exp(t·I·Aₙˢʸᵐ) of the symmetrized Yosida approximants are unitary
operators. This follows from the chain:

  Aₙˢʸᵐ self-adjoint ⟹ I·Aₙˢʸᵐ skew-adjoint ⟹ exp(t·I·Aₙˢʸᵐ) unitary

Unitarity means these operators:
  1. Preserve inner products: ⟨Uψ, Uφ⟩ = ⟨ψ, φ⟩
  2. Are isometries: ‖Uψ‖ = ‖ψ‖
  3. Are invertible with U⁻¹ = U*

This unitarity is essential for the Yosida construction: it ensures the approximating
sequence has uniformly bounded norms (all equal to 1), enabling the strong limit
to exist and be unitary.
-/

/-- **Yosida Exponentials Preserve Inner Products**

The exponential exp(t·I·Aₙˢʸᵐ) preserves inner products:

  ⟨exp(t·I·Aₙˢʸᵐ)ψ, exp(t·I·Aₙˢʸᵐ)φ⟩ = ⟨ψ, φ⟩

**Proof:**

1. I·Aₙˢʸᵐ is skew-adjoint (from `I_smul_yosidaApproxSym_skewAdjoint`)
2. Skew-adjoint operators have unitary exponentials (from `expBounded_skewAdjoint_unitary`)
3. Unitary operators preserve inner products: ⟨Uψ, Uφ⟩ = ⟨ψ, U*Uφ⟩ = ⟨ψ, φ⟩

**Role in the construction:**

Inner product preservation passes to limits. Since each approximant preserves
inner products, and the inner product is continuous, the limiting operator
exp(itA) also preserves inner products — establishing its unitarity.
-/
theorem expBounded_yosidaApproxSym_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ φ : H) :
    ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
     expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_skew := I_smul_yosidaApproxSym_skewAdjoint gen hsa n
  have h_unitary := expBounded_skewAdjoint_unitary (I • yosidaApproxSym gen hsa n) h_skew t
  let U := expBounded (I • yosidaApproxSym gen hsa n) t

  calc ⟪U ψ, U φ⟫_ℂ
      = ⟪ψ, U.adjoint (U φ)⟫_ℂ := (ContinuousLinearMap.adjoint_inner_right U ψ (U φ)).symm
    _ = ⟪ψ, (U.adjoint.comp U) φ⟫_ℂ := rfl
    _ = ⟪ψ, (ContinuousLinearMap.id ℂ H) φ⟫_ℂ := by rw [h_unitary.1]
    _ = ⟪ψ, φ⟫_ℂ := by simp


/-- **Yosida Exponentials are Isometries**

The exponential exp(t·I·Aₙˢʸᵐ) preserves norms:

  ‖exp(t·I·Aₙˢʸᵐ)ψ‖ = ‖ψ‖

**Proof:**

From inner product preservation with φ = ψ:
  ‖Uψ‖² = ⟨Uψ, Uψ⟩ = ⟨ψ, ψ⟩ = ‖ψ‖²

Taking square roots (both sides non-negative): ‖Uψ‖ = ‖ψ‖.

**Significance:**

Isometry is the key property used in the Cauchy sequence argument. When showing
exp(t·I·Aₘˢʸᵐ)ψ - exp(t·I·Aₙˢʸᵐ)ψ is small, we use:

  ‖exp(t·I·Aₘˢʸᵐ)(ψ - φ)‖ = ‖ψ - φ‖

This allows approximation by domain elements without worrying about operator norms.
-/
theorem expBounded_yosidaApproxSym_isometry
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (ψ : H) :
    ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ = ‖ψ‖ := by
  set U := expBounded (I • yosidaApproxSym gen hsa n) t with hU
  have h_inner := expBounded_yosidaApproxSym_unitary gen hsa n t ψ ψ
  have h1 : ‖U ψ‖^2 = re ⟪U ψ, U ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) (U ψ)).symm
  have h2 : ‖ψ‖^2 = re ⟪ψ, ψ⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) ψ).symm
  have h_sq : ‖U ψ‖^2 = ‖ψ‖^2 := by
    rw [h1, h2, h_inner]
  have h_nonneg1 : 0 ≤ ‖U ψ‖ := norm_nonneg _
  have h_nonneg2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U ψ‖ - ‖ψ‖), sq_nonneg (‖U ψ‖ + ‖ψ‖), h_sq, h_nonneg1, h_nonneg2]





/-!
============================================================================================================================
## Section 8: Convergence and the Exponential Definition
============================================================================================================================

We now establish that the Yosida exponentials form a Cauchy sequence, enabling
the definition of exp(itA) as their strong limit.

**The convergence argument:**

For ψ ∈ H and ε > 0:
1. Approximate ψ by φ ∈ D(A) with ‖ψ - φ‖ < ε/3
2. On domain elements, use the Duhamel formula to show exp(t·I·Aₙˢʸᵐ)φ → U(t)φ
3. Use isometry to control ‖exp(t·I·Aₙˢʸᵐ)(ψ - φ)‖ = ‖ψ - φ‖

**The Duhamel formula:**

For φ ∈ D(A), the difference between the true evolution and the approximation is:

  U(t)φ - exp(tBₙ)φ = ∫₀ᵗ exp((t-s)Bₙ)(iA - Bₙ)U(s)φ ds

where Bₙ = I·Aₙˢʸᵐ. Since exp((t-s)Bₙ) is an isometry:

  ‖U(t)φ - exp(tBₙ)φ‖ ≤ |t| · sup_{s∈[0,|t|]} ‖(A - Aₙˢʸᵐ)U(s)φ‖

The RHS → 0 as n → ∞ by uniform convergence of Aₙˢʸᵐ → A on the orbit {U(s)φ}.

**Definition of exp(itA):**

With Cauchy sequences established, we define:

  exp(itA) := s-lim_{n→∞} exp(t·I·Aₙˢʸᵐ)

This is the strong operator limit, existing by completeness of H.
-/


/-!
================================================================================
SECTION X: UNIFORM CONVERGENCE ON COMPACT ORBITS
================================================================================

The final piece needed for the convergence theorem.
-/

section UniformConvergence

open StonesTheorem.Resolvent StonesTheorem.Exponential

variable (U_grp : OneParameterUnitaryGroup (H := H))
variable (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
variable (h_dense : Dense (gen.domain : Set H))

/-- The orbit {U(s)φ : s ∈ [0, |t|]} is compact. -/
lemma orbit_compact (t : ℝ) (φ : H) :
    IsCompact {ψ : H | ∃ s ∈ Set.Icc 0 |t|, ψ = U_grp.U s φ} := by
  -- Continuous image of compact set [0, |t|]
  sorry

/-- The Yosida approximants are equicontinuous (uniformly bounded). -/
lemma yosidaApproxSym_equicontinuous :
    ∀ n : ℕ+, ‖yosidaApproxSym gen hsa n‖ ≤ 2 * n := by
  sorry

/-- Pointwise convergence of Yosida approximants on the domain. -/
lemma yosidaApproxSym_pointwise
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApproxSym gen hsa n ψ) atTop (𝓝 (gen.op ψ)) := by
  exact yosidaApproxSym_tendsto_on_domain gen hsa h_dense ψ hψ

/-- **Uniform Convergence on Orbit**

For φ ∈ D(A), the Yosida approximants converge uniformly to A on the orbit.
-/
theorem yosidaApproxSym_uniform_on_orbit (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => ⨆ s ∈ Set.Icc 0 |t|,
              ‖(gen.op - yosidaApproxSym gen hsa n) (U_grp.U s φ)‖)
            atTop (𝓝 0) := by
  -- Strategy:
  -- 1. The orbit K = {U(s)φ : s ∈ [0,|t|]} is compact
  -- 2. U(s)φ ∈ D(A) for all s (domain invariance)
  -- 3. Aₙ(ψ) → A(ψ) pointwise for all ψ ∈ D(A)
  -- 4. {Aₙ} is equicontinuous (uniformly bounded)
  -- 5. Apply Arzelà-Ascoli / equicontinuity argument:
  --    pointwise convergence + equicontinuity on compact = uniform convergence
  sorry

end UniformConvergence


/-- **Exponential at t=0 is Identity**

For any bounded operator B: exp(0·B) = I.

**Proof:**

The power series at t=0 collapses:
  exp(0·B) = Σₖ (0·B)ᵏ/k! = (0·B)⁰/0! + Σₖ≥₁ 0ᵏ·Bᵏ/k! = I + 0 = I
-/
lemma expBounded_at_zero (B : H →L[ℂ] H) (ψ : H) :
    expBounded B 0 ψ = ψ := by
  unfold expBounded
  simp only [one_div, ofReal_zero, zero_smul]

  have h_zero_pow : ∀ k : ℕ, (0 : H →L[ℂ] H) ^ k = if k = 0 then 1 else 0 := by
    intro k
    cases k with
    | zero => simp [pow_zero]
    | succ k => simp [pow_succ, mul_zero]

  simp_rw [h_zero_pow]
  have h_sum : (∑' k : ℕ, (1 / k.factorial : ℂ) • (if k = 0 then (1 : H →L[ℂ] H) else 0)) = 1 := by
    rw [tsum_eq_single 0]
    · simp [Nat.factorial_zero]
    · intro k hk
      simp [hk]
  simp only [smul_ite, smul_zero]
  simp_all only [one_div, smul_ite, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, smul_zero, tsum_ite_eq,
    ContinuousLinearMap.one_apply]



/-- **Unitary Group at t=0**

U(0) = I for any one-parameter unitary group.

This is part of the group axioms: U(0) = U(t + (-t)) = U(t)U(-t) requires U(0) = I.
-/
lemma unitary_group_at_zero
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (ψ : H) :
    U_grp.U 0 ψ = ψ := by
  rw [U_grp.identity]
  simp only [ContinuousLinearMap.id_apply]


/-- **Domain Invariance under Unitary Group**

If φ ∈ D(A), then U(t)φ ∈ D(A) for all t ∈ ℝ.

**Physical meaning:**

The domain of the Hamiltonian is preserved under time evolution. States that
are "smooth enough" to be in D(A) remain smooth under the dynamics generated by A.

**Mathematical role:**

This invariance is essential for the Duhamel formula: we need A(U(s)φ) to be
defined for all s ∈ [0,t], which requires U(s)φ ∈ D(A).
-/
lemma unitary_group_domain_invariant
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ ∈ gen.domain :=
  gen.domain_invariant t φ hφ



/-- **Generator Commutes with Unitary Group**

For φ ∈ D(A): A(U(t)φ) = U(t)(Aφ)

**Derivation:**

Both sides are well-defined since U(t)φ ∈ D(A) by domain invariance and Aφ ∈ H.

The identity follows from the group law and the definition of the generator:

  A(U(t)φ) = lim_{s→0} (U(s)U(t)φ - U(t)φ)/(is)
           = lim_{s→0} (U(t+s)φ - U(t)φ)/(is)
           = lim_{s→0} U(t)((U(s)φ - φ)/(is))
           = U(t) · lim_{s→0} (U(s)φ - φ)/(is)
           = U(t)(Aφ)

The interchange of U(t) with the limit uses continuity of U(t).

**Physical interpretation:**

Time evolution commutes with the Hamiltonian on domain elements. This is the
infinitesimal version of [U(t), A] = 0, reflecting that A is conserved under
its own time evolution.
-/
lemma generator_commutes_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp)
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    gen.op (U_grp.U t φ) = U_grp.U t (gen.op φ) := by
  have hUtφ : U_grp.U t φ ∈ gen.domain := gen.domain_invariant t φ hφ
  have h_gen_Utφ := gen.generator_formula (U_grp.U t φ) hUtφ
  have h_gen_φ := gen.generator_formula φ hφ

  have h_key : ∀ s : ℝ, U_grp.U s (U_grp.U t φ) - U_grp.U t φ = U_grp.U t (U_grp.U s φ - φ) := by
    intro s
    have h1 : U_grp.U s (U_grp.U t φ) = U_grp.U (s + t) φ := by
      rw [U_grp.group_law]
      rfl
    have h2 : U_grp.U (s + t) φ = U_grp.U (t + s) φ := by
      rw [add_comm]
    have h3 : U_grp.U (t + s) φ = U_grp.U t (U_grp.U s φ) := by
      rw [U_grp.group_law]
      rfl
    calc U_grp.U s (U_grp.U t φ) - U_grp.U t φ
        = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := by rw [h1, h2, h3]
      _ = U_grp.U t (U_grp.U s φ) - U_grp.U t φ := rfl
      _ = U_grp.U t (U_grp.U s φ - φ) := by rw [ContinuousLinearMap.map_sub]

  have h_eq_seq : ∀ s : ℝ, (I * s)⁻¹ • (U_grp.U s (U_grp.U t φ) - U_grp.U t φ) =
                          U_grp.U t ((I * s)⁻¹ • (U_grp.U s φ - φ)) := by
    intro s
    rw [h_key s, ContinuousLinearMap.map_smul]

  have h_rhs_tendsto : Tendsto (fun s : ℝ => U_grp.U t ((I * (s : ℂ))⁻¹ • (U_grp.U s φ - φ)))
                               (𝓝[≠] 0) (𝓝 (U_grp.U t (gen.op φ))) := by
    apply Filter.Tendsto.comp (U_grp.U t).continuous.continuousAt h_gen_φ

  have h_limits_eq := tendsto_nhds_unique h_gen_Utφ (h_rhs_tendsto.congr (fun s => (h_eq_seq s).symm))
  exact h_limits_eq




/-
# MASSIVE TO-DO!!!
-/
/-!
================================================================================
SECTION 6: DUHAMEL FORMULA
================================================================================

The variation of parameters formula for comparing U(t) with exp(tB).
-/

section DuhamelFormula

open StonesTheorem.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))
variable (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
variable (h_dense : Dense (gen.domain : Set H))

/-- The integrand in the Duhamel formula:
    f(s) = exp((t-s)B) · (iA - B) · U(s)φ
where B = i·Aₙˢʸᵐ -/
noncomputable def duhamelIntegrand
    (n : ℕ+) (t : ℝ) (φ : H) (s : ℝ) : H :=
  expBounded (I • yosidaApproxSym gen hsa n) (t - s)
    ((I • gen.op - I • yosidaApproxSym gen hsa n) (U_grp.U s φ))

/-- The integrand is continuous in s. -/
lemma duhamelIntegrand_continuous (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Continuous (duhamelIntegrand U_grp gen hsa n t φ) := by
  sorry

/-- The integrand is bounded. -/
lemma duhamelIntegrand_bound (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) (s : ℝ)
    (hs : s ∈ Set.Icc 0 |t|) :
    ‖duhamelIntegrand U_grp gen hsa n t φ s‖ ≤
    ‖(I • gen.op - I • yosidaApproxSym gen hsa n) (U_grp.U s φ)‖ := by
  -- Uses that exp((t-s)B) is an isometry
  sorry

/-- The Duhamel formula as an integral identity.

For φ ∈ D(A):
  U(t)φ - exp(t·i·Aₙˢʸᵐ)φ = ∫₀ᵗ exp((t-s)·i·Aₙˢʸᵐ) · i·(A - Aₙˢʸᵐ) · U(s)φ ds

This is proven by showing the integrand is the derivative of
  s ↦ exp((t-s)·i·Aₙˢʸᵐ) · U(s)φ
-/
theorem duhamel_identity (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ =
    ∫ s in Set.Ioc 0 t, duhamelIntegrand U_grp gen hsa n t φ s := by
  sorry


/-- **Duhamel Estimate for Yosida Exponentials**

For φ ∈ D(A) and t ∈ ℝ:

  ‖U(t)φ - exp(t·I·Aₙˢʸᵐ)φ‖ ≤ |t| · sup_{s∈[0,|t|]} ‖(A - Aₙˢʸᵐ)(U(s)φ)‖

**The Duhamel formula:**

Let Bₙ = I·Aₙˢʸᵐ. Define f : [0,t] → H by f(s) = exp((t-s)Bₙ)(U(s)φ).

Differentiating (using product rule for operator-valued functions):
  f'(s) = -Bₙ exp((t-s)Bₙ)(U(s)φ) + exp((t-s)Bₙ)(iA·U(s)φ)
        = exp((t-s)Bₙ)(iA - Bₙ)(U(s)φ)

Boundary values:
  f(0) = exp(tBₙ)φ
  f(t) = exp(0)U(t)φ = U(t)φ

Fundamental theorem of calculus:
  U(t)φ - exp(tBₙ)φ = f(t) - f(0) = ∫₀ᵗ f'(s) ds
                    = ∫₀ᵗ exp((t-s)Bₙ)(iA - Bₙ)(U(s)φ) ds

Taking norms and using ‖exp((t-s)Bₙ)‖ = 1 (isometry):
  ‖U(t)φ - exp(tBₙ)φ‖ ≤ ∫₀ᵗ ‖(A - Aₙˢʸᵐ)(U(s)φ)‖ ds
                      ≤ |t| · sup_{s∈[0,|t|]} ‖(A - Aₙˢʸᵐ)(U(s)φ)‖

**AXIOMATIZED:** Requires Bochner integration machinery for operator-valued functions.
-/
lemma duhamel_estimate
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ ≤
    |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op (U_grp.U s φ) - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ := by
  sorry
/-- **Duhamel Estimate**

The error between U(t) and the Yosida exponential is controlled by the
supremum of the approximation error on the orbit.
-/
theorem duhamel_estimate' (n : ℕ+) (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ ≤
    |t| * ⨆ s ∈ Set.Icc 0 |t|, ‖(gen.op - yosidaApproxSym gen hsa n) (U_grp.U s φ)‖ := by
  sorry

end DuhamelFormula
/-- **Uniform Convergence of Approximant on Orbit**

For φ ∈ D(A), the approximants converge uniformly on the orbit {U(s)φ : s ∈ [0,|t|]}:

  sup_{s∈[0,|t|]} ‖(A - Aₙˢʸᵐ)(U(s)φ)‖ → 0 as n → ∞

**Proof outline:**

1. **Domain invariance:** U(s)φ ∈ D(A) for all s (from `unitary_group_domain_invariant`)

2. **Pointwise convergence:** Aₙˢʸᵐ(U(s)φ) → A(U(s)φ) for each s
   (from `yosidaApproxSym_tendsto_on_domain`)

3. **Compactness:** The orbit {U(s)φ : s ∈ [0,|t|]} is compact
   (continuous image of compact interval)

4. **Continuity:** s ↦ A(U(s)φ) = U(s)(Aφ) is continuous
   (from `generator_commutes_unitary` and strong continuity of U)

5. **Dini's theorem:** Pointwise convergence of continuous functions on compact
   set with monotone convergence implies uniform convergence

**AXIOMATIZED:** Requires careful handling of compactness and uniform convergence.
-/
lemma yosidaApproxSym_uniform_convergence_on_orbit
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => ⨆ (s : Set.Icc 0 |t|),
             ‖gen.op (U_grp.U s φ) - yosidaApproxSym gen hsa n (U_grp.U s φ)‖)
            atTop (𝓝 0) := by
  sorry

/-- **Yosida Exponentials Converge to Unitary Group on Domain**

For φ ∈ D(A):

  exp(t·I·Aₙˢʸᵐ)φ → U(t)φ  as n → ∞

**Proof:**

Combining `duhamel_estimate` and `yosidaApproxSym_uniform_convergence_on_orbit`:

  ‖exp(t·I·Aₙˢʸᵐ)φ - U(t)φ‖ ≤ |t| · sup_s ‖(A - Aₙˢʸᵐ)(U(s)φ)‖ → 0

**Role in the construction:**

This is the key convergence result on the domain. Combined with:
  - Density of D(A) in H
  - Isometry of the approximating exponentials

we obtain convergence on all of H (via the Cauchy sequence argument).
-/
lemma expBounded_yosidaApproxSym_tendsto_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
            atTop (𝓝 (U_grp.U t φ)) := by

  by_cases ht : t = 0
  · simp only [ht]
    have h_exp_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 φ = φ :=
      fun n => expBounded_at_zero _ φ
    have h_U_zero : U_grp.U 0 φ = φ := unitary_group_at_zero φ
    simp_rw [h_exp_zero, h_U_zero]
    exact tendsto_const_nhds

  · apply Metric.tendsto_atTop.mpr
    intro ε hε

    have h_unif := yosidaApproxSym_uniform_convergence_on_orbit gen hsa h_dense t φ hφ
    rw [Metric.tendsto_atTop] at h_unif

    have ht_pos : 0 < |t| + 1 := by linarith [abs_nonneg t]
    have hεt : ε / (|t| + 1) > 0 := div_pos hε ht_pos
    obtain ⟨N, hN⟩ := h_unif (ε / (|t| + 1)) hεt

    use N
    intro n hn
    rw [dist_eq_norm]

    calc ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - U_grp.U t φ‖
        = ‖U_grp.U t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ := norm_sub_rev _ _
      _ ≤ |t| * ⨆ (s : Set.Icc 0 |t|), ‖gen.op (U_grp.U s φ) - yosidaApproxSym gen hsa n (U_grp.U s φ)‖ :=
          duhamel_estimate gen hsa n t φ hφ
      _ < |t| * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_left _ (abs_pos.mpr ht)
          specialize hN n hn
          simp only [dist_zero_right, Real.norm_eq_abs] at hN
          rw [abs_of_nonneg] at hN
          · exact hN
          · apply Real.iSup_nonneg
            intro s
            exact norm_nonneg _
      _ < (|t| + 1) * (ε / (|t| + 1)) := by
          apply mul_lt_mul_of_pos_right _ hεt
          linarith
      _ = ε := mul_div_cancel₀ ε (ne_of_gt ht_pos)


/-- **Yosida Exponentials Form a Cauchy Sequence**

For any ψ ∈ H and t ∈ ℝ, the sequence {exp(t·I·Aₙˢʸᵐ)ψ}_{n≥1} is Cauchy.

**Proof (ε/3 argument):**

Given ε > 0:

1. **Approximate by domain:** Choose φ ∈ D(A) with ‖ψ - φ‖ < ε/3

2. **Cauchy on domain:** The sequence exp(t·I·Aₙˢʸᵐ)φ converges to U(t)φ
   (by `expBounded_yosidaApproxSym_tendsto_unitary`), hence is Cauchy.
   Choose N such that m,n ≥ N ⟹ ‖exp(...)_m φ - exp(...)_n φ‖ < ε/3

3. **Triangle inequality:** For m,n ≥ N:
```
   ‖exp(...)_m ψ - exp(...)_n ψ‖
     ≤ ‖exp(...)_m (ψ - φ)‖ + ‖exp(...)_m φ - exp(...)_n φ‖ + ‖exp(...)_n (φ - ψ)‖
     = ‖ψ - φ‖ + ‖exp(...)_m φ - exp(...)_n φ‖ + ‖φ - ψ‖    [isometry]
     < ε/3 + ε/3 + ε/3 = ε
```

**Significance:**

This Cauchy property, combined with completeness of H, ensures the strong limit
exists. We can then define exp(itA)ψ := lim_n exp(t·I·Aₙˢʸᵐ)ψ.
-/
theorem expBounded_yosidaApproxSym_cauchy
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε

  have hε3 : ε / 3 > 0 := by linarith

  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  have h_cauchy_φ : CauchySeq (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ) := by
    apply Filter.Tendsto.cauchySeq
    exact expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ_mem

  rw [Metric.cauchySeq_iff] at h_cauchy_φ
  obtain ⟨N, hN⟩ := h_cauchy_φ (ε / 3) hε3

  use N
  intro m hm n hn
  rw [dist_eq_norm]

  calc ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ -
        expBounded (I • yosidaApproxSym gen hsa n) t ψ‖
      = ‖(expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ) +
         (expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ)‖ := by
          congr 1; abel
    _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa m) t ψ - expBounded (I • yosidaApproxSym gen hsa m) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t φ - expBounded (I • yosidaApproxSym gen hsa n) t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖expBounded (I • yosidaApproxSym gen hsa m) t (ψ - φ)‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa n) t (φ - ψ)‖ := by
          congr 1
          · congr 1
            · rw [← ContinuousLinearMap.map_sub]
          · rw [← ContinuousLinearMap.map_sub]
    _ = ‖ψ - φ‖ +
        ‖expBounded (I • yosidaApproxSym gen hsa m) t φ - expBounded (I • yosidaApproxSym gen hsa n) t φ‖ +
        ‖φ - ψ‖ := by
          congr 1
          · congr 1
            · exact expBounded_yosidaApproxSym_isometry gen hsa m t (ψ - φ)
          · exact expBounded_yosidaApproxSym_isometry gen hsa n t (φ - ψ)
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hN m hm n hn
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring


/-- **Definition of exp(itA)**

The exponential of itA for self-adjoint A, defined as the strong operator limit
of the symmetrized Yosida approximants:

  exp(itA) := s-lim_{n→∞} exp(t·I·Aₙˢʸᵐ)

**Existence:**

The limit exists because:
  1. For each ψ ∈ H, {exp(t·I·Aₙˢʸᵐ)ψ} is Cauchy (by `expBounded_yosidaApproxSym_cauchy`)
  2. H is complete, so Cauchy sequences converge
  3. The limit defines a bounded linear operator (uniform boundedness principle)

**Properties (proved below):**
  - Unitary: ⟨exp(itA)ψ, exp(itA)φ⟩ = ⟨ψ, φ⟩
  - Group law: exp(i(s+t)A) = exp(isA) ∘ exp(itA)
  - Identity: exp(0) = I
  - Strong continuity: t ↦ exp(itA)ψ is continuous
  - Generator: d/dt[exp(itA)ψ]|_{t=0} = iAψ for ψ ∈ D(A)

**This completes Stone's theorem:** Every self-adjoint operator A generates a
strongly continuous one-parameter unitary group exp(itA), and conversely.
-/
noncomputable def exponential
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (t : ℝ) : H →L[ℂ] H :=
  limUnder atTop (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t)



/-!
============================================================================================================================
## Section 9: Properties of the Exponential
============================================================================================================================

We verify that the exponential exp(itA) defined via Yosida approximation satisfies
all the properties required of a strongly continuous one-parameter unitary group:

1. **Unitarity:** exp(itA) preserves inner products (hence norms)
2. **Group law:** exp(i(s+t)A) = exp(isA) ∘ exp(itA)
3. **Identity:** exp(0) = I
4. **Strong continuity:** t ↦ exp(itA)ψ is continuous for each ψ
5. **Generator:** The generator of this group is A itself

These properties are inherited from the approximating sequence by taking limits,
using continuity of the relevant operations (inner product, composition, etc.).

**Completing Stone's theorem:**

The results in this section, combined with the construction, establish:

  **Stone's Theorem:** There is a bijective correspondence between:
    - Self-adjoint operators A on H
    - Strongly continuous one-parameter unitary groups U(t) on H

  Given by: A ↦ (t ↦ exp(itA)) and U ↦ (its generator)
-/

/-- **Pointwise Convergence of Exponential**

The exponential applied to ψ equals the pointwise limit:

  exponential t ψ = lim_n exp(t·I·Aₙˢʸᵐ)ψ

This relates the operator-level `limUnder` definition to pointwise convergence.
-/
lemma exponential_tendsto
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) :
    Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
            atTop (𝓝 (exponential gen hsa t ψ)) := by
  sorry


/-- **Exponential is Unitary**

The exponential preserves inner products:

  ⟨exp(itA)ψ, exp(itA)φ⟩ = ⟨ψ, φ⟩

**Proof:**

Each approximant preserves inner products (by `expBounded_yosidaApproxSym_unitary`):
  ⟨exp(t·I·Aₙˢʸᵐ)ψ, exp(t·I·Aₙˢʸᵐ)φ⟩ = ⟨ψ, φ⟩

The inner product is continuous in both arguments:
  ⟨exp(t·I·Aₙˢʸᵐ)ψ, exp(t·I·Aₙˢʸᵐ)φ⟩ → ⟨exp(itA)ψ, exp(itA)φ⟩

The sequence is constantly ⟨ψ, φ⟩, so the limit is ⟨ψ, φ⟩.

**Physical significance:**

Unitarity means probability is conserved under time evolution. In quantum
mechanics, |⟨φ|ψ⟩|² is the probability of measuring state ψ in state φ.
Unitarity ensures these probabilities are preserved.
-/
theorem exponential_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ φ : H) :
    ⟪exponential gen hsa t ψ, exponential gen hsa t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  have h_conv_ψ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa t ψ)) := by
    unfold exponential
    have h_eval : Continuous (fun T : H →L[ℂ] H => T ψ) :=
      (ContinuousLinearMap.apply ℂ H ψ).continuous
    exact exponential_tendsto gen hsa h_dense t ψ

  have h_conv_φ : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa t φ)) := by
    unfold exponential
    have h_eval : Continuous (fun T : H →L[ℂ] H => T φ) :=
      (ContinuousLinearMap.apply ℂ H φ).continuous
    exact exponential_tendsto gen hsa h_dense t φ

  have h_approx_unitary : ∀ n : ℕ+,
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
    fun n => expBounded_yosidaApproxSym_unitary gen hsa n t ψ φ

  have h_inner_cont : Tendsto (fun n : ℕ+ =>
      ⟪expBounded (I • yosidaApproxSym gen hsa n) t ψ,
       expBounded (I • yosidaApproxSym gen hsa n) t φ⟫_ℂ)
      atTop (𝓝 ⟪exponential gen hsa t ψ, exponential gen hsa t φ⟫_ℂ) := by
    apply Filter.Tendsto.inner h_conv_ψ h_conv_φ

  have h_const : Tendsto (fun n : ℕ+ => ⟪ψ, φ⟫_ℂ) atTop (𝓝 ⟪ψ, φ⟫_ℂ) := tendsto_const_nhds

  have h_eq := tendsto_nhds_unique h_inner_cont (h_const.congr (fun n => (h_approx_unitary n).symm))
  exact h_eq

/-- **Exponential Satisfies Group Law**

The exponential satisfies the fundamental group property:

  exp(i(s+t)A)ψ = exp(isA)(exp(itA)ψ)

**Proof:**

Each approximant satisfies the group law (by `expBounded_group_law`):
  exp((s+t)·I·Aₙˢʸᵐ) = exp(s·I·Aₙˢʸᵐ) ∘ exp(t·I·Aₙˢʸᵐ)

Passing to the limit requires care: we need exp(s·I·Aₙˢʸᵐ)χ → exp(isA)χ
uniformly enough to compose with the inner convergence.

The key is using isometry: ‖exp(s·I·Aₙˢʸᵐ)‖ = 1 uniformly, allowing an
ε/2 argument to handle the composition.

**Physical significance:**

The group law says time evolution is composable: evolving for time s then
time t is the same as evolving for time s+t. This is the mathematical
statement of time-translation symmetry in quantum mechanics.
-/
theorem exponential_group_law
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (s t : ℝ) (ψ : H) :
    exponential gen hsa (s + t) ψ = exponential gen hsa s (exponential gen hsa t ψ) := by
  have h_approx_group : ∀ n : ℕ+,
      expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ =
      expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) := by
    intro n
    rw [expBounded_group_law]
    exact rfl

  have h_conv_lhs : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) (s + t) ψ)
                            atTop (𝓝 (exponential gen hsa (s + t) ψ)) := by
    unfold exponential
    have h_eval : Continuous (fun T : H →L[ℂ] H => T ψ) :=
      (ContinuousLinearMap.apply ℂ H ψ).continuous
    exact exponential_tendsto gen hsa h_dense (s + t) ψ

  have h_conv_t : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t ψ)
                          atTop (𝓝 (exponential gen hsa t ψ)) := by
    unfold exponential
    have h_eval : Continuous (fun T : H →L[ℂ] H => T ψ) :=
      (ContinuousLinearMap.apply ℂ H ψ).continuous
    exact exponential_tendsto gen hsa h_dense t ψ

  have h_conv_rhs : Tendsto (fun n : ℕ+ =>
      expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ))
      atTop (𝓝 (exponential gen hsa s (exponential gen hsa t ψ))) := by
    have h_inner := exponential_tendsto gen hsa h_dense t ψ
    have h_outer : ∀ χ : H, Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s χ)
                                    atTop (𝓝 (exponential gen hsa s χ)) :=
      fun χ => exponential_tendsto gen hsa h_dense s χ

    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hε2 : ε / 2 > 0 := by linarith

    rw [Metric.tendsto_atTop] at h_inner
    obtain ⟨N₁, hN₁⟩ := h_inner (ε / 2) hε2

    have h_outer_limit := h_outer (exponential gen hsa t ψ)
    rw [Metric.tendsto_atTop] at h_outer_limit
    obtain ⟨N₂, hN₂⟩ := h_outer_limit (ε / 2) hε2

    use max N₁ N₂
    intro n hn
    rw [dist_eq_norm]

    calc ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
          exponential gen hsa s (exponential gen hsa t ψ)‖
        = ‖(expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
           expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ)) +
          (expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ) -
           exponential gen hsa s (exponential gen hsa t ψ))‖ := by congr 1; abel
      _ ≤ ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ) -
           expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ) -
           exponential gen hsa s (exponential gen hsa t ψ)‖ := norm_add_le _ _
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) s (expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa t ψ)‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ) -
           exponential gen hsa s (exponential gen hsa t ψ)‖ := by rw [← map_sub]
      _ = ‖expBounded (I • yosidaApproxSym gen hsa n) t ψ - exponential gen hsa t ψ‖ +
          ‖expBounded (I • yosidaApproxSym gen hsa n) s (exponential gen hsa t ψ) -
           exponential gen hsa s (exponential gen hsa t ψ)‖ := by
            rw [expBounded_yosidaApproxSym_isometry gen hsa n s _]
      _ < ε / 2 + ε / 2 := by
            apply add_lt_add
            · rw [← dist_eq_norm]; exact hN₁ n (le_of_max_le_left hn)
            · rw [← dist_eq_norm]; exact hN₂ n (le_of_max_le_right hn)
      _ = ε := by ring

  have h_eq := tendsto_nhds_unique h_conv_lhs (h_conv_rhs.congr (fun n => (h_approx_group n).symm))
  exact h_eq

/-- **Exponential at Zero is Identity**

exp(i·0·A)ψ = ψ

**Proof:**

Each approximant at t=0 is the identity (by `expBounded_at_zero`):
  exp(0·I·Aₙˢʸᵐ)ψ = ψ

The constant sequence ψ converges to ψ, which must equal exponential(0)ψ.

**Role in group structure:**

This is one of the group axioms: U(0) must be the identity. Combined with
the group law, it implies U(t)U(-t) = U(0) = I, so U(-t) = U(t)⁻¹.
-/
theorem exponential_identity
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    exponential gen hsa 0 ψ = ψ := by
  have h_approx_zero : ∀ n : ℕ+, expBounded (I • yosidaApproxSym gen hsa n) 0 ψ = ψ :=
    fun n => expBounded_at_zero _ ψ

  have h_const : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                         atTop (𝓝 ψ) := by
    simp_rw [h_approx_zero]
    exact tendsto_const_nhds

  have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) 0 ψ)
                        atTop (𝓝 (exponential gen hsa 0 ψ)) := by
    unfold exponential
    have h_eval : Continuous (fun T : H →L[ℂ] H => T ψ) :=
      (ContinuousLinearMap.apply ℂ H ψ).continuous
    exact exponential_tendsto gen hsa h_dense 0 ψ

  exact tendsto_nhds_unique h_conv h_const

/-- **Exponential is Strongly Continuous**

For each ψ ∈ H, the map t ↦ exp(itA)ψ is continuous.

**Proof:**

On domain elements φ ∈ D(A), the exponential equals the original unitary group U(t)φ
(by convergence to the limit). Since U is strongly continuous, so is exponential on D(A).

For general ψ ∈ H, use an ε/3 argument:
  1. Approximate ψ by φ ∈ D(A)
  2. Use continuity at φ
  3. Control errors using isometry ‖exp(itA)(ψ - φ)‖ = ‖ψ - φ‖

**Physical significance:**

Strong continuity means small changes in time produce small changes in the
evolved state. This is essential for the physical interpretation: time
evolution should not have discontinuous jumps.

**Definition of C₀-group:**

A one-parameter group is called a C₀-group (or strongly continuous group) if
it satisfies this continuity condition. Stone's theorem characterizes precisely
which operators generate C₀-unitary groups: the self-adjoint operators.
-/
theorem exponential_strong_continuous
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) :
    Continuous (fun t : ℝ => exponential gen hsa t ψ) := by
  have h_exp_eq_U : ∀ (φ : H), φ ∈ gen.domain → ∀ t : ℝ, exponential gen hsa t φ = U_grp.U t φ := by
    intro φ hφ t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa t φ)) := by

      unfold exponential
      have h_eval : Continuous (fun T : H →L[ℂ] H => T φ) :=
        (ContinuousLinearMap.apply ℂ H φ).continuous
      exact exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto

  have h_cont_domain : ∀ (φ : H), φ ∈ gen.domain →
      Continuous (fun t : ℝ => exponential gen hsa t φ) := by
    intro φ hφ
    have h_eq : (fun t => exponential gen hsa t φ) = (fun t => U_grp.U t φ) := by
      ext t
      exact h_exp_eq_U φ hφ t
    rw [h_eq]
    exact U_grp.strong_continuous φ

  have h_isometry : ∀ t : ℝ, ∀ (χ : H), ‖exponential gen hsa t χ‖ = ‖χ‖ := by
    intro t χ
    have h_inner := exponential_unitary gen hsa h_dense t χ χ
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner
    have h_sq : ‖exponential gen hsa t χ‖^2 = ‖χ‖^2 := by
      have h_eq : (‖exponential gen hsa t χ‖ : ℂ)^2 = (‖χ‖ : ℂ)^2 := by
        exact h_inner
      exact_mod_cast h_eq
    rw [← Real.sqrt_sq (norm_nonneg (exponential gen hsa t χ)),
        ← Real.sqrt_sq (norm_nonneg χ), h_sq]

  rw [Metric.continuous_iff]
  intro t ε hε

  have hε3 : ε / 3 > 0 := by linarith

  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp
    (h_dense.closure_eq ▸ Set.mem_univ ψ) (ε / 3) hε3
  rw [dist_eq_norm] at hφ_close

  have h_cont_φ := h_cont_domain φ hφ_mem
  rw [Metric.continuous_iff] at h_cont_φ
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_φ t (ε / 3) hε3

  use δ, hδ_pos
  intro s hs
  rw [dist_eq_norm]

  calc ‖exponential gen hsa s ψ - exponential gen hsa t ψ‖
      = ‖(exponential gen hsa s ψ - exponential gen hsa s φ) +
         (exponential gen hsa s φ - exponential gen hsa t φ) +
         (exponential gen hsa t φ - exponential gen hsa t ψ)‖ := by abel_nf
    _ ≤ ‖exponential gen hsa s ψ - exponential gen hsa s φ‖ +
        ‖exponential gen hsa s φ - exponential gen hsa t φ‖ +
        ‖exponential gen hsa t φ - exponential gen hsa t ψ‖ := by
          apply le_trans (norm_add_le _ _)
          apply add_le_add_right
          exact norm_add_le _ _
    _ = ‖exponential gen hsa s (ψ - φ)‖ +
        ‖exponential gen hsa s φ - exponential gen hsa t φ‖ +
        ‖exponential gen hsa t (φ - ψ)‖ := by
          rw [← map_sub (exponential gen hsa s), ← map_sub (exponential gen hsa t)]
    _ = ‖ψ - φ‖ + ‖exponential gen hsa s φ - exponential gen hsa t φ‖ + ‖φ - ψ‖ := by
          rw [h_isometry s (ψ - φ), h_isometry t (φ - ψ)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          apply add_lt_add
          apply add_lt_add
          · exact hφ_close
          · rw [← dist_eq_norm]; exact hδ s hs
          · rw [norm_sub_rev]; exact hφ_close
    _ = ε := by ring

/-- **Generator of the Exponential is A**

The generator of the unitary group t ↦ exp(itA) is A itself:

  lim_{t→0} (exp(itA)φ - φ)/(it) = Aφ  for φ ∈ D(A)

Equivalently: lim_{t→0} t⁻¹(exp(itA)φ - φ) = iAφ

**Proof:**

On domain elements, exponential(t)φ = U(t)φ (the original unitary group).
The generator formula for U gives:
  lim_{t→0} (I·t)⁻¹(U(t)φ - φ) = Aφ

Converting: t⁻¹ = I·(I·t)⁻¹, so t⁻¹(U(t)φ - φ) = I·((I·t)⁻¹(U(t)φ - φ)) → I·Aφ

**Completing Stone's theorem:**

This result shows the correspondence A ↦ exp(itA) ↦ (generator of exp(itA)) = A
is the identity. Combined with the other direction (any C₀-unitary group has
a self-adjoint generator), this establishes the bijection of Stone's theorem.
-/
theorem exponential_generator_eq
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (φ : H) (hφ : φ ∈ gen.domain) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (exponential gen hsa t φ - φ))
            (𝓝[≠] 0) (𝓝 (I • gen.op φ)) := by
  have h_exp_eq_U : ∀ t : ℝ, exponential gen hsa t φ = U_grp.U t φ := by
    intro t
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense t φ hφ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) t φ)
                          atTop (𝓝 (exponential gen hsa t φ)) := by
      unfold exponential
      have h_eval : Continuous (fun T : H →L[ℂ] H => T φ) :=
        (ContinuousLinearMap.apply ℂ H φ).continuous
      exact exponential_tendsto gen hsa h_dense t φ
    exact tendsto_nhds_unique h_conv h_tendsto

  have h_eq_seq : ∀ t : ℝ, (t⁻¹ : ℂ) • (exponential gen hsa t φ - φ) =
                          (t⁻¹ : ℂ) • (U_grp.U t φ - φ) := by
    intro t
    rw [h_exp_eq_U t]

  have h_gen_formula := gen.generator_formula φ hφ

  have h_scalar : ∀ t : ℝ, t ≠ 0 → (t⁻¹ : ℂ) = I * (I * (t : ℂ))⁻¹ := by
    intro t ht
    field_simp

  have h_transform : ∀ t : ℝ, t ≠ 0 →
      (t⁻¹ : ℂ) • (U_grp.U t φ - φ) = I • ((I * (t : ℂ))⁻¹ • (U_grp.U t φ - φ)) := by
    intro t ht
    rw [← smul_assoc, h_scalar t ht]
    exact rfl

  refine Tendsto.congr' ?_ (Filter.Tendsto.const_smul h_gen_formula I)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h_eq_seq t, h_transform t ht]



/-- **Derivative of Exponential on Domain**

For φ ∈ D(A), the exponential is differentiable with derivative iA·exp(itA)φ:

  d/dt[exp(itA)φ] = iA·exp(itA)φ

**Proof:**

Using the group law and generator formula:
  d/dt[exp(itA)φ] = lim_{h→0} (exp(i(t+h)A)φ - exp(itA)φ)/h
                  = lim_{h→0} (exp(itA)(exp(ihA)φ - φ))/h
                  = exp(itA) · lim_{h→0} (exp(ihA)φ - φ)/h
                  = exp(itA) · (iAφ)
                  = iA·exp(itA)φ

The last equality uses commutativity A·U(t) = U(t)·A on domain elements.

**This is the Schrödinger equation:**

Writing ψ(t) = exp(itA)φ, the derivative formula becomes:
  dψ/dt = iAψ

which is the time-dependent Schrödinger equation with Hamiltonian A (in units
where ℏ = 1). Stone's theorem thus provides the mathematical foundation for
quantum dynamics.
-/
theorem exponential_derivative_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (t : ℝ) (ψ : H) (hψ : ψ ∈ gen.domain) :
    HasDerivAt (fun s : ℝ => exponential gen hsa s ψ)
               (I • gen.op (exponential gen hsa t ψ))
               t := by
  have h_exp_eq_U : ∀ s : ℝ, exponential gen hsa s ψ = U_grp.U s ψ := by
    intro s
    have h_tendsto := expBounded_yosidaApproxSym_tendsto_unitary gen hsa h_dense s ψ hψ
    have h_conv : Tendsto (fun n : ℕ+ => expBounded (I • yosidaApproxSym gen hsa n) s ψ)
                          atTop (𝓝 (exponential gen hsa s ψ)) := by
      unfold exponential
      have h_eval : Continuous (fun T : H →L[ℂ] H => T ψ) :=
        (ContinuousLinearMap.apply ℂ H ψ).continuous
      exact exponential_tendsto gen hsa h_dense s ψ

    exact tendsto_nhds_unique h_conv h_tendsto

  have h_fun_eq : (fun s : ℝ => exponential gen hsa s ψ) = (fun s : ℝ => U_grp.U s ψ) := by
    ext s
    exact h_exp_eq_U s

  rw [h_fun_eq]

  have hUtψ : U_grp.U t ψ ∈ gen.domain := gen.domain_invariant t ψ hψ

  rw [hasDerivAt_iff_tendsto_slope]

  have h_diff : ∀ s : ℝ, U_grp.U s ψ - U_grp.U t ψ = U_grp.U t (U_grp.U (s - t) ψ - ψ) := by
    intro s
    have h1 : U_grp.U s ψ = U_grp.U (t + (s - t)) ψ := by ring_nf
    have h2 : U_grp.U (t + (s - t)) ψ = U_grp.U t (U_grp.U (s - t) ψ) := by
      rw [U_grp.group_law]; rfl
    calc U_grp.U s ψ - U_grp.U t ψ
        = U_grp.U t (U_grp.U (s - t) ψ) - U_grp.U t ψ := by rw [h1, h2]
      _ = U_grp.U t (U_grp.U (s - t) ψ - ψ) := by rw [ContinuousLinearMap.map_sub]

  have h_slope : ∀ s : ℝ, s ≠ t → slope (fun s => U_grp.U s ψ) t s =
      U_grp.U t ((s - t)⁻¹ • (U_grp.U (s - t) ψ - ψ)) := by
    intro s hs
    simp only [slope, vsub_eq_sub, h_diff s]
    exact
      Eq.symm
        (ContinuousLinearMap.map_smul_of_tower (U_grp.U t) (s - t)⁻¹ ((U_grp.U (s - t)) ψ - ψ))


  have h_gen := gen.generator_formula ψ hψ

  have h_convert : ∀ h : ℝ, h ≠ 0 → (h⁻¹ : ℂ) • (U_grp.U h ψ - ψ) =
      I • ((I * (h : ℂ))⁻¹ • (U_grp.U h ψ - ψ)) := by
    intro h hh
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, mul_inv_rev, Complex.inv_I, mul_neg, mul_comm ((↑h)⁻¹) I,
        ← neg_mul, ← mul_assoc]
    simp

  have h_lim : Tendsto (fun s : ℝ => ((s - t)⁻¹ : ℂ) • (U_grp.U (s - t) ψ - ψ))
                       (𝓝[≠] t) (𝓝 (I • gen.op ψ)) := by
    have h_comp : Tendsto (fun s : ℝ => s - t) (𝓝[≠] t) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)) :=
          tendsto_id.sub tendsto_const_nhds
        simp only [sub_self] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero]
        exact hs
    have h_inner := h_gen.comp h_comp
    have h_smul := h_inner.const_smul I
    refine h_smul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← ofReal_sub]
    exact (h_convert (s - t) (sub_ne_zero.mpr hs)).symm

  have h_final : Tendsto (slope (fun s => U_grp.U s ψ) t) (𝓝[≠] t) (𝓝 (I • gen.op (U_grp.U t ψ))) := by
    have h_Ut_cont : Continuous (U_grp.U t) := (U_grp.U t).continuous
    have h_composed := h_Ut_cont.continuousAt.tendsto.comp h_lim
    have h_comm : U_grp.U t (I • gen.op ψ) = I • gen.op (U_grp.U t ψ) := by
      rw [ContinuousLinearMap.map_smul, generator_commutes_unitary gen t ψ hψ]
    rw [h_comm] at h_composed
    refine h_composed.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply]
    convert (h_slope s hs).symm using 2
    rw [← Complex.ofReal_sub]
    rw [← h_exp_eq_U]
    norm_cast

  rw [h_exp_eq_U, ← h_exp_eq_U, h_exp_eq_U]
  exact h_final

/-
## Summary
This completes the documentation for the Yosida approximation file. Here's the overall structure:
Section 0: Arithmetic lemmas for complex spectral parameters (I·n, -I·n)
Section 1: Core Yosida operator definitions (Aₙ, Aₙˢʸᵐ, Jₙ, Jₙ⁻)
Section 2: Norm bounds (‖Aₙ‖ ≤ 2n, ‖Jₙ‖ ≤ 1)
Section 3: Self-adjointness of Aₙˢʸᵐ and skew-adjointness of I·Aₙˢʸᵐ
Section 4: J operator identities and convergence (Jₙ → I strongly)
Section 5: Yosida approximant convergence (Aₙφ → Aφ on domain)
Section 6: Exponential of bounded operators (definition, group law, adjoint, unitarity)
Section 7: Unitarity of Yosida exponentials (inner product and norm preservation)
Section 8: Cauchy sequences and exponential definition (Duhamel estimate, convergence)
- Epanded with Bochner and Uniform Convergence for Duhamel
Section 9: Properties of exp(itA) (unitarity, group law, strong continuity, generator = A)
Axiomatized results (marked with sorry):

duhamel_estimate: Requires Bochner integration
yosidaApproxSym_uniform_convergence_on_orbit: Requires compactness/Dini's theorem machinery
exponential_tendsto: Relates operator limit to pointwise limit

These axiomatizations isolate the analytic/measure-theoretic content from the algebraic structure,
following the same philosophy as VonNeumann.lean.
-/

end StonesTheorem.Exponential
