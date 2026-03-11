/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/CompositeObservable.lean
-/
import LogosLibrary.QuantumMechanics.Uncertainty.Schrodinger
import LogosLibrary.InformationGeometry.CramerRao.SchrodingerRLD
/-!
# Composite Observables and the Quantum–Geometric Bridge

The **composite observable** `O_v = ∑ᵢ vᵢ Oᵢ` contracts a real tangent
vector `v ∈ ℝⁿ` against a family of self-adjoint operators.  It is the
quantum object corresponding to a *directional score* in information
geometry: just as `⟨v, s(θ,ω)⟩ = ∑ vᵢ sᵢ` probes the statistical
manifold in direction `v`, the composite `O_v` probes the quantum state
in direction `v` through the observable algebra.

The central results are three bilinearity lemmas:

1. `covariance_composite` — `Cov(O_v, O_w) = ∑ᵢⱼ vᵢ wⱼ Cov(Oᵢ, Oⱼ)`
2. `commutator_im_composite` — `Im⟨ψ,[O_v,O_w]ψ⟩ = ∑ᵢⱼ vᵢ wⱼ Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`
3. `variance_composite` — `Var(O_v) = ∑ᵢⱼ vᵢ vⱼ Cov(Oᵢ, Oⱼ)`

These establish that the covariance matrix `Cov(Oᵢ, Oⱼ)` is a genuine
bilinear form on tangent vectors, and the commutator expectation matrix
`Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩` is a genuine 2-form.  In the language of information
geometry: the first is the **Riemannian metric** (SLD Fisher information)
and the second is the **symplectic form**.

The key data structure `QuantumRLDData` bundles a family of `n`
observables with a common invariant domain — the quantum analogue of
a regular statistical model.  The invariant domain condition
`∀ i j, Oⱼψ ∈ dom(Oᵢ)` ensures that all pairwise products, commutators,
and composites are well-defined on the state `ψ`.  This is the minimal
regularity needed to make the Fisher metric finite and the Schrödinger
bound meaningful.

## Design notes

The bilinearity proofs work by reducing composite-level identities
(Schrödinger applied to `O_v, O_w`) to sums over pairwise identities
(Schrödinger applied to `Oᵢ, Oⱼ`).  The reduction passes through
`inner_shifted_composite`, which decomposes `⟨Õ_v ψ, Õ_w ψ⟩` as a
double sum, then takes real and imaginary parts separately.

This mirrors the classical proof that the Fisher matrix is the Hessian
of the KL divergence: one differentiates a scalar quantity (the divergence
/ the inner product) and identifies the components of the resulting
bilinear form.  The quantum novelty is that the form is *complex-valued*,
and its imaginary part — invisible classically — carries the symplectic
structure responsible for uncertainty.

## References

* S. Amari, *Information Geometry and Its Applications*, §2.2, 2016.
  — The directional score `⟨v, s⟩` and the Fisher bilinear form.
* A. S. Holevo, *Probabilistic and Statistical Aspects of Quantum
  Theory*, North-Holland, 1982. — The multiparameter quantum
  estimation framework.
-/
namespace QuantumMechanics.Bridge

open InnerProductSpace UnboundedObservable Robertson Schrodinger InformationGeometry
open scoped ComplexConjugate

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma mem_of_mem_iInf {O : Fin n → UnboundedObservable H} {x : H}
    (hx : x ∈ ⨅ i, (O i).domain) (i : Fin n) : x ∈ (O i).domain :=
  iInf_le (fun i => (O i).domain) i hx


private lemma mem_iInf_of_forall {O : Fin n → UnboundedObservable H} {x : H}
    (hx : ∀ i, x ∈ (O i).domain) : x ∈ ⨅ i, (O i).domain := by
  rw [← SetLike.mem_coe, Submodule.coe_iInf]
  exact Set.mem_iInter.mpr hx

/-- The **composite observable** `O_v = ∑ᵢ vᵢ · Oᵢ`, defined on `⋂ᵢ dom(Oᵢ)`.

This is the quantum analogue of contracting a tangent vector `v ∈ T_θΘ`
against a family of observables.  The coefficients are *real* to preserve
self-adjointness: `⟨O_v ψ, φ⟩ = ∑ vᵢ ⟨Oᵢψ, φ⟩ = ∑ vᵢ ⟨ψ, Oᵢφ⟩ = ⟨ψ, O_v φ⟩`. -/
noncomputable def compositeObservable
    (O : Fin n → UnboundedObservable H) (v : Fin n → ℝ)
    (h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H)) :
    UnboundedObservable H where
  domain := ⨅ i, (O i).domain
  toFun :=
    ∑ i : Fin n, ((v i : ℝ) : ℂ) •
      ((O i).toFun.comp (Submodule.inclusion (iInf_le (fun i => (O i).domain) i)))
  dense := h_dense
  symmetric := fun ⟨ψ, hψ⟩ ⟨φ, hφ⟩ => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [sum_inner, inner_sum]
    congr 1; ext i
    simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    exact (O i).symmetric
      ⟨ψ, iInf_le (fun i => (O i).domain) i hψ⟩
      ⟨φ, iInf_le (fun i => (O i).domain) i hφ⟩


/-- The composite observable applied to `φ` decomposes as a sum. -/
lemma compositeObservable_apply
    (O : Fin n → UnboundedObservable H) (v : Fin n → ℝ)
    (h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H))
    (φ : H) (hφ : φ ∈ ⨅ i, (O i).domain) :
    (compositeObservable O v h_dense).apply φ hφ =
    ∑ i : Fin n, ((v i : ℝ) : ℂ) • (O i).apply φ (mem_of_mem_iInf hφ i) := by
  simp only [compositeObservable, apply]
  -- unused : LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.comp_apply
  /-⊢ (∑ i, ↑(v i) • (O i).toFun ∘ₗ Submodule.inclusion ⋯) ⟨φ, hφ⟩ = ∑ x, ↑(v x) • (O x).toFun ⟨φ, ⋯⟩-/
  exact
    LinearMap.sum_apply Finset.univ
      (fun d => ↑(v d) • (O d).toFun ∘ₗ Submodule.inclusion (compositeObservable._proof_3 O d))
      ⟨φ, hφ⟩


/-- Bundled quantum data for constructing the RLD Fisher model.

This packages a family of `n` observables, a normalized state `ψ`,
and the mutual domain conditions ensuring that all pairwise
commutators and composites are well-defined on `ψ`.

The key condition `hOψ_all` says that `ψ` sits in a *common invariant
domain* for all observables — the quantum analogue of regularity. -/
structure QuantumRLDData (n : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  O : Fin n → UnboundedObservable H
  ψ : H
  h_norm : ‖ψ‖ = 1
  hψ_all : ∀ i, ψ ∈ (O i).domain
  /-- `Oⱼψ ∈ dom(Oᵢ)` for all `i, j`: the invariant domain condition. -/
  hOψ_all : ∀ i j, (O j).apply ψ (hψ_all j) ∈ (O i).domain
  h_dense : Dense ((⨅ i, (O i).domain : Submodule ℂ H) : Set H)


namespace QuantumRLDData

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : QuantumRLDData n H)


/-- Abbreviation for the common domain `⋂ᵢ dom(Oᵢ)`. -/
def commonDomain : Submodule ℂ H := ⨅ i, (D.O i).domain

/-- `ψ ∈ ⋂ᵢ dom(Oᵢ)`. -/
lemma ψ_mem_commonDomain : D.ψ ∈ D.commonDomain :=
  mem_iInf_of_forall D.hψ_all

/-- `O_w ψ = ∑ⱼ wⱼ Oⱼψ` lies in the common domain. -/
lemma compositeApply_mem_commonDomain (w : Fin n → ℝ) :
    (compositeObservable D.O w D.h_dense).apply D.ψ
      D.ψ_mem_commonDomain ∈ D.commonDomain := by
  rw [compositeObservable_apply]
  apply mem_iInf_of_forall; intro i
  apply Submodule.sum_mem; intro j _
  exact Submodule.smul_mem _ _ (D.hOψ_all i j)

/-- `DomainConditions` for `[O_v, O_w]ψ`, derived from `QuantumRLDData`. -/
def composites_domainConditions (v w : Fin n → ℝ) :
    DomainConditions (compositeObservable D.O v D.h_dense)
                     (compositeObservable D.O w D.h_dense) D.ψ where
  hψ_A := D.ψ_mem_commonDomain
  hψ_B := D.ψ_mem_commonDomain
  hBψ_A := D.compositeApply_mem_commonDomain w
  hAψ_B := D.compositeApply_mem_commonDomain v

/-- `ShiftedDomainConditions` for `O_v, O_w` — ready to feed
into `schrodinger_uncertainty`. -/
def composites_shiftedDC (v w : Fin n → ℝ) :
    ShiftedDomainConditions
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense) D.ψ where
  hψ_A := D.ψ_mem_commonDomain
  hψ_B := D.ψ_mem_commonDomain
  hBψ_A := D.compositeApply_mem_commonDomain w
  hAψ_B := D.compositeApply_mem_commonDomain v
  h_norm := D.h_norm

/-- Pairwise `DomainConditions` for `[Oᵢ, Oⱼ]ψ`. -/
def pairwise_domainConditions (i j : Fin n) :
    DomainConditions (D.O i) (D.O j) D.ψ where
  hψ_A := D.hψ_all i
  hψ_B := D.hψ_all j
  hBψ_A := D.hOψ_all i j
  hAψ_B := D.hOψ_all j i

end QuantumRLDData

/-- Expectation of the composite observable decomposes linearly:
  `⟨O_v⟩_ψ = ∑ᵢ vᵢ ⟨Oᵢ⟩_ψ`. -/
lemma expectation_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeObservable D.O v D.h_dense).expectation D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    ∑ i : Fin n, v i * (D.O i).expectation D.ψ D.h_norm (D.hψ_all i) := by
  unfold expectation
  rw [compositeObservable_apply]
  rw [inner_sum]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [inner_smul_right]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
  rw [(D.O i).inner_self_eq_re (D.hψ_all i)]
  simp

/-- The shifted composite decomposes as a sum of shifted components:
  `(O_v - ⟨O_v⟩)ψ = ∑ᵢ vᵢ (Oᵢ - ⟨Oᵢ⟩)ψ`. -/
lemma shiftedApply_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeObservable D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain =
    ∑ i : Fin n, ((v i : ℝ) : ℂ) •
      (D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i) := by
  unfold shiftedApply
  rw [compositeObservable_apply]
  rw [expectation_composite]
  -- LHS: (∑ᵢ vᵢ • Oᵢψ) - (∑ᵢ vᵢ⟨Oᵢ⟩) • ψ
  -- RHS: ∑ᵢ vᵢ • (Oᵢψ - ⟨Oᵢ⟩ψ)
  simp only [smul_sub, Finset.sum_sub_distrib]
  congr 1
  -- Need: (∑ᵢ vᵢ⟨Oᵢ⟩) • ψ = ∑ᵢ vᵢ • (⟨Oᵢ⟩ • ψ)
  -- i.e. (∑ᵢ vᵢ⟨Oᵢ⟩) • ψ = ∑ᵢ (vᵢ⟨Oᵢ⟩) • ψ
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.coe_smul]
  rw [Finset.sum_smul]
  congr 1; ext i
  simp [smul_smul]
  rw [← Complex.ofReal_mul]
  exact Complex.coe_smul (v i * (D.O i).expectation D.ψ D.h_norm (D.hψ_all i)) D.ψ

/-- The inner product of shifted composites decomposes as a double sum:
  `⟨Õ_v ψ, Õ_w ψ⟩ = ∑ᵢⱼ vᵢwⱼ ⟨Õᵢψ, Õⱼψ⟩`. -/
lemma inner_shifted_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    ⟪(compositeObservable D.O v D.h_dense).shiftedApply
        D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
      (compositeObservable D.O w D.h_dense).shiftedApply
        D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ =
    ∑ i : Fin n, ∑ j : Fin n,
      ((v i : ℝ) : ℂ) * ((w j : ℝ) : ℂ) *
      ⟪(D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i),
        (D.O j).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all j) (D.hψ_all j)⟫_ℂ := by
  rw [shiftedApply_composite, shiftedApply_composite]
  rw [sum_inner]
  congr 1; ext i
  rw [inner_smul_left, inner_sum]
  rw [Finset.mul_sum]
  congr 1; ext j
  rw [inner_smul_right, Complex.conj_ofReal]
  ring


def pairwise_shiftedDC (D : QuantumRLDData n H) (i j : Fin n) :
    ShiftedDomainConditions (D.O i) (D.O j) D.ψ where
  hψ_A := D.hψ_all i
  hψ_B := D.hψ_all j
  hBψ_A := D.hOψ_all i j
  hAψ_B := D.hOψ_all j i
  h_norm := D.h_norm

/-- Covariance of composite observables is bilinear:
  `Cov(O_v, O_w)_ψ = ∑ᵢⱼ vᵢwⱼ Cov(Oᵢ, Oⱼ)_ψ`. -/
lemma covariance_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    covariance (compositeObservable D.O v D.h_dense)
               (compositeObservable D.O w D.h_dense)
               D.ψ (D.composites_shiftedDC v w) =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * covariance (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j) := by
  rw [← re_inner_shifted_eq_covariance]
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
  rw [inner_shifted_composite]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [Complex.re_sum]
  congr 1; ext j
  rw [← re_inner_shifted_eq_covariance]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             mul_zero, sub_zero]
  ring_nf
  simp_all only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero,
    mul_eq_mul_left_iff, mul_eq_zero]
  apply Or.inl
  rfl

/-- The imaginary part of the commutator expectation of composites is bilinear:
  `Im⟨ψ,[O_v,O_w]ψ⟩ = ∑ᵢⱼ vᵢwⱼ Im⟨ψ,[Oᵢ,Oⱼ]ψ⟩`. -/
lemma commutator_im_composite (D : QuantumRLDData n H) (v w : Fin n → ℝ) :
    (⟪D.ψ, commutatorAt
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j *
      (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im := by
  -- Strategy: use im_inner_shifted_eq_half_commutator on both sides
  -- to reduce to imaginary part of inner_shifted_composite.
  have h_lhs := im_inner_shifted_eq_half_commutator
    (compositeObservable D.O v D.h_dense)
    (compositeObservable D.O w D.h_dense)
    D.ψ (D.composites_shiftedDC v w)
  -- h_lhs : (⟪Õ_v ψ, Õ_w ψ⟫).im = ½ * Im⟨ψ,[O_v,O_w]ψ⟩
  -- So: Im⟨ψ,[O_v,O_w]ψ⟩ = 2 * (⟪Õ_v ψ, Õ_w ψ⟫).im
  -- Similarly for each (i,j) pair.

  -- Take Im of inner_shifted_composite
  have h_decomp : (⟪(compositeObservable D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
    (compositeObservable D.O w D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j *
      (⟪(D.O i).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all i) (D.hψ_all i),
        (D.O j).shiftedApply D.ψ D.ψ D.h_norm (D.hψ_all j) (D.hψ_all j)⟫_ℂ).im := by
    rw [inner_shifted_composite]
    rw [Complex.im_sum]
    congr 1; ext i
    rw [Complex.im_sum]
    congr 1; ext j
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
        add_zero, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

  -- Now connect both sides through the ½ factor
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ] at h_lhs
  have h_ij (i j : Fin n) :=
    im_inner_shifted_eq_half_commutator (D.O i) (D.O j) D.ψ (pairwise_shiftedDC D i j)
  -- h_lhs: (...).im = ½ * (⟪ψ,[O_v,O_w]ψ⟫).im
  -- h_ij:  (...).im = ½ * (⟪ψ,[Oᵢ,Oⱼ]ψ⟫).im
  -- h_decomp: LHS of h_lhs = ∑ᵢⱼ vᵢwⱼ * LHS of h_ij
  -- So: ½ * target_LHS = ∑ᵢⱼ vᵢwⱼ * ½ * target_RHS(i,j)
  -- Rewrite h_decomp using h_ij: replace each (⟪Õᵢψ, Õⱼψ⟫).im with ½ * (⟪ψ,[Oᵢ,Oⱼ]ψ⟫).im
  have h_decomp' : (⟪(compositeObservable D.O v D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain,
    (compositeObservable D.O w D.h_dense).shiftedApply
      D.ψ D.ψ D.h_norm D.ψ_mem_commonDomain D.ψ_mem_commonDomain⟫_ℂ).im =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * (1/2 *
        (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
          (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im) := by
    rw [h_decomp]
    congr 1; ext i; congr 1; ext j
    exact Real.ext_cauchy (congrArg Real.cauchy (congrArg (HMul.hMul (v i * w j)) (h_ij i j)))
  -- Now h_lhs says LHS = ½ * target_LHS
  -- and h_decomp' says LHS = ∑ᵢⱼ vᵢwⱼ * (½ * target_RHS(i,j))
  -- So: ½ * target_LHS = ∑ᵢⱼ vᵢwⱼ * ½ * target_RHS(i,j)
  -- Factor out ½ on the RHS and cancel
  have h_half_ne : (1/2 : ℝ) ≠ 0 := by norm_num
  have h_combined : 1/2 * (⟪D.ψ, commutatorAt
      (compositeObservable D.O v D.h_dense)
      (compositeObservable D.O w D.h_dense)
      D.ψ (D.composites_shiftedDC v w).toDomainConditions⟫_ℂ).im =
    1/2 * ∑ i : Fin n, ∑ j : Fin n,
      v i * w j * (⟪D.ψ, commutatorAt (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j).toDomainConditions⟫_ℂ).im := by
    rw [← h_lhs, h_decomp']
    ring_nf
    rw [Finset.sum_mul]
    congr 1; ext i
    rw [← Finset.sum_mul]

  linarith [mul_left_cancel₀ h_half_ne h_combined]

/-- Variance equals self-covariance: `Var(A) = Cov(A,A)`. -/
lemma variance_eq_covariance_self (D : QuantumRLDData n H) (i : Fin n) :
    (D.O i).variance D.ψ D.h_norm (D.hψ_all i) =
    covariance (D.O i) (D.O i) D.ψ (pairwise_shiftedDC D i i) := by
  unfold variance
  rw [← re_inner_shifted_eq_covariance]
  simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
  -- ⊢ ‖x‖ ^ 2 = (⟪x, x⟫_ℂ).re  (where x = shiftedApply ...)
  rw [inner_self_eq_norm_sq_to_K]
  simp only [Complex.coe_algebraMap]
  norm_cast

/-- Variance of composite observable is bilinear:
  `Var(O_v) = ∑ᵢⱼ vᵢvⱼ Cov(Oᵢ,Oⱼ)`. -/
lemma variance_composite (D : QuantumRLDData n H) (v : Fin n → ℝ) :
    (compositeObservable D.O v D.h_dense).variance D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    ∑ i : Fin n, ∑ j : Fin n,
      v i * v j * covariance (D.O i) (D.O j) D.ψ
        (pairwise_shiftedDC D i j) := by
  -- Var(O_v) = ‖Õ_v ψ‖² = Re⟨Õ_v ψ, Õ_v ψ⟩ = Cov(O_v, O_v) = ∑ᵢⱼ vᵢvⱼ Cov(Oᵢ,Oⱼ)
  have h_var_cov : (compositeObservable D.O v D.h_dense).variance D.ψ D.h_norm
      D.ψ_mem_commonDomain =
    covariance (compositeObservable D.O v D.h_dense)
               (compositeObservable D.O v D.h_dense)
               D.ψ (D.composites_shiftedDC v v) := by
    unfold variance
    rw [← re_inner_shifted_eq_covariance]
    simp only [ShiftedDomainConditions.A'ψ, ShiftedDomainConditions.B'ψ]
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap]
    norm_cast
  rw [h_var_cov, covariance_composite]




end QuantumMechanics.Bridge
