/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvo/API.lean
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Schrodinger

namespace QuantumMechanics.UnitaryEvo

open InnerProductSpace Complex Filter Topology

open Generators StonesTheorem Schrödinger Yosida Bochner Resolvent


/-- The generator commutes with the unitary group on its domain:
`A(U(t)ψ) = U(t)(Aψ)` for `ψ ∈ dom(A)`. -/
lemma generator_commutes_with_group {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ₀ : H) (hψ₀ : ψ₀ ∈ gen.domain)
    (t : ℝ) :
    gen.op ⟨U_grp.U t ψ₀, gen.domain_invariant t ψ₀ hψ₀⟩ =
    U_grp.U t (gen.op ⟨ψ₀, hψ₀⟩) := by
  have hφ : U_grp.U t ψ₀ ∈ gen.domain := gen.domain_invariant t ψ₀ hψ₀
  -- (1) Generator formula at U(t)ψ₀ (converting exponential → U)
  have hlim1 : Tendsto
      (fun h : ℝ => ((I * ↑h)⁻¹ : ℂ) • (U_grp.U h (U_grp.U t ψ₀) - U_grp.U t ψ₀))
      (𝓝[≠] 0) (𝓝 (gen.op ⟨U_grp.U t ψ₀, hφ⟩)) := by
    have := stone_generator_of_exponential U_grp gen hsa h_dense _ hφ
    exact this.congr' (by
      filter_upwards [self_mem_nhdsWithin] with h _
      simp only [stone_exponential_eq_group U_grp gen hsa h_dense])
  -- (2) U(h) and U(t) commute on ψ₀ (by group law + add_comm)
  have hcomm : ∀ r : ℝ, U_grp.U r (U_grp.U t ψ₀) = U_grp.U t (U_grp.U r ψ₀) := by
    intro r
    have h1 := ContinuousLinearMap.ext_iff.mp (U_grp.group_law r t) ψ₀
    have h2 := ContinuousLinearMap.ext_iff.mp (U_grp.group_law t r) ψ₀
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [← h1, show r + t = t + r from add_comm r t, h2]
  -- (3) Rewrite limit 1: factor U(t) out via commutativity + linearity
  have hlim1' : Tendsto
      (fun h : ℝ => U_grp.U t (((I * ↑h)⁻¹ : ℂ) • (U_grp.U h ψ₀ - ψ₀)))
      (𝓝[≠] 0) (𝓝 (gen.op ⟨U_grp.U t ψ₀, hφ⟩)) := by
    refine hlim1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    rw [hcomm h, ← map_sub (U_grp.U t) (U_grp.U h ψ₀) ψ₀,
        ← map_smul (U_grp.U t) ((I * ↑h)⁻¹) (U_grp.U h ψ₀ - ψ₀)]
  -- (4) Generator formula at ψ₀
  have hlim2 : Tendsto
      (fun h : ℝ => ((I * ↑h)⁻¹ : ℂ) • (U_grp.U h ψ₀ - ψ₀))
      (𝓝[≠] 0) (𝓝 (gen.op ⟨ψ₀, hψ₀⟩)) := by
    have := stone_generator_of_exponential U_grp gen hsa h_dense ψ₀ hψ₀
    exact this.congr' (by
      filter_upwards [self_mem_nhdsWithin] with h _
      simp only [stone_exponential_eq_group U_grp gen hsa h_dense])
  -- (5) U(t) is continuous → passes through the limit
  have hlim3 : Tendsto
      (fun h : ℝ => U_grp.U t (((I * ↑h)⁻¹ : ℂ) • (U_grp.U h ψ₀ - ψ₀)))
      (𝓝[≠] 0) (𝓝 (U_grp.U t (gen.op ⟨ψ₀, hψ₀⟩))) :=
    ((U_grp.U t).continuous.tendsto _).comp hlim2
  -- (6) Both limits equal → A(U(t)ψ₀) = U(t)(Aψ₀)
  exact tendsto_nhds_unique hlim1' hlim3


/-- **Energy conservation**: the expectation value of the generator (Hamiltonian)
is preserved under unitary time evolution: `⟨A(U(t)ψ), U(t)ψ⟩ = ⟨Aψ, ψ⟩`. -/
lemma energy_conservationvariable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp)
    (hsa : gen.IsSelfAdjoint)
    (h_dense : Dense (gen.domain : Set H))
    (ψ : H) (hψ : ψ ∈ gen.domain)
    (t : ℝ) :
    ⟪gen.op ⟨U_grp.U t ψ, gen.domain_invariant t ψ hψ⟩, U_grp.U t ψ⟫_ℂ =
    ⟪gen.op ⟨ψ, hψ⟩, ψ⟫_ℂ := by
  rw [generator_commutes_with_group U_grp gen hsa h_dense ψ hψ t]
  exact U_grp.unitary t (gen.op ⟨ψ, hψ⟩) ψ


/-- **Time-reversal of transition amplitudes.**
`⟨U(t)ψ, φ⟩ = ⟨ψ, U(-t)φ⟩`: the adjoint of `U(t)` is `U(-t)`,
i.e., unitary operators satisfy `U(t)* = U(t)⁻¹ = U(-t)`. -/
lemma transition_amplitude_reversal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ φ : H) (t : ℝ) :
    ⟪U_grp.U t ψ, φ⟫_ℂ = ⟪ψ, U_grp.U (-t) φ⟫_ℂ := by
  -- Insert U(-t)U(-t)⁻¹ = U(-t)U(t) on the left via unitarity
  calc ⟪U_grp.U t ψ, φ⟫_ℂ
      = ⟪U_grp.U (-t) (U_grp.U t ψ), U_grp.U (-t) φ⟫_ℂ :=
          (U_grp.unitary (-t) _ _).symm
    _ = ⟪ψ, U_grp.U (-t) φ⟫_ℂ := by
          congr 1
          -- Goal: U(-t)(U(t)ψ) = ψ
          have h := ContinuousLinearMap.ext_iff.mp (U_grp.group_law (-t) t) ψ
          simp only [ContinuousLinearMap.comp_apply, neg_add_cancel] at h
          rw [← h]
          exact ContinuousLinearMap.ext_iff.mp U_grp.identity ψ


/-- **Probability conservation**: the norm of a state is preserved
under unitary time evolution. The Born rule probability ‖ψ‖² is constant. -/
lemma probability_conservationvariable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ : H) (t : ℝ) :
    ‖U_grp.U t ψ‖ = ‖ψ‖ := by
  have h := U_grp.unitary t ψ ψ
  rw [@inner_self_eq_norm_sq_to_K ℂ, @inner_self_eq_norm_sq_to_K ℂ] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)


/-- **Operator norm of a unitary**: `‖U(t)‖ = 1` on a nontrivial space.
Upper bound from isometry, lower bound from any nonzero vector. -/
lemma unitary_group_norm_eq_one {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (t : ℝ) :
    ‖U_grp.U t‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ψ => by
      rw [one_mul]
      exact le_of_eq (probability_conservationvariable U_grp ψ t))
  · obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have h_pos : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hψ
    have h_le := ContinuousLinearMap.le_opNorm (U_grp.U t) ψ
    rw [probability_conservationvariable U_grp ψ t] at h_le
    exact one_le_of_le_mul_right₀ h_pos h_le


/-- `U(-t)` is the inverse of `U(t)`: `U(-t)(U(t)ψ) = ψ`. -/
lemma unitary_inversevariable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ : H) (t : ℝ) :
    U_grp.U (-t) (U_grp.U t ψ) = ψ := by
  have := ContinuousLinearMap.ext_iff.mp (U_grp.group_law (-t) t) ψ
  simp only [ContinuousLinearMap.comp_apply, neg_add_cancel] at this
  rw [this.symm]; simp [show U_grp.U 0 = ContinuousLinearMap.id ℂ H from U_grp.identity]


/-- `U(t)` is the forward inverse of `U(-t)`: `U(t)(U(-t)ψ) = ψ`. -/
lemma unitary_inverse_forward {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ : H) (t : ℝ) :
    U_grp.U t (U_grp.U (-t) ψ) = ψ := by
  have := unitary_inversevariable U_grp ψ (-t)
  rwa [neg_neg] at this


/-- **Microscopic reversibility**: the transition amplitude from `ψ` to `φ`
forward in time equals the conjugate of the amplitude from `φ` to `ψ` backward:
`⟨U(t)ψ, φ⟩ = conj⟨U(-t)φ, ψ⟩`. -/
lemma transition_amplitude_reversibilityvariable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ φ : H) (t : ℝ) :
    ⟪U_grp.U t ψ, φ⟫_ℂ = starRingEnd ℂ ⟪U_grp.U (-t) φ, ψ⟫_ℂ := by
  rw [transition_amplitude_reversal U_grp ψ φ t, inner_conj_symm]


/-- **Orthogonality is preserved**: orthogonal states remain orthogonal
under unitary time evolution. -/
lemma orthogonality_preserved {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ φ : H) (t : ℝ) (h : ⟪ψ, φ⟫_ℂ = 0) :
    ⟪U_grp.U t ψ, U_grp.U t φ⟫_ℂ = 0 := by
  rw [U_grp.unitary t ψ φ, h]


/-- **Transition probabilities are conserved**: `‖⟨U(t)ψ, U(t)φ⟩‖ = ‖⟨ψ, φ⟩‖`.
Physically: the probability of measuring state φ given state ψ is
time-independent. Distinct from `probability_conservationvariable`,
which is the single-state norm; this is the two-state overlap. -/
lemma transition_probability_conserved {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (ψ φ : H) (t : ℝ) :
    ‖⟪U_grp.U t ψ, U_grp.U t φ⟫_ℂ‖ = ‖⟪ψ, φ⟫_ℂ‖ := by
  rw [U_grp.unitary t ψ φ]


/-- **Conserved quantities (Noether's theorem, quantum version).**
If a bounded observable `B` commutes with the unitary group, then its
expectation value is preserved under time evolution:
  `⟨B(U(t)ψ), U(t)ψ⟩ = ⟨Bψ, ψ⟩`.

Physically: symmetries of the Hamiltonian yield conservation laws.
Angular momentum is conserved iff the Hamiltonian is rotationally invariant,
linear momentum iff translationally invariant, energy iff time-translation
invariant (the special case `B = A` is `energy_conservation`).

The converse direction — commuting with the generator on its domain implies
commuting with `U(t)` — requires an ODE uniqueness argument and is deferred
to `Noether.lean`. -/
theorem conserved_quantity {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (B : H →L[ℂ] H)
    (hcomm : ∀ t ψ, B (U_grp.U t ψ) = U_grp.U t (B ψ))
    (ψ : H) (t : ℝ) :
    ⟪B (U_grp.U t ψ), U_grp.U t ψ⟫_ℂ = ⟪B ψ, ψ⟫_ℂ := by
  rw [hcomm t ψ, U_grp.unitary t (B ψ) ψ]


/-- **Expectation value continuity**: `t ↦ ⟨U(t)ψ, B(U(t)ψ)⟩` is continuous
for any bounded observable `B`. This is the topological counterpart to
Ehrenfest's differentiability result. -/
lemma expectation_value_continuous {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (B : H →L[ℂ] H)
    (ψ : H) :
    Continuous (fun t => ⟪U_grp.U t ψ, B (U_grp.U t ψ)⟫_ℂ) :=
  (U_grp.strong_continuous ψ).inner (B.continuous.comp (U_grp.strong_continuous ψ))


/-- **Conserved quantities have zero rate of change.**
If `B` commutes with `U(t)`, then `d/dt ⟨U(t)ψ, B(U(t)ψ)⟩ = 0`.

This is the bridge between `conserved_quantity` (the expectation value is constant)
and `ehrenfest_theorem` (the derivative has a commutator structure):
the Ehrenfest RHS vanishes precisely when `B` commutes with the evolution. -/
lemma conserved_quantity_deriv_zero {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H))
    (B : H →L[ℂ] H)
    (hcomm : ∀ t ψ, B (U_grp.U t ψ) = U_grp.U t (B ψ))
    (ψ : H) (t₀ : ℝ) :
    HasDerivAt (fun t => ⟪U_grp.U t ψ, B (U_grp.U t ψ)⟫_ℂ) 0 t₀ := by
  have hconst : ∀ t, ⟪U_grp.U t ψ, B (U_grp.U t ψ)⟫_ℂ = ⟪ψ, B ψ⟫_ℂ := by
    intro t
    rw [hcomm t ψ, U_grp.unitary t ψ (B ψ)]
  rw [show (fun t => ⟪U_grp.U t ψ, B (U_grp.U t ψ)⟫_ℂ) = fun _ => ⟪ψ, B ψ⟫_ℂ
    from funext hconst]
  exact hasDerivAt_const t₀ _


/-- Each `U(t)` as a continuous linear equivalence, with `U(-t)` as its inverse.
This bundling gives access to `.symm`, `.toHomeomorph`, and coercions in both
directions, making downstream composition ergonomic. -/
def unitaryEquiv{H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
   (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    H ≃L[ℂ] H where
  toFun := U_grp.U t
  invFun := U_grp.U (-t)
  left_inv := fun ψ => unitary_inversevariable U_grp ψ t
  right_inv := fun ψ => unitary_inverse_forward U_grp ψ t
  continuous_toFun := (U_grp.U t).continuous
  continuous_invFun := (U_grp.U (-t)).continuous
  map_smul' := by exact fun m x => ContinuousLinearMap.map_smul_of_tower (U_grp.U t) m x
  map_add' := by exact fun x y => ContinuousLinearMap.map_add (U_grp.U t) x y


@[simp]
theorem unitaryEquiv_apply {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (ψ : H) :
    unitaryEquiv U_grp t ψ = U_grp.U t ψ := rfl

@[simp]
theorem unitaryEquiv_symm {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    (unitaryEquiv U_grp t).symm = unitaryEquiv U_grp (-t) := by
  ext ψ
  rfl

@[simp]
theorem unitaryEquiv_trans {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U_grp : OneParameterUnitaryGroup (H := H)) (s t : ℝ) :
    (unitaryEquiv U_grp t).trans (unitaryEquiv U_grp s) = unitaryEquiv U_grp (s + t) := by
  ext ψ
  simp only [ContinuousLinearEquiv.trans_apply, unitaryEquiv_apply]
  rw [@OneParameterUnitaryGroup.group_law]
  exact Eq.symm (ContinuousLinearMap.comp_apply (U_grp.U s) (U_grp.U t) ψ)


end QuantumMechanics.UnitaryEvo
