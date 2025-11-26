/-
================================================================================
EXPONENTIAL OF SELF-ADJOINT OPERATORS VIA YOSIDA APPROXIMATION
================================================================================

For self-adjoint A with resolvent R(z) = (A - zI)⁻¹, we construct exp(itA)
without invoking the full spectral theorem.

Strategy:
  1. Yosida approximants A_n are bounded operators
  2. exp(itA_n) is well-defined via power series
  3. exp(itA) := s-lim_{n→∞} exp(itA_n)

Dependencies: Resolvent.lean (resolvent bounds, identity, surjectivity)
-/
import LogosLibrary.DeepTheorems.Quantum.Evolution.Stone.Resolvent
import LogosLibrary.DeepTheorems.Quantum.Uncertainty.Robertson.Theorem


namespace StonesTheorem.Exponential
open InnerProductSpace MeasureTheory Complex Filter Topology StonesTheorem.Resolvent Generator

open scoped BigOperators Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
================================================================================
SECTION 0: Helper Lemmas
================================================================================
The bounded approximants A_n = n²iR(ni) - nI converge strongly to A on D(A).
-/
/-- For n : ℕ+, the complex number I * n has nonzero imaginary part -/
lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
             zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero

/-- Variant for -I * n -/
lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, Complex.neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)

/-- The imaginary part of I * n equals n -/
lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [Complex.mul_im]

/-- The absolute value of the imaginary part -/
lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)

/-- Complex norm of n² where n : ℕ+ -/
lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  rw [norm_pow]
  simp

/-- Complex norm of I * n -/
lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  calc ‖I * (n : ℂ)‖
      = ‖I‖ * ‖(n : ℂ)‖ := norm_mul I (n : ℂ)
    _ = 1 * ‖(n : ℂ)‖ := by rw [Complex.norm_I]
    _ = ‖(n : ℂ)‖ := one_mul _
    _ = (n : ℝ) := by simp only [Complex.norm_natCast]

/-- Bundle the resolvent at I*n with its proof, for convenience -/
noncomputable def resolventAtIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

/-- And at -I*n -/
noncomputable def resolventAtNegIn
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

/-- Bound on the resolvent at I * n -/
lemma resolventAtIn_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖resolventAtIn gen hsa n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

/-- The resolvent R(z)φ is in the domain and satisfies (A - zI)(R(z)φ) = φ -/
lemma resolvent_spec
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    (resolvent gen z hz hsa φ) ∈ gen.domain ∧
    gen.op (resolvent gen z hz hsa φ) - z • (resolvent gen z hz hsa φ) = φ := by
  -- resolvent is defined via Classical.choose of self_adjoint_range_all_z
  -- The chosen element is a subtype {x : H // x ∈ gen.domain}
  -- Its .val is what resolvent returns, its .property gives domain membership
  let ψ_sub := Classical.choose (self_adjoint_range_all_z gen hsa z hz φ)
  have h_spec := (Classical.choose_spec (self_adjoint_range_all_z gen hsa z hz φ)).1
  -- ψ_sub.property : ψ_sub.val ∈ gen.domain
  -- h_spec : gen.op ψ_sub.val - z • ψ_sub.val = φ
  exact ⟨ψ_sub.property, h_spec⟩

/- Yosida approximant using the helper lemma for the imaginary part condition -/
noncomputable def yosidaApprox
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

noncomputable def yosidaJ
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (-I * (n : ℂ)) • resolventAtIn gen hsa n


/-- **Norm Bound on Yosida Approximants**

The bounded Yosida approximants `Aₙ = n² R(in) - in·I` satisfy the linear bound:

  `‖Aₙ‖ ≤ 2n`  for all `n ≥ 1`

**Proof:**

By the triangle inequality and resolvent bound `‖R(in)‖ ≤ 1/n`:
```
  ‖Aₙ‖ = ‖n² R(in) - in·I‖
       ≤ ‖n² R(in)‖ + ‖in·I‖
       = n² · ‖R(in)‖ + n · ‖I‖
       ≤ n² · (1/n) + n · 1
       = n + n = 2n
```

**Context:**

This bound shows that `Aₙ` are indeed bounded operators (unlike the original
unbounded `A`), but with norms growing linearly in `n`. This growth is acceptable
because:

1. For the exponential `exp(itAₙ)`, what matters is that each `Aₙ` is bounded,
   not the uniformity of bounds across `n`

2. The exponentials `exp(itAₙ)` will be unitary (norm 1) regardless of `‖Aₙ‖`,
   since `Aₙ` inherits a form of skew-adjointness from `A`

3. The convergence `Aₙ φ → Aφ` on the domain does not require uniform operator
   norm bounds, only pointwise convergence

**Comparison with `yosidaJ_norm_bound`:**

While `‖Jₙ‖ ≤ 1` is uniform, `‖Aₙ‖ ≤ 2n` grows. This reflects that `Jₙ` approximates
the bounded identity operator `I`, while `Aₙ` approximates the unbounded operator `A`.
-/
theorem yosidaApprox_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖yosidaApprox gen hsa n‖ ≤ 2 * (n : ℝ) := by
  -- Unfold definition: A_n = n² • R(I·n) - (I·n) • I
  unfold yosidaApprox

  -- First term bound: ‖n² • R(I·n)‖ ≤ n
  have h_first : ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ ≤ (n : ℝ) := by
    calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖
        = ‖(n : ℂ)^2‖ * ‖resolventAtIn gen hsa n‖ := norm_smul ((n : ℂ)^2) _
      _ ≤ ‖(n : ℂ)^2‖ * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (resolventAtIn_bound gen hsa n)
          exact norm_nonneg _
      _ = (n : ℝ)^2 * (1 / (n : ℝ)) := by rw [norm_pnat_sq]
      _ = (n : ℝ) := by field_simp

  -- Second term bound: ‖(I·n) • I‖ ≤ n
  have h_second : ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ ≤ (n : ℝ) := by
    calc ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
        = ‖I * (n : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ := norm_smul (I * (n : ℂ)) _
      _ ≤ ‖I * (n : ℂ)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
          exact norm_nonneg _
      _ = ‖I * (n : ℂ)‖ := mul_one _
      _ = (n : ℝ) := norm_I_mul_pnat n

  -- Combine via triangle inequality
  calc ‖(n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
      ≤ ‖(n : ℂ)^2 • resolventAtIn gen hsa n‖ + ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ :=
          norm_sub_le _ _
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add h_first h_second
    _ = 2 * (n : ℝ) := by ring

/-!
================================================================================
SECTION 0.6: J_n Convergence Lemmas
================================================================================
-/

/-- **Uniform Bound on Yosida's J Operator**

The auxiliary operators `Jₙ = -in · R(in)` are uniformly bounded by 1:

  `‖Jₙ‖ ≤ 1`  for all `n ≥ 1`

**Proof:**

Using the resolvent bound `‖R(in)‖ ≤ 1/|Im(in)| = 1/n`:
```
  ‖Jₙ‖ = ‖-in · R(in)‖ = |-in| · ‖R(in)‖ = n · ‖R(in)‖ ≤ n · (1/n) = 1
```

**Significance:**

This uniform bound is essential for:
1. The density argument in `yosida_J_tendsto_id` (controls `‖Jₙ(ψ - φ)‖`)
2. Ensuring the exponentials `exp(itAₙ)` remain well-behaved as `n → ∞`
3. Applying the Banach-Steinhaus theorem in related convergence arguments

The bound being exactly 1 (not just finite) reflects the fact that `Jₙ` are
"approximate identities" in the operator sense.
-/
lemma yosidaJ_norm_bound
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 := by
  -- First establish -I * n = -(I * n)
  have h_neg : (-I : ℂ) * (n : ℂ) = -(I * (n : ℂ)) := by ring

  -- Bound on the coefficient norm
  have h_coeff : ‖(-I * (n : ℂ))‖ = (n : ℝ) := by
    calc ‖(-I * (n : ℂ))‖
        = ‖-(I * (n : ℂ))‖ := by rw [h_neg]
      _ = ‖I * (n : ℂ)‖ := norm_neg _
      _ = (n : ℝ) := norm_I_mul_pnat n

  -- Bound on the resolvent norm
  have h_res : ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
        ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa _ _
      _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

  -- n > 0 as a real
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos

  -- Combine
  calc ‖(-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      = ‖(-I * (n : ℂ))‖ * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res
          exact le_of_lt hn_pos
    _ = 1 := by field_simp


/-- **Resolvent Identity for Yosida's J Operator**

For a self-adjoint generator `A` with domain `D(A)`, the auxiliary operator `Jₙ = -in · R(in)`
satisfies the fundamental identity:

  `Jₙ φ = φ - R(in)(Aφ)`  for all `φ ∈ D(A)`

where `R(z) = (A - zI)⁻¹` is the resolvent.

**Derivation:**

From the resolvent equation `(A - zI)R(z) = I`, applying both sides to `ψ ∈ H`:
  `(A - zI)R(z)ψ = ψ`

For `φ ∈ D(A)`, we can also write `R(z)(A - zI)φ = φ`, which gives:
  `R(z)(Aφ) - z · R(z)φ = φ`

Rearranging:
  `-z · R(z)φ = φ - R(z)(Aφ)`

With `z = in`, the left side is exactly `Jₙ φ`.

**Significance:**

This identity reveals that `Jₙ` measures the "defect" between the identity and the
composition `R(in) ∘ A`. Since `‖R(in)‖ ≤ 1/n` (see `resolventAtIn_bound`), for
`φ ∈ D(A)` we have:

  `‖Jₙ φ - φ‖ = ‖R(in)(Aφ)‖ ≤ (1/n) ‖Aφ‖ → 0`

This is the key estimate enabling `yosidaJ_tendsto_on_domain`.
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
  have hRφ_spec := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) φ -- Unknown identifier `resolvent_spec`
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

  -- Key: Show R(Aφ) = A(Rφ) - z·Rφ + z·R(Aφ)...
  -- Actually easier: show R(Aφ) = Rφ + z·R(Aφ) - z·Rφ... hmm

  -- Let's use: R((A - zI)φ) = φ for φ ∈ D(A)
  -- (A - zI)φ ∈ H, so R((A-zI)φ) is the unique ψ with (A-zI)ψ = (A-zI)φ
  -- By uniqueness, ψ = φ
  have h_R_AzI : R (gen.op φ - z • φ) = φ := by
    -- (A - zI)φ is in H, R inverts (A - zI)
    have h_target := gen.op φ - z • φ
    have h_φ_solves : gen.op φ - z • φ = gen.op φ - z • φ := rfl
    -- φ is in domain and solves (A - zI)x = (Aφ - zφ)
    -- R(Aφ - zφ) is THE solution, so by uniqueness R(Aφ - zφ) = φ
    have hspec := resolvent_spec gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op φ - z • φ)
    -- Use uniqueness from self_adjoint_range_all_z
    have h_unique := (Classical.choose_spec
        (self_adjoint_range_all_z gen hsa z (I_mul_pnat_im_ne_zero n) (gen.op φ - z • φ))).2
    have h_φ_works : gen.op φ - z • φ = gen.op φ - z • φ := rfl
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

  -- From R(Aφ - zφ) = φ, we get R(Aφ) - z·R(φ) = φ (by linearity of R... wait no)
  -- R is linear: R(Aφ - zφ) = R(Aφ) - R(zφ) = R(Aφ) - z·R(φ)
  have h_R_linear : R (gen.op φ - z • φ) = R (gen.op φ) - z • R φ := by
    calc R (gen.op φ - z • φ)
        = R (gen.op φ) - R (z • φ) := by rw [R.map_sub]
      _ = R (gen.op φ) - z • R φ := by rw [R.map_smul]

  -- So R(Aφ) - z·Rφ = φ, i.e., R(Aφ) = φ + z·Rφ
  have h_RAφ_explicit : R (gen.op φ) = φ + z • R φ := by
    calc R (gen.op φ)
        = R (gen.op φ) - z • R φ + z • R φ := by abel
      _ = R (gen.op φ - z • φ) + z • R φ := by rw [h_R_linear]
      _ = φ + z • R φ := by rw [h_R_AzI]

  -- Now compute J_n φ = (-z)·Rφ
  -- Want to show: (-z)·Rφ = φ - R(Aφ)
  -- From h_RAφ_explicit: R(Aφ) = φ + z·Rφ
  -- So φ - R(Aφ) = φ - (φ + z·Rφ) = -z·Rφ ✓
  calc (-I * (n : ℂ)) • R φ
      = (-z) • R φ := by rw [neg_mul]
    _ = -(z • R φ) := by rw [neg_smul]
    _ = φ - (φ + z • R φ) := by abel
    _ = φ - R (gen.op φ) := by rw [← h_RAφ_explicit]


/-- **Resolvent Identity for Yosida's J Operator**

For a self-adjoint generator `A` with domain `D(A)`, the auxiliary operator `Jₙ = -in · R(in)`
satisfies the fundamental identity:

  `Jₙ φ = φ - R(in)(Aφ)`  for all `φ ∈ D(A)`

where `R(z) = (A - zI)⁻¹` is the resolvent.

**Derivation:**

From the resolvent equation `(A - zI)R(z) = I`, applying both sides to `ψ ∈ H`:
  `(A - zI)R(z)ψ = ψ`

For `φ ∈ D(A)`, we can also write `R(z)(A - zI)φ = φ`, which gives:
  `R(z)(Aφ) - z · R(z)φ = φ`

Rearranging:
  `-z · R(z)φ = φ - R(z)(Aφ)`

With `z = in`, the left side is exactly `Jₙ φ`.

**Significance:**

This identity reveals that `Jₙ` measures the "defect" between the identity and the
composition `R(in) ∘ A`. Since `‖R(in)‖ ≤ 1/n` (see `resolventAtIn_bound`), for
`φ ∈ D(A)` we have:

  `‖Jₙ φ - φ‖ = ‖R(in)(Aφ)‖ ≤ (1/n) ‖Aφ‖ → 0`

This is the key estimate enabling `yosidaJ_tendsto_on_domain`.
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

  -- Need n large enough that (1/n)·‖Aφ‖ < ε
  -- If ‖Aφ‖ = 0, any n works. Otherwise need n > ‖Aφ‖/ε
  by_cases h_Aφ_zero : ‖gen.op φ‖ = 0
  · -- Case: Aφ = 0, so J_n φ = φ for all n
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

    -- Compute distance
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
            -- From h_n_bound: ‖gen.op φ‖/ε + 1 ≤ n, so ‖gen.op φ‖/ε < n
            have h_ratio_lt : ‖gen.op φ‖ / ε < (n : ℝ) := by linarith
            -- Therefore ‖gen.op φ‖ < n * ε
            have h_prod_lt : ‖gen.op φ‖ < (n : ℝ) * ε := by
              calc ‖gen.op φ‖
                  = (‖gen.op φ‖ / ε) * ε := by field_simp
                _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right h_ratio_lt hε
            -- Therefore ‖gen.op φ‖ / n < ε
            calc (1 / (n : ℝ)) * ‖gen.op φ‖
                = ‖gen.op φ‖ / (n : ℝ) := by ring
              _ = ‖gen.op φ‖ * (1 / (n : ℝ)) := by ring
              _ < ((n : ℝ) * ε) * (1 / (n : ℝ)) := by
                  apply mul_lt_mul_of_pos_right h_prod_lt
                  exact one_div_pos.mpr hn_pos
              _ = ε := by field_simp
/-!
================================================================================
SECTION 1: Yosida Approximation
================================================================================
-/
/-- **Strong Convergence of Yosida's J Operator to Identity**

For a self-adjoint generator `A`, the auxiliary operators `Jₙ = -in · R(in)` converge
strongly to the identity:

  `Jₙ ψ → ψ`  as `n → ∞`  for all `ψ ∈ H`

**Proof Strategy:**

The proof proceeds in two stages:

1. **Convergence on `D(A)`** (`yosidaJ_tendsto_on_domain`):
   For `φ ∈ D(A)`, using `yosidaJ_eq_sub_resolvent_A`:
```
   ‖Jₙ φ - φ‖ = ‖R(in)(Aφ)‖ ≤ ‖R(in)‖ · ‖Aφ‖ ≤ (1/n) · ‖Aφ‖ → 0
```

2. **Extension to all of `H`** (density argument):
   For arbitrary `ψ ∈ H` and `ε > 0`:
   - By `gen.dense_domain`, choose `φ ∈ D(A)` with `‖ψ - φ‖ < ε/3`
   - By stage 1, choose `N` such that `n ≥ N ⟹ ‖Jₙ φ - φ‖ < ε/3`
   - Using `‖Jₙ‖ ≤ 1` (see `yosidaJ_norm_bound`):
```
   ‖Jₙ ψ - ψ‖ ≤ ‖Jₙ(ψ - φ)‖ + ‖Jₙ φ - φ‖ + ‖φ - ψ‖
              ≤ 1 · ‖ψ - φ‖ + ε/3 + ‖ψ - φ‖
              < ε/3 + ε/3 + ε/3 = ε
```

**Role in Stone's Theorem:**

This convergence, combined with `yosidaApprox_eq_J_comp_A`, yields strong convergence
of the Yosida approximants to `A` on domain elements:

  `Aₙ φ = Jₙ(Aφ) → Aφ`  for all `φ ∈ D(A)`

The uniform bound `‖Jₙ‖ ≤ 1` is also crucial for controlling the exponentials
`exp(itAₙ)` and passing to the limit.
-/
theorem yosida_J_tendsto_id
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) :
    Tendsto (fun n : ℕ+ => (-I * (n : ℂ)) •
              resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa ψ)
            atTop (𝓝 ψ) := by
  -- Abbreviate for clarity
  let J : ℕ+ → H →L[ℂ] H := fun n =>
    (-I * (n : ℂ)) • resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

  -- Use density argument: D(A) is dense, J_n bounded, J_n → I on D(A)
  rw [Metric.tendsto_atTop]
  intro ε hε

  -- Step 1: Approximate ψ by domain element φ
  have h_dense := gen.dense_domain
  obtain ⟨φ, hφ_mem, hφ_close⟩ := Metric.mem_closure_iff.mp (h_dense.closure_eq ▸ Set.mem_univ ψ)
                                    (ε / 3) (by linarith)

  -- Step 2: Get N such that J_n φ is close to φ for n ≥ N
  have h_domain_conv := yosidaJ_tendsto_on_domain gen hsa φ hφ_mem
  rw [Metric.tendsto_atTop] at h_domain_conv
  obtain ⟨N, hN⟩ := h_domain_conv (ε / 3) (by linarith)

  -- Step 3: For n ≥ N, J_n ψ is close to ψ
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


/-- **Yosida Approximant as Composition Identity**

For a self-adjoint generator `A` with domain `D(A)`, the Yosida approximant `Aₙ` acts on
domain elements as the composition `Jₙ ∘ A`:

  `Aₙ φ = Jₙ(Aφ)`  for all `φ ∈ D(A)`

where:
- `Aₙ = n² R(in) - in·I` is the bounded Yosida approximant
- `Jₙ = -in · R(in)` is the auxiliary operator converging strongly to identity
- `R(z) = (A - zI)⁻¹` is the resolvent

**Mathematical Derivation:**

Starting from the resolvent equation `(A - zI)R(z) = I`, we have for `φ ∈ D(A)`:
  `Jₙ φ = φ - R(in)(Aφ)`

Rearranging: `R(in)(Aφ) = φ + in · R(in)φ`

Therefore:
```
  Jₙ(Aφ) = -in · R(in)(Aφ)
         = -in · (φ + in · R(in)φ)
         = -in · φ + n² · R(in)φ      [since (-in)(in) = n²]
         = Aₙ φ
```

**Role in Stone's Theorem:**

This identity is essential for proving that `Aₙ → A` strongly on `D(A)`. Combined with
`Jₙ → I` strongly (see `yosida_J_tendsto_id`), we obtain:

  `Aₙ φ = Jₙ(Aφ) → I(Aφ) = Aφ`  for all `φ ∈ D(A)`

This convergence of bounded operators to the unbounded generator is the heart of the
Yosida approximation method, allowing construction of `exp(itA)` as the strong limit
of the well-defined exponentials `exp(itAₙ)`.
-/
theorem yosidaApprox_eq_J_comp_A (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) (φ : H) (hφ : φ ∈ gen.domain) :
    yosidaApprox gen hsa n φ = yosidaJ gen hsa n (gen.op φ) := by
  -- Get the key identity: J_n φ = φ - R(in)(Aφ)
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


/-- **Strong Convergence of Yosida Approximants on Domain**

For a self-adjoint generator `A` with domain `D(A)`, the bounded Yosida approximants
`Aₙ = n² R(in) - in·I` converge strongly to `A` on domain elements:

  `Aₙ φ → Aφ`  as `n → ∞`  for all `φ ∈ D(A)`

**Proof:**

This is an immediate consequence of two previously established results:

1. `yosidaApprox_eq_J_comp_A`: On the domain, `Aₙ φ = Jₙ(Aφ)`
2. `yosida_J_tendsto_id`: The operators `Jₙ → I` strongly

Combining these:
```
  Aₙ φ = Jₙ(Aφ) → I(Aφ) = Aφ
```

**Role in Stone's Theorem:**

This convergence is the central approximation result of the Yosida method. It shows
that the unbounded self-adjoint operator `A` can be approximated by bounded operators
`Aₙ` in the strong sense on its domain.

The bounded approximants `Aₙ` have well-defined exponentials `exp(itAₙ)` (via power
series), and this domain convergence—combined with uniform estimates—allows us to
define `exp(itA)` as the strong limit of `exp(itAₙ)`.

Note: Convergence holds only on `D(A)`, not on all of `H`. This is expected since
`Aφ` is only defined for `φ ∈ D(A)`. The extension to the unitary group on all of
`H` comes from the uniform boundedness of `exp(itAₙ)` as unitary operators.
-/
theorem yosidaApprox_tendsto_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) (hψ : ψ ∈ gen.domain) :
    Tendsto (fun n : ℕ+ => yosidaApprox gen hsa n ψ) atTop (𝓝 (gen.op ψ)) := by
  -- A_n ψ = J_n(Aψ)  by yosidaApprox_eq_J_comp_A
  -- J_n(Aψ) → Aψ     by yosida_J_tendsto_id applied to (gen.op ψ)
  simp only [fun n => yosidaApprox_eq_J_comp_A gen hsa n ψ hψ]
  exact yosida_J_tendsto_id gen hsa (gen.op ψ)


/-- **Yosida Approximants Commute with Resolvent**

The bounded Yosida approximants `Aₙ = n² R(in) - in·I` commute with the resolvent
`R(z) = (A - zI)⁻¹` for any `z` with non-zero imaginary part:

  `Aₙ ∘ R(z) = R(z) ∘ Aₙ`

**Proof:**

Since `Aₙ = n² R(in) - in·I`, commutativity reduces to showing that resolvents
at different spectral points commute: `R(in) ∘ R(z) = R(z) ∘ R(in)`.

From the resolvent identity:
  `R(w₁) - R(w₂) = (w₁ - w₂) • R(w₁) ∘ R(w₂) = (w₁ - w₂) • R(w₂) ∘ R(w₁)`

we obtain `R(w₁) ∘ R(w₂) = R(w₂) ∘ R(w₁)` for all valid spectral parameters.

**Role in Stone's Theorem:**

This commutativity extends to the exponentials: `exp(itAₙ)` commutes with `R(z)`.
This ensures that `exp(itAₙ)` preserves the domain `D(A)` and that the limiting
semigroup `exp(itA)` interacts properly with the generator.
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
    · -- If in = z, trivially commute
      have hz' : (I * (n : ℂ)).im ≠ 0 := I_mul_pnat_im_ne_zero n
      -- Need to show the two resolvents are equal, then comp trivially commutes
      have h_res_eq : resolvent gen (I * (n : ℂ)) hz' hsa = resolvent gen z hz hsa := by
        subst h_eq
        congr
      rw [h_res_eq]
    · -- If in ≠ z, use resolvent identity to show commutativity
      have h_diff_ne : I * (n : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_eq
      have h_diff_ne' : z - I * (n : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_eq)
      -- Get both forms of the resolvent identity
      have h_id1 := resolvent_identity gen hsa (I * (n : ℂ)) z (I_mul_pnat_im_ne_zero n) hz
      have h_id2 := resolvent_identity gen hsa z (I * (n : ℂ)) hz (I_mul_pnat_im_ne_zero n)
      -- h_id1: R(in) - R(z) = (in - z) • R(in) ∘ R(z)
      -- h_id2: R(z) - R(in) = (z - in) • R(z) ∘ R(in)
      -- From h_id1: R(in) ∘ R(z) = (in - z)⁻¹ • (R(in) - R(z))
      have h1 : (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa).comp (resolvent gen z hz hsa) =
                (I * (n : ℂ) - z)⁻¹ • (resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa - resolvent gen z hz hsa) := by
        -- h_id1 : R(in) - R(z) = (in - z) • (R(in) ∘ R(z))
        -- So (in - z)⁻¹ • (R(in) - R(z)) = R(in) ∘ R(z)
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
  simp only [resolventAtIn] at h_resolvent_comm  -- unfold in hypothesis too
  rw [h_resolvent_comm]


/-!
================================================================================
SECTION 2: Exponential of Bounded Operators
================================================================================

For bounded B, exp(tB) is defined by the norm-convergent power series.
This is standard but we need it explicitly.
-/

/-- **Exponential of a Bounded Operator**

For a bounded linear operator `B : H →L[ℂ] H` and time parameter `t : ℝ`, defines the
operator exponential via the norm-convergent power series:

  `exp(tB) = ∑_{k=0}^∞ (tB)^k / k!`

**Convergence:**

The series converges absolutely in operator norm for any bounded `B` and any `t ∈ ℝ`.
This follows from the estimate:

  `‖(tB)^k / k!‖ ≤ (|t| · ‖B‖)^k / k!`

and the convergence of `∑ x^k / k! = eˣ` for all `x ∈ ℝ`.

**Properties (proved separately):**
- `exp(0·B) = I` (identity at t=0)
- `exp((s+t)B) = exp(sB) · exp(tB)` (semigroup law)
- `d/dt[exp(tB)] = B · exp(tB)` (derivative recovers generator)
- If `B` is skew-adjoint (`B* = -B`), then `exp(tB)` is unitary

**Role in Stone's Theorem:**

The Yosida approximants `Aₙ` are bounded, so `exp(itAₙ)` is well-defined via this
power series. The unitary group `exp(itA)` for unbounded self-adjoint `A` is then
constructed as the strong limit of `exp(itAₙ)`.

**Implementation:**

Uses Mathlib's `NormedSpace.exp` for Banach algebras, instantiated on the normed
algebra `H →L[ℂ] H` of bounded operators.
-/
noncomputable def expBounded (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' (k : ℕ), (1 / k.factorial : ℂ) • ((t : ℂ) • B) ^ k


/-- **Semigroup Law for Bounded Operator Exponential**

The exponential of bounded operators satisfies the semigroup law:

  `exp((s + t)B) = exp(sB) ∘ exp(tB)`

**Proof Sketch:**

Since `sB` and `tB` commute (both are scalar multiples of `B`), we can apply the
Cauchy product formula for absolutely convergent power series:
```
  exp(sB) · exp(tB) = (∑_j (sB)^j / j!) · (∑_k (tB)^k / k!)
                    = ∑_n ∑_{j+k=n} (sB)^j (tB)^k / (j! k!)
                    = ∑_n (B^n / n!) · ∑_{j=0}^n C(n,j) s^j t^{n-j}
                    = ∑_n ((s+t)B)^n / n!                          [binomial theorem]
                    = exp((s+t)B)
```

**Role in Stone's Theorem:**

This law ensures that `t ↦ exp(itAₙ)` forms a one-parameter group for each
bounded approximant `Aₙ`. The group law passes to the strong limit, giving
the group law for `exp(itA)`.
-/
theorem expBounded_group_law (B : H →L[ℂ] H) (s t : ℝ) :
    expBounded B (s + t) = (expBounded B s).comp (expBounded B t) := by
  sorry


/-- Exponential norm bound -/
theorem expBounded_norm_bound (B : H →L[ℂ] H) (t : ℝ) :
    ‖expBounded B t‖ ≤ Real.exp (|t| * ‖B‖) := by
  sorry

/-!
================================================================================
SECTION 3: Exponential of Unbounded Self-Adjoint Operators
================================================================================

exp(itA) := s-lim_{n→∞} exp(itA_n) where A_n is the Yosida approximant.
-/

/-- The exponential of itA via Yosida approximation -/
noncomputable def exponential
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : IsSelfAdjoint gen)
    (t : ℝ) : H →L[ℂ] H :=
  sorry -- Strong limit of expBounded (yosidaApprox gen hsa n) t

/-- Convergence of the Yosida exponentials -/
theorem exponential_is_strong_limit
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (t : ℝ) (ψ : H) :
    Tendsto (fun n : ℕ+ => expBounded (yosidaApprox gen hsa n) t ψ)
            atTop
            (𝓝 (exponential gen hsa t ψ)) := by
  sorry

/-!
================================================================================
SECTION 4: Properties of the Exponential
================================================================================
-/

/-- The exponential is unitary -/
theorem exponential_unitary
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (t : ℝ) (ψ φ : H) :
    ⟪exponential gen hsa t ψ, exponential gen hsa t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  sorry

/-- The exponential satisfies the group law -/
theorem exponential_group_law
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (s t : ℝ) :
    (exponential gen hsa s).comp (exponential gen hsa t) = exponential gen hsa (s + t) := by
  sorry

/-- The exponential at zero is the identity -/
theorem exponential_identity
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    exponential gen hsa 0 = ContinuousLinearMap.id ℂ H := by
  sorry

/-- The exponential is strongly continuous -/
theorem exponential_strong_continuous
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (ψ : H) : Continuous (fun t : ℝ => exponential gen hsa t ψ) := by
  sorry

/-!
================================================================================
SECTION 5: The Generator of exp(itA) is A
================================================================================

The critical link: differentiating exp(itA) recovers A.
-/

/-- On domain elements, d/dt[exp(itA)ψ] = iA·exp(itA)ψ -/
theorem exponential_derivative_on_domain
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (t : ℝ) (ψ : H) (hψ : ψ ∈ gen.domain) :
    HasDerivAt (fun s : ℝ => exponential gen hsa s ψ)
               (I • gen.op (exponential gen hsa t ψ))
               t := by
  sorry

/-- The generator of t ↦ exp(itA) is exactly A -/
theorem exponential_generator_eq
    {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint) :
    ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
      Tendsto (fun t : ℝ => (I * t)⁻¹ • (exponential gen hsa t ψ - ψ))
              (𝓝[≠] 0)
              (𝓝 (gen.op ψ)) := by
  sorry


end StonesTheorem.Exponential
