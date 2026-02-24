/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.SpecialCases
import LogosLibrary.QuantumMechanics.UnitaryEvo.Resolvent.LowerBound
/-!
# Closedness of the Range of (A - zI)

This file proves that for a self-adjoint generator `A` and any `z` with
`Im(z) ≠ 0`, the range of `(A - zI)` is closed.

The key insight is the lower bound `|Im(z)| · ‖ψ‖ ≤ ‖(A - zI)ψ‖`, which
implies that preimages of Cauchy sequences are Cauchy. The limit is shown
to lie in the domain by routing through `R(i)`.

## Main results

* `preimage_cauchySeq`: Preimages of Cauchy sequences under `(A - zI)` are Cauchy
* `range_limit_mem`: Sequential limits of range elements are in the range
* `range_sub_smul_closed`: The range of `(A - zI)` is closed

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology QuantumMechanics.Bochner QuantumMechanics.Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-! ### Step 2: Range is closed -/

/-- Preimages of Cauchy sequences under (A - zI) are Cauchy when Im(z) ≠ 0. -/
lemma preimage_cauchySeq {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (z : ℂ) (hz : z.im ≠ 0)
    (ψ_seq : ℕ → gen.domain)
    (hu_cauchy : CauchySeq (fun n => gen.op (ψ_seq n) - z • (ψ_seq n : H))) :
    CauchySeq (fun n => (ψ_seq n : H)) := by
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
                z • ((ψ_seq m : H) - (ψ_seq n : H)) =
                (gen.op (ψ_seq m) - z • (ψ_seq m : H)) - (gen.op (ψ_seq n) - z • (ψ_seq n : H)) := by
    have op_sub := gen.op.map_sub (ψ_seq m) (ψ_seq n)
    have op_eq : gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ =
                 gen.op (ψ_seq m) - gen.op (ψ_seq n) := by
      convert op_sub using 1
    calc gen.op ⟨(ψ_seq m : H) - (ψ_seq n : H), h_sub_mem⟩ -
        z • ((ψ_seq m : H) - (ψ_seq n : H))
        = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - z • ((ψ_seq m : H) - (ψ_seq n : H)) :=
            by rw [op_eq]
      _ = (gen.op (ψ_seq m) - gen.op (ψ_seq n)) - (z • (ψ_seq m : H) - z • (ψ_seq n : H)) := by
          rw [smul_sub]
      _ = (gen.op (ψ_seq m) - z • (ψ_seq m : H)) - (gen.op (ψ_seq n) - z • (ψ_seq n : H)) :=
          by abel
  rw [h_diff] at h_bound
  have h_ubound : dist ((gen.op (ψ_seq m) - z • (ψ_seq m : H)))
                       ((gen.op (ψ_seq n) - z • (ψ_seq n : H))) < |z.im| * ε := hN m hm n hn
  rw [dist_eq_norm] at h_ubound
  have h_chain : |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖ < |z.im| * ε := by
    calc |z.im| * ‖(ψ_seq m : H) - (ψ_seq n : H)‖
        ≤ ‖(gen.op (ψ_seq m) - z • (ψ_seq m : H)) -
           (gen.op (ψ_seq n) - z • (ψ_seq n : H))‖ := h_bound
      _ < |z.im| * ε := h_ubound
  have h_pos : 0 < |z.im| := abs_pos.mpr hz
  rw [dist_eq_norm]
  exact (mul_lt_mul_left h_pos).mp h_chain

/-- The limit of a convergent sequence in ran(A - zI) is in ran(A - zI). -/
lemma range_limit_mem {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (_ /-hz-/ : z.im ≠ 0)
    (ψ_seq : ℕ → gen.domain) (φ_lim : H)
    (hψ_seq : ∀ n, gen.op (ψ_seq n) - z • (ψ_seq n : H) = φ_lim)
    (hψ_lim : ∃ ψ_lim, Tendsto (fun n => (ψ_seq n : H)) atTop (𝓝 ψ_lim)) :
    ∃ (ψ : gen.domain), gen.op ψ - z • (ψ : H) = φ_lim := by
  obtain ⟨ψ_lim, hψ_tendsto⟩ := hψ_lim
  let R := resolvent_at_i gen hsa
  have h_AiI_lim : Tendsto (fun n => gen.op (ψ_seq n) - I • (ψ_seq n : H))
                          atTop (𝓝 (φ_lim + (z - I) • ψ_lim)) := by
    have h1 : Tendsto (fun n => gen.op (ψ_seq n) - z • (ψ_seq n : H)) atTop (𝓝 φ_lim) := by
      simp only [hψ_seq]
      exact tendsto_const_nhds
    have h2 : Tendsto (fun n => (z - I) • (ψ_seq n : H)) atTop (𝓝 ((z - I) • ψ_lim)) :=
      Tendsto.const_smul hψ_tendsto (z - I)
    have h3 := Tendsto.add h1 h2
    have h_eq : ∀ n, gen.op (ψ_seq n) - I • (ψ_seq n : H) =
                (gen.op (ψ_seq n) - z • (ψ_seq n : H)) + (z - I) • (ψ_seq n : H) := fun n => by
      simp only [sub_smul]; abel
    exact h3.congr (fun n => (h_eq n).symm)
  have h_R_inverse : ∀ (ψ : H) (hψ : ψ ∈ gen.domain),
                      R (gen.op ⟨ψ, hψ⟩ - I • ψ) = ψ := fun ψ hψ =>
    resolvent_at_i_unique gen hsa _ (R _) ψ (resolvent_solution_mem gen hsa _) hψ
      (resolvent_solution_eq gen hsa _) rfl
  have h_R_lim : Tendsto (fun n => R (gen.op (ψ_seq n) - I • (ψ_seq n : H)))
                        atTop (𝓝 (R (φ_lim + (z - I) • ψ_lim))) :=
    R.continuous.tendsto _ |>.comp h_AiI_lim
  have h_R_eq : ∀ n, R (gen.op (ψ_seq n) - I • (ψ_seq n : H)) = (ψ_seq n : H) := fun n =>
    h_R_inverse (ψ_seq n : H) (ψ_seq n).property
  have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop
      (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := h_R_lim.congr (fun n => (h_R_eq n))
  have h_ψ_lim_eq : ψ_lim = R (φ_lim + (z - I) • ψ_lim) :=
    tendsto_nhds_unique hψ_tendsto h_ψ_lim_alt
  have h_ψ_lim_domain : ψ_lim ∈ gen.domain := by
    rw [h_ψ_lim_eq]
    exact resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)
  refine ⟨⟨ψ_lim, h_ψ_lim_domain⟩, ?_⟩
  have h_AiI_ψ_lim := resolvent_solution_eq gen hsa (φ_lim + (z - I) • ψ_lim)
  have h_op_eq : gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ =
                 gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                        resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ := by
    congr 1
    exact Subtype.ext h_ψ_lim_eq
  calc gen.op ⟨ψ_lim, h_ψ_lim_domain⟩ - z • ψ_lim
      = gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
              resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
      z • R (φ_lim + (z - I) • ψ_lim) := by
        rw [h_op_eq]
        exact
          congrArg
            (HSub.hSub
              (gen.op
                ⟨R (φ_lim + (z - I) • ψ_lim),
                  resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩))
            (congrArg (HSMul.hSMul z) h_ψ_lim_eq)
    _ = (gen.op ⟨R (φ_lim + (z - I) • ψ_lim),
                resolvent_solution_mem gen hsa (φ_lim + (z - I) • ψ_lim)⟩ -
        I • R (φ_lim + (z - I) • ψ_lim)) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
        simp only [sub_smul]; abel
    _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
      exact congrFun (congrArg HSub.hSub h_AiI_ψ_lim) ((z - I) • R (φ_lim + (z - I) • ψ_lim))
    _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
    _ = φ_lim := by abel


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The range of (A - zI) is closed. -/
lemma range_sub_smul_closed {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) (hsa : Generator.IsSelfAdjoint gen)
    (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed (Set.range (fun (ψ : gen.domain) => gen.op ψ - z • (ψ : H))) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u φ_lim hu_range hφ_lim
  have hu_cauchy : CauchySeq u := hφ_lim.cauchySeq
  choose ψ_seq hψ_seq using fun n => Set.mem_range.mp (hu_range n)
  have hψ_cauchy : CauchySeq (fun n => (ψ_seq n : H)) := by
    have hu_cauchy' : CauchySeq (fun n => gen.op (ψ_seq n) - z • (ψ_seq n : H)) := by
      convert hu_cauchy using 1
      ext n
      exact hψ_seq n
    exact preimage_cauchySeq gen z hz ψ_seq hu_cauchy'
  obtain ⟨ψ_lim, hψ_lim⟩ := cauchySeq_tendsto_of_complete hψ_cauchy
  -- Now we need to show φ_lim is in the range
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
  have h_ψ_lim_alt : Tendsto (fun n => (ψ_seq n : H)) atTop
      (𝓝 (R (φ_lim + (z - I) • ψ_lim))) := by
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
                        I • R (φ_lim + (z - I) • ψ_lim) +
                        (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          rw [← add_smul]; congr 1; ring
        rw [hz_split]
        abel
      _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • R (φ_lim + (z - I) • ψ_lim) := by
          rw [h_AiI_ψ_lim]
      _ = (φ_lim + (z - I) • ψ_lim) - (z - I) • ψ_lim := by rw [← h_ψ_lim_eq]
      _ = φ_lim := by abel
  exact ⟨⟨ψ_lim, h_ψ_lim_domain⟩, h_eq⟩
