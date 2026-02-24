/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import LogosLibrary.QuantumMechanics.BellsTheorem.QuantumCHSH.Violation
import LogosLibrary.QuantumMechanics.BellsTheorem.CHSH_bounds.TsirelsonClassical

open Matrix Complex MatrixGroups QuantumInfo
namespace QuantumCHSH


/-- **Tsirelson's Bound**: No quantum state can achieve |S| > 2√2.

The proof uses S² = 4I - [A₀,A₁]·[B₀,B₁] and operator norm bounds. -/
theorem tsirelson_bound' {n : ℕ} [NeZero n]
    (A₀' A₁' B₀' B₁' : Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : A₀'.IsHermitian) (hA₁ : A₁'.IsHermitian)
    (hB₀ : B₀'.IsHermitian) (hB₁ : B₁'.IsHermitian)
    (hA₀_sq : A₀' * A₀' = 1) (hA₁_sq : A₁' * A₁' = 1)
    (hB₀_sq : B₀' * B₀' = 1) (hB₁_sq : B₁' * B₁' = 1)
    (hcomm₀₀ : A₀' * B₀' = B₀' * A₀') (hcomm₀₁ : A₀' * B₁' = B₁' * A₀')
    (hcomm₁₀ : A₁' * B₀' = B₀' * A₁') (hcomm₁₁ : A₁' * B₁' = B₁' * A₁')
    (ρ : DensityMatrix n) :
    ‖(((A₀' * B₁' - A₀' * B₀' + A₁' * B₀' + A₁' * B₁') * ρ.toMatrix).trace)‖
      ≤ 2 * Real.sqrt 2 := by
  let hT : QuantumInfo.IsCHSHTuple A₀' A₁' B₀' B₁' := {
    A₀_herm := hA₀
    A₁_herm := hA₁
    B₀_herm := hB₀
    B₁_herm := hB₁
    A₀_sq := hA₀_sq
    A₁_sq := hA₁_sq
    B₀_sq := hB₀_sq
    B₁_sq := hB₁_sq
    comm_A₀_B₀ := hcomm₀₀
    comm_A₀_B₁ := hcomm₀₁
    comm_A₁_B₀ := hcomm₁₀
    comm_A₁_B₁ := hcomm₁₁
  }
  have h := tsirelson_bound A₀' A₁' B₀' B₁' hT ρ
  simp only [CHSH_expect, CHSH_op] at h
  convert h using 2
