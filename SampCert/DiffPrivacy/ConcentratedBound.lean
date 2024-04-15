/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.GaussBound
import SampCert.DiffPrivacy.GaussConvergence
import SampCert.DiffPrivacy.GaussPeriodicity

open Real

noncomputable def RenyiDivergence (p q : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (∑' x : ℤ, (p x)^α  * (q x)^(1 - α))

theorem RenyiDivergenceBound (μ : ℤ) (ss : ℝ) (h : ss > 0) (h' : α > 1) :
  RenyiDivergence (fun (x : ℝ) => sg' ss μ x / ∑' x : ℤ, sg' ss μ x)
                  (fun (x : ℝ) => sg' ss (0 : ℤ) x / ∑' x : ℤ, sg' ss (0 : ℤ) x)
                  α ≤ α * (μ^2 / (2 * ss)) := by
  unfold RenyiDivergence
  have A : 0 < 1 / (α - 1) := by
    simp [h']
  rw [← le_div_iff' A]
  refine Real.exp_le_exp.mp ?_
  rw [exp_log]
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ sg' ss μ x := sorry
  have B' : ∀ x : ℝ, 0 ≤ sg' ss 0 x := sorry
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), sg' ss μ x)⁻¹ := sorry
  have C' : 0 ≤ (∑' (x : ℤ), sg' ss 0 x)⁻¹ := sorry
  have D : 0 < (∑' (x : ℤ), sg' ss 0 x)⁻¹ := sorry
  . -- First, I work on the denominator
    conv =>
      left
      ring_nf
      right
      intro x
      rw [mul_rpow (B μ x) (C μ)]
      rw [mul_rpow (B' x) C']
    rw [SG_periodic' _ _ h]
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      rw [← mul_assoc]
      left
      rw [mul_comm]
    have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      right
      rw [X]
      rw [rpow_add D]
      rw [mul_comm]
      rw [mul_assoc]
      simp
      right
      rw [← rpow_add D]
      simp
    simp
    conv =>
      left
      right
      intro x
      rw [← mul_assoc]
    rw [tsum_mul_right]
    rw [← division_def]
    -- Now, I work on the numerator
    conv =>
      left
      left
      unfold sg'
      right
      intro x
      rw [← Real.exp_mul]
      rw [← Real.exp_mul]
      rw [← exp_add]
      rw [← mul_div_right_comm]
      rw [← mul_div_right_comm]
      rw [div_add_div_same]
      rw [mul_sub_left_distrib]
      right
      left
      simp
      ring_nf
    sorry
  . sorry
