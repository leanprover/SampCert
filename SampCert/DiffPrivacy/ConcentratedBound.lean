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

theorem sg_sum_pos (μ : ℤ) (ss : ℝ) (h : ss > 0) :
  0 < (∑' (x : ℤ), sg' ss μ x) := by
  unfold sg'
  apply tsum_pos (GaussConvergence _ _ h) _ 0
  . apply exp_pos
  . intro i
    apply exp_nonneg

-- rw [inv_pos] to get result for inverse

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
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ sg' ss μ x := by
    intro μ x
    unfold sg'
    apply exp_nonneg
  have B' : ∀ x : ℝ, 0 ≤ sg' ss 0 x := by
    unfold sg'
    intro x
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), sg' ss μ x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sg_sum_pos _ _ h
  have C' : 0 ≤ (∑' (x : ℤ), sg' ss 0 x)⁻¹ := by
    rw [inv_nonneg]
    apply le_of_lt
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos _ _ h
  have D : 0 < (∑' (x : ℤ), sg' ss 0 x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos _ _ h
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
    have E : ∀ x : ℤ, x * μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = - (x - α * μ)^2 + α * (α -1) * μ^2 := by
      intro x
      ring_nf
    conv =>
      left
      left
      right
      intro x
      rw [E]
      rw [add_div]
      rw [exp_add]
    rw [tsum_mul_right]
    rw [mul_comm]
    rw [mul_div_assoc]
    have F := SGBound ss (α * μ) h
    unfold sg'
    unfold sg' at F
    clear A B B' C C' D X E
    have X : 0 < ∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * ss)) := by
      conv =>
        right
        rw [← Int.cast_zero]
      apply sg_sum_pos _ _ h
    have G := @div_le_one ℝ _ (∑' (x : ℤ), rexp (-(↑x - α * ↑μ) ^ 2 / (2 * ss))) (∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * ss)))
    replace G := (G X).2 F
    clear X F
    conv =>
      right
      rw [← mul_rotate]
      right
      left
      rw [mul_comm]
    conv =>
      right
      rw [← mul_div_assoc]
    apply mul_le_of_le_one_right _ G
    apply exp_nonneg
  . sorry
