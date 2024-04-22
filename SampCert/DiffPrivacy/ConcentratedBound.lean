/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DiffPrivacy.DiscreteGaussian
import SampCert.DiffPrivacy.GaussBound
import SampCert.DiffPrivacy.GaussConvergence
import SampCert.DiffPrivacy.GaussPeriodicity
import SampCert.Util.Shift

open Real

noncomputable def RenyiDivergence (p q : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (∑' x : ℤ, (p x)^α  * (q x)^(1 - α))

theorem sg_sum_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  0 < (∑' (x : ℤ), (gauss_term_ℝ σ μ) x) := by
  unfold gauss_term_ℝ
  apply tsum_pos (summable_gauss_term' h μ) _ 0
  . apply exp_pos
  . intro i
    apply exp_nonneg

theorem sg_sum_pos' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (α : ℝ)  :
  0 < ((gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x)^α := by
  apply rpow_pos_of_pos
  rw [div_pos_iff]
  left
  constructor
  . apply exp_pos
  . apply sg_sum_pos h

theorem SG_Renyi_simplify {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) :
  (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x) x ^ α *
      (fun (x : ℤ) => (gauss_term_ℝ σ ν) x / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x) x ^ (1 - α)
    = (gauss_term_ℝ σ μ) x ^ α * (gauss_term_ℝ σ ν) x ^ (1 - α) / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x := by
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sg_sum_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos h
  simp
  conv =>
    left
    ring_nf
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  rw [SG_periodic' h]
  rw [SG_periodic' h]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
  conv =>
    left
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
    rw [← mul_assoc]


theorem RenyiDivergenceBound {σ : ℝ} (h : σ ≠ 0) (μ : ℤ) (α : ℝ) (h' : α > 1) :
  RenyiDivergence (fun (x : ℝ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x)
                  (fun (x : ℝ) => (gauss_term_ℝ σ (0 : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ (0 : ℤ)) x)
                  α ≤ α * (μ^2 / (2 * σ^2)) := by
  unfold RenyiDivergence
  have A : 0 < 1 / (α - 1) := by
    simp [h']
  rw [← le_div_iff' A]
  refine Real.exp_le_exp.mp ?_
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have B' : ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ 0) x := by
    unfold gauss_term_ℝ
    intro x
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sg_sum_pos h
  have C' : 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_nonneg]
    apply le_of_lt
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos h
  rw [exp_log]
  . conv =>
      left
      ring_nf
      right
      intro x
      rw [mul_rpow (B μ x) (C μ)]
      rw [mul_rpow (B' x) C']
    -- First, I work on the denominator
    rw [SG_periodic' h]
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
      unfold gauss_term_ℝ
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
    have F := sum_gauss_term_bound h (α * μ)
    unfold gauss_term_ℝ
    unfold gauss_term_ℝ at F
    --clear A B B' C C' D X E
    have X : 0 < ∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)) := by
      conv =>
        right
        rw [← Int.cast_zero]
      apply sg_sum_pos h
    have G := @div_le_one ℝ _ (∑' (x : ℤ), rexp (-(↑x - α * ↑μ) ^ 2 / (2 * σ^2))) (∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)))
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
  . apply tsum_pos _ _ 0 _
    . simp -- some of this proof is similar to the one just above and needs to be hoisted
      conv =>
        right
        intro x
        rw [division_def]
        rw [division_def]
        rw [mul_rpow (B μ x) (C μ)]
        rw [mul_rpow (B' x) C']
      conv =>
        right
        intro x
        rw [mul_assoc]
        right
        rw [← mul_assoc]
        left
        rw [mul_comm]
      conv =>
        right
        intro x
        ring_nf
      apply Summable.mul_right
      apply Summable.mul_right
      unfold gauss_term_ℝ
      conv =>
        right
        intro x
        rw [← Real.exp_mul]
        rw [← Real.exp_mul]
        rw [← exp_add]
        rw [← mul_div_right_comm]
        rw [← mul_div_right_comm]
        rw [div_add_div_same]
        rw [mul_sub_left_distrib]
        rw [sub_zero]
        rw [mul_one]
        right
        left
        ring_nf
      have X : ∀ x : ℤ, x * ↑μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = -(x - α * μ)^2 + α * (α -1) * μ^2 := by
        intro x
        ring_nf
      conv =>
        right
        intro x
        rw [X]
        rw [← div_add_div_same]
        rw [exp_add]
      apply Summable.mul_right
      apply summable_gauss_term' h
    . intro i
      apply le_of_lt
      rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' h
      . apply sg_sum_pos' h
    . rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' h
      . apply sg_sum_pos' h

theorem SG_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ : ℤ) :
  (∑' x : ℤ, (gauss_term_ℝ σ μ) (x + τ)) = ∑' x : ℤ, (gauss_term_ℝ σ μ) x := by
  have B := tsum_shift (fun x : ℤ => (gauss_term_ℝ σ μ) x) τ
  rw [← B]
  . apply tsum_congr
    intro b
    simp
  . intro ν
    conv =>
      right
      intro x
      rw [SGShift]
    apply summable_gauss_term' h

theorem sg_mul_simplify (ss : ℝ) (x μ ν : ℤ) :
  rexp (-(x - μ) ^ 2 / (2 * ss)) ^ α * rexp (-(x - ν) ^ 2 / (2 * ss)) ^ (1 - α)
  = rexp (-((x - μ) ^ 2 * α + (x - ν) ^ 2 * (1 - α)) / (2 * ss)) := by
  rw [← Real.exp_mul]
  rw [← Real.exp_mul]
  rw [← exp_add]
  rw [← mul_div_right_comm]
  rw [← mul_div_right_comm]
  rw [div_add_div_same]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_add]

theorem SG_Renyi_shift {σ : ℝ} (h : σ ≠ 0) (α : ℝ) (μ ν τ : ℤ) :
  RenyiDivergence (fun (x : ℝ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x) (fun (x : ℝ) => (gauss_term_ℝ σ ν) x / ∑' x : ℤ, (gauss_term_ℝ σ ν) x) α
    = RenyiDivergence (fun (x : ℝ) => (gauss_term_ℝ σ ((μ + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x) (fun (x : ℝ) => (gauss_term_ℝ σ ((ν + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((ν + τ) : ℤ)) x) α := by
  unfold RenyiDivergence
  congr 2
  conv =>
    left
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  conv =>
    right
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  rw [tsum_mul_right]
  rw [tsum_mul_right]
  rw [SG_periodic' h]
  rw [SG_periodic' h]
  congr 1

  -- re-indexing

  have A : ∀ μ : ℤ, ∀ x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x =  (gauss_term_ℝ σ μ) (x - τ) := by
    intro x μ
    simp [gauss_term_ℝ]
    ring_nf
  conv =>
    right
    right
    intro x
    rw [A]
    rw [A]
  clear A

  -- Now for the crux of the proof

  unfold gauss_term_ℝ
  conv =>
    left
    right
    intro x
    rw [sg_mul_simplify]
  conv =>
    right
    right
    intro x
    rw [sub_sub]
    rw [sub_sub]
    rw [← Int.cast_add]
    rw [← Int.cast_add]
    rw [sg_mul_simplify]

  rw [← tsum_shift _ (-τ)]
  . apply tsum_congr
    intro b
    congr 6
    . simp
      ring_nf
    . simp
      ring_nf
  . intro β
    conv =>
      right
      intro x
      rw [Int.cast_add]
      rw [add_sub_assoc]
      rw [add_sub_assoc]
    have X : ∀ x : ℤ, ↑x * ↑β * 2 - ↑x * ↑μ * α * 2 + (↑x * α * ↑ν * 2 - ↑x * ↑ν * 2) + (↑x ^ 2 - ↑β * ↑μ * α * 2) +
                (↑β * α * ↑ν * 2 - ↑β * ↑ν * 2) +
              ↑β ^ 2 +
            (↑μ ^ 2 * α - α * ↑ν ^ 2) +
          ↑ν ^ 2 =
          (↑x ^ 2 - 2 * x * (-↑β + ↑μ * α - α * ↑ν + ↑ν)) + (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2) := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      right
      left
      right
      ring_nf
      rw [X]
    clear X
    have X : (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)
      = (-↑β + ↑μ * α - α * ↑ν + ↑ν)^2 + (- ↑μ * α * ↑ν * 2 + ↑μ * α ^ 2 * ↑ν * 2 -
          ↑μ ^ 2 * α ^ 2 + α * ↑ν ^ 2 - α ^ 2 * ↑ν ^ 2 + α * ↑μ ^ 2) := by
      ring_nf
    conv =>
      right
      intro x
      rw [X]
      rw [← add_assoc]
    clear X
    have X : ∀ x : ℤ, (x - (-↑β + ↑μ * α - α * ↑ν + ↑ν))^2 = ↑x ^ 2 - 2 * ↑x * (-↑β + ↑μ * α - α * ↑ν + ↑ν) + (-↑β + ↑μ * α - α * ↑ν + ↑ν) ^ 2 := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      rw [← X]
      rw [neg_add]
      rw [← div_add_div_same]
      rw [exp_add]
    clear X
    apply Summable.mul_right
    apply summable_gauss_term' h

theorem RenyiDivergenceBound' {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) (h' : α > 1) :
  RenyiDivergence (fun (x : ℝ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x)
                  (fun (x : ℝ) => (gauss_term_ℝ σ ν) x / ∑' x : ℤ, (gauss_term_ℝ σ ν) x)
                  α ≤ α * (((μ - ν) : ℤ)^2 / (2 * σ^2)) := by
  rw [SG_Renyi_shift h α μ ν (-ν)]
  rw [add_right_neg]
  apply  RenyiDivergenceBound h (μ + -ν) α h'
