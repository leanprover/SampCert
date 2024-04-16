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

theorem sg_sum_pos' (μ : ℤ) (ss : ℝ) (h1 : ss > 0) (α : ℝ)  :
  0 < (sg' ss μ x / ∑' (x : ℤ), sg' ss μ x)^α := by
  apply rpow_pos_of_pos
  rw [div_pos_iff]
  left
  constructor
  . apply exp_pos
  . apply sg_sum_pos _ _ h1

theorem SG_Renyi_simplify (μ ν : ℤ) (ss : ℝ) (h : ss > 0) (α : ℝ) :
  (fun (x : ℤ) => sg' ss μ x / ∑' (x : ℤ), sg' ss μ x) x ^ α *
      (fun (x : ℤ) => sg' ss ν x / ∑' (x : ℤ), sg' ss ν x) x ^ (1 - α)
    = sg' ss μ x ^ α * sg' ss ν x ^ (1 - α) / ∑' (x : ℤ), sg' ss ν x := by
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ sg' ss μ x := by
    intro μ x
    unfold sg'
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), sg' ss μ x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sg_sum_pos _ _ h
  have D : 0 < (∑' (x : ℤ), sg' ss 0 x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sg_sum_pos _ _ h
  simp
  conv =>
    left
    ring_nf
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  rw [SG_periodic' _ _ h]
  rw [SG_periodic' _ _ h]
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


theorem RenyiDivergenceBound (μ : ℤ) (ss : ℝ) (h : ss > 0) (α : ℝ) (h' : α > 1) :
  RenyiDivergence (fun (x : ℝ) => sg' ss μ x / ∑' x : ℤ, sg' ss μ x)
                  (fun (x : ℝ) => sg' ss (0 : ℤ) x / ∑' x : ℤ, sg' ss (0 : ℤ) x)
                  α ≤ α * (μ^2 / (2 * ss)) := by
  unfold RenyiDivergence
  have A : 0 < 1 / (α - 1) := by
    simp [h']
  rw [← le_div_iff' A]
  refine Real.exp_le_exp.mp ?_
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
  rw [exp_log]
  . conv =>
      left
      ring_nf
      right
      intro x
      rw [mul_rpow (B μ x) (C μ)]
      rw [mul_rpow (B' x) C']
    -- First, I work on the denominator
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
    --clear A B B' C C' D X E
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
      unfold sg'
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
      apply GaussConvergence _ _ h
    . intro i
      apply le_of_lt
      rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' _ _ h
      . apply sg_sum_pos' _ _ h
    . rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' _ _ h
      . apply sg_sum_pos' _ _ h

-- theorem summable_shift (f : ℤ → ℝ) (μ : ℤ) (h : Summable fun x : ℤ => f x) :
--   Summable fun x : ℤ => f (x + μ) := by
--   have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ f
--   replace A := A.1 h
--   cases A
--   rename_i A B
--   rw [summable_int_iff_summable_nat_and_neg_add_zero]
--   cases μ
--   . rename_i μ
--     constructor
--     . have C := @summable_nat_add_iff ℝ _ _ _ (fun (n : ℕ) => f n) μ
--       replace C := C.2 A
--       simp at *
--       exact C
--     . have C := @summable_nat_add_iff ℝ _ _ _ (fun (n : ℕ) => f (-((n : ℤ) + 1))) μ
--       replace C := C.2 B

--       simp at *
--       conv =>
--         right
--         intro n
--         rw [add_assoc]
--         right
--         right
--         rw [add_comm]
--       sorry -- problem
--   . sorry

theorem tsum_shift (f : ℤ → ℝ) (μ : ℕ)
  (h2 : ∀ μ : ℤ, Summable fun x : ℕ => f (x + μ))
  (h3 : ∀ μ : ℤ, Summable fun x : ℕ => f (-(x + 1) + μ))
  :
  (∑' x : ℤ, f x) = ∑' x : ℤ, f (x + μ) := by
  have h1 : Summable fun x : ℕ => f x := by
    apply h2 0
  have h4 : Summable fun x : ℕ => f (- (x + 1)) := by
    apply h3 0
  rw [tsum_of_nat_of_neg_add_one h1]
  . rw [← sum_add_tsum_nat_add μ h1]
    rw [add_rotate]
    conv =>
      left
      rw [add_assoc]
      right
      rw [add_comm]
    conv =>
      right
      rw [@tsum_of_nat_of_neg_add_one ℝ _ _ _ _ (fun x : ℤ => f (x + μ)) (h2 μ) (h3 μ)]
    congr 1
    conv =>
      right
      rw [← sum_add_tsum_nat_add μ (h3 μ)]
    conv =>
      right
      right
      right
      intro i
      ring_nf
      simp
      ring_nf
      rw [← neg_add']
      rw [add_comm]
    congr 1
    induction μ
    . simp
    . rename_i n IH
      rw [Finset.sum_range_succ]
      rw [IH]
      clear IH
      rw [Finset.sum_range_succ']
      simp
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring_nf
  . exact h4

theorem tsum_shift' (f : ℤ → ℝ) (μ : ℕ) :
  ∑' x : ℤ, f (x - μ) = (∑' x : ℤ, f x) := by
  rw [tsum_of_nat_of_neg_add_one sorry]
  . rw [← sum_add_tsum_nat_add μ sorry]
    rw [add_rotate]
    conv =>
      left
      rw [add_assoc]
      right
      rw [add_comm]
    conv =>
      right
      rw [tsum_of_nat_of_neg_add_one sorry sorry]
    congr 1
    . apply tsum_congr
      intro b
      congr 1
      simp
    . conv =>
        right
        rw [← sum_add_tsum_nat_add μ sorry]
      congr 1
      . induction μ
        . simp
        . rename_i μ IH
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ]
          rw [← IH]
          simp
      . apply tsum_congr
        intro b
        congr 1
        simp
        ring_nf
  . sorry

theorem SG_Renyi_shift (ss : ℝ) (h : 0 < ss) (p q : ℝ → ℝ) (α : ℝ) (μ ν τ : ℤ) :
  RenyiDivergence (fun (x : ℝ) => sg' ss μ x / ∑' x : ℤ, sg' ss μ x) (fun (x : ℝ) => sg' ss ν x / ∑' x : ℤ, sg' ss ν x) α
    = RenyiDivergence (fun (x : ℝ) => sg' ss ((μ + τ) : ℤ) x / ∑' x : ℤ, sg' ss ((μ + τ) : ℤ) x) (fun (x : ℝ) => sg' ss ((ν + τ) : ℤ) x / ∑' x : ℤ, sg' ss ((ν + τ) : ℤ) x) α := by
  unfold RenyiDivergence
  congr 2
  conv =>
    left
    right
    intro x
    rw [SG_Renyi_simplify _ _ _ h]
    rw [division_def]
  conv =>
    right
    right
    intro x
    rw [SG_Renyi_simplify _ _ _ h]
    rw [division_def]
  rw [tsum_mul_right]
  rw [tsum_mul_right]
  rw [SG_periodic' _ _ h]
  rw [SG_periodic' _ _ h]
  congr 1
  have A : ∀ μ : ℤ, ∀ x : ℤ, sg' ss ((μ + τ) : ℤ) x =  sg' ss μ (x - τ) := by
    intro x μ
    simp [sg']
    ring_nf
  conv =>
    right
    right
    intro x
    rw [A]
    rw [A]
  clear A
  sorry
