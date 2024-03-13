/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability
import SampCert.Foundations.Util

noncomputable section

open Classical SubPMF ProbabilityTheory Nat ENNReal BigOperators Finset

noncomputable def prob_until (body : RandomM ℕ) (cond : ℕ → Bool) : RandomM ℕ := do
  let v ← body
  prob_while (λ v : ℕ => ¬ cond v) (λ _ : ℕ => body) v

@[simp]
theorem until_zero (st : ℕ) (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 0 st x = 0 := by
  simp [prob_while_cut]

@[simp]
theorem repeat_apply_unsat (body : RandomM ℕ) (cond : ℕ → Bool) (fuel i x : ℕ) (h : ¬ cond x) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x = 0 := by
  revert i
  induction fuel
  . simp only [zero_eq, until_zero, forall_const]
  . rename_i fuel IH
    intro j
    simp [prob_while_cut, WhileFunctional, ite_apply]
    split
    . simp [IH]
    . rename_i h'
      split
      . rename_i h'
        subst h'
        simp at h'
        simp [h'] at h
      . simp

@[simp]
theorem prob_until_apply_unsat (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : ¬ cond x) :
  prob_until (body : RandomM ℕ) (cond : ℕ → Bool) x = 0 := by
  simp only [prob_until, Bind.bind, Bool.not_eq_true, bind_apply, prob_while]
  simp only [ENNReal.tsum_eq_zero]
  simp only [_root_.mul_eq_zero]
  simp only [iSup_eq_zero]
  intro i ; right ; intro j
  simp [repeat_apply_unsat, h]

theorem if_simpl (body : RandomM ℕ) (cond : ℕ → Bool) (x_1 x : ℕ) :
  @ite ℝ≥0∞ (x_1 = x) (propDecidable (x_1 = x)) 0 (@ite ℝ≥0∞ (cond x_1 = true) (instDecidableEqBool (cond x_1) true) (body x_1 * @ite ℝ≥0∞ (x = x_1) (propDecidable (x = x_1)) 1 0) 0) = 0 := by
  split
  . simp
  . split
    . split
      . rename_i h1 h2 h3
        simp at *
        subst h3
        contradiction
      . simp
    . simp

theorem repeat_1 (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) :
  ∑' (i : ℕ), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 1 i x
    = body x := by
  simp only [prob_while_cut, WhileFunctional, decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply,
    bind_apply, pure_apply, mul_ite]
  rw [tsum_split_ite']
  have FOO := tsum_split_coe_right cond (fun i => body ↑i * @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) 1 0)
  rw [FOO]
  clear FOO
  conv =>
    left
    right
    rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [h, zero_apply, mul_zero, tsum_zero, ↓reduceIte, mul_one,
    zero_add]
  conv =>
    left
    right
    right
    intro y
    rw [if_simpl]
  simp

theorem repeat_closed_form (body : RandomM ℕ) (cond : ℕ → Bool) (fuel x : ℕ) (h1 : cond x) :
  ∑' (i : ℕ), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x
    = ∑ i in range fuel, body x * (∑' (i : {i | cond i = false}), body i)^i := by
  induction fuel
  . simp
  . rename_i fuel IH
    unfold prob_while_cut
    unfold WhileFunctional
    conv =>
      left
      simp only [decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply, bind_apply, pure_apply,
        mul_ite, succ_sub_succ_eq_sub, tsub_zero, sum_const,
        card_range, nsmul_eq_mul, cast_succ, cast_add, cast_one]
    rw [tsum_split_ite']
    rw [ENNReal.tsum_mul_right]
    have B := tsum_split_coe_right cond (fun i => body ↑i * @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) 1 0)
    rw [B]
    clear B
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite x]
      right
      right
      intro y
      rw [if_simpl]
    simp only [h1, reduceIte, mul_one, tsum_zero, add_zero]
    rw [IH]
    clear IH
    conv =>
      right
      rw [Finset.sum_range_succ']
    simp only [_root_.pow_zero, mul_one]
    conv =>
      right
      left
      right
      intro k
      rw [_root_.pow_succ]
    rw [← mul_sum]
    rw [← mul_sum]
    rw [← mul_sum]
    conv =>
      left
      left
      rw [← mul_assoc]
      left
      rw [mul_comm]
    rw [mul_assoc]

theorem convergence (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) :
  ⨆ fuel, ∑ i in range fuel, body x * (∑' (i : {i | cond i = false}), body i)^i
    = body x * (1 - ∑' (i : ↑{i | cond i = false}), body ↑i)⁻¹ := by
  rw [← ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_geometric]

theorem repeat_monotone (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) :
  ∀ (a : ℕ) ,Monotone fun i => body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x := by
  intro a
  have A := @prob_while_cut_monotonic ℕ (fun v => decide (cond v = false)) (fun _ => body) a x
  exact Monotone.const_mul' A (body a)

@[simp]
theorem prob_until_apply_sat (body : RandomM ℕ) (cond : ℕ → Bool) (x : ℕ) (h : cond x) :
  prob_until (body : RandomM ℕ) (cond : ℕ → Bool) x
    = body x * (1 - ∑' (i : ↑{i | cond i = false}), body ↑i)⁻¹ := by
  simp only [prob_until, Bind.bind, Bool.not_eq_true, bind_apply, prob_while]
  rw [← convergence]
  conv =>
    right
    right
    intro fuel
    rw [← repeat_closed_form _ _ _ _ h]
  rw [eq_comm]
  rw [ENNReal.tsum_eq_iSup_sum]
  conv =>
    right
    right
    intro s
    right
    intro a
    rw [mul_iSup]
  conv =>
    right
    right
    intro s
    rw [finset_sum_iSup_nat (repeat_monotone body cond x h)]
  rw [iSup_comm]
  conv =>
    right
    right
    intro j
    rw [← ENNReal.tsum_eq_iSup_sum]
