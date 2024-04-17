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

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

@[simp]
theorem until_zero (st : T) (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 0 st x = 0 := by
  simp [prob_while_cut]

@[simp]
theorem repeat_apply_unsat (body : RandomM T) (cond : T → Bool) (fuel : ℕ) (i x : T) (h : ¬ cond x) :
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x = 0 := by
  revert i
  induction fuel
  . simp only [zero_eq, until_zero, implies_true]
  . rename_i fuel IH
    intro j
    simp only [prob_while_cut, WhileFunctional, decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply,
      bind_apply, pure_apply]
    split
    . simp only [IH, mul_zero, tsum_zero]
    . rename_i h'
      split
      . rename_i h'
        subst h'
        simp at h'
        simp [h'] at h
      . simp

@[simp]
theorem prob_until_apply_unsat (body : RandomM T) (cond : T → Bool) (x : T) (h : ¬ cond x) :
  prob_until (body : RandomM T) (cond : T → Bool) x = 0 := by
  simp only [prob_until, Bind.bind, Bool.not_eq_true, bind_apply, prob_while]
  simp only [ENNReal.tsum_eq_zero]
  simp only [_root_.mul_eq_zero]
  simp only [iSup_eq_zero]
  intro i ; right ; intro j
  simp only [h, not_false_eq_true, repeat_apply_unsat]

theorem if_simpl (body : RandomM T) (cond : T → Bool) (x_1 x : T) :
  (if x_1 = x then 0 else if cond x_1 = true then if x = x_1 then body x_1 else 0 else 0) = 0 := by
  split
  . simp
  . split
    . split
      . rename_i h1 h2 h3
        subst h3
        contradiction
      . simp
    . simp

theorem repeat_1 (body : RandomM T) (cond : T → Bool) (x : T) (h : cond x) :
  ∑' (i : T), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) 1 i x
    = body x := by
  simp [prob_while_cut, WhileFunctional, ite_apply]
  rw [tsum_split_ite']
  simp only [tsum_zero, zero_add]
  have FOO := tsum_split_coe_right cond (fun i => @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) (body ↑i) 0)
  rw [FOO]
  clear FOO
  conv =>
    left
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

theorem tsum_split_ite_exp (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i = false then f i else g i)
    = (∑' i : T, if cond i = false then f i else 0) + (∑' i : T, if cond i = true then g i else 0) := by
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro b
  split
  . split
    . rename_i h h'
      rw [h'] at h
      contradiction
    . simp
  . split
    . simp
    . rename_i h h'
      simp at h'
      rw [h'] at h
      contradiction

theorem repeat_closed_form (body : RandomM T) (cond : T → Bool) (fuel : ℕ) (x : T) (h1 : cond x) :
  ∑' (i : T), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x
    = ∑ i in range fuel, body x * (∑' x : T, if cond x then 0 else body x)^i := by
  induction fuel
  . simp only [zero_eq, until_zero, mul_zero, tsum_zero, range_zero, sum_empty]
  . rename_i fuel IH
    unfold prob_while_cut
    unfold WhileFunctional
    simp only [decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply, bind_apply, pure_apply, mul_ite,
      mul_one, mul_zero]
    rw [tsum_split_ite_exp]
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite x]
      right
      right
      intro y
      rw [if_simpl]
    simp only [h1, ↓reduceIte, tsum_zero, add_zero]
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
    congr
    conv =>
      right
      right
      right
      intro x
      rw [mul_comm]
    rw [← mul_sum]
    have A : ∀ i : T, @ite ℝ≥0∞ (cond i = false) (instDecidableEqBool (cond i) false)
            (body i * (body x * ∑ i in range fuel, (∑' (x : T), @ite ℝ≥0∞ (cond x = true) (instDecidableEqBool (cond x) true) 0 (body x)) ^ i)) 0
            = @ite ℝ≥0∞ (cond i = false) (instDecidableEqBool (cond i) false)
            (body i) 0 * (body x * ∑ i in range fuel, (∑' (x : T), @ite ℝ≥0∞ (cond x = true) (instDecidableEqBool (cond x) true) 0 (body x)) ^ i) := by
      intro i
      split
      . simp
      . simp
    conv =>
      left
      right
      intro i
      rw [A]
    rw [ENNReal.tsum_mul_right]
    conv =>
      rw [← mul_assoc]
      left
      left
      rw [mul_comm]
    rw [mul_assoc]
    congr
    ext i
    split
    . rename_i h
      simp [h]
    . rename_i h
      simp [h]

theorem convergence (body : RandomM T) (cond : T → Bool) (x : T) :
  ⨆ fuel, ∑ i in range fuel, body x * (∑' x : T, if cond x then 0 else body x)^i
    = body x * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
  rw [← ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_geometric]

theorem repeat_monotone (body : RandomM T) (cond : T → Bool) (x : T) :
  ∀ (a : T), Monotone fun i => body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x := by
  intro a
  have A := @prob_while_cut_monotonic T (fun v => decide (cond v = false)) (fun _ => body) a x
  exact Monotone.const_mul' A (body a)

@[simp]
theorem prob_until_apply_sat (body : RandomM T) (cond : T → Bool) (x : T) (h : cond x) :
  prob_until (body : RandomM T) (cond : T → Bool) x
    = body x * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
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
    rw [finset_sum_iSup_nat (repeat_monotone body cond x)]
  rw [iSup_comm]
  conv =>
    right
    right
    intro j
    rw [← ENNReal.tsum_eq_iSup_sum]

@[simp]
theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) * (1 - ∑' x : T, if cond x then 0 else body x)⁻¹ := by
  split
  . rename_i h
    simp [h, prob_until_apply_sat]
  . rename_i h
    simp [h, prob_until_apply_unsat]

@[simp]
theorem prob_until_apply_norm (body : RandomM T) (cond : T → Bool) (x : T) (norm : ∑' x : T, body x = 1) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) * (∑' x : T, if cond x then body x else 0)⁻¹ := by
  rw [prob_until_apply body cond x]
  congr
  have A : ∀ x, body x = (if cond x then body x else 0) + (if cond x then 0 else body x) := by
    intro x
    split
    . simp
    . simp
  revert norm
  conv =>
    left
    left
    right
    intro y
    rw [A]
  clear A
  rw [tsum_add ENNReal.summable ENNReal.summable]
  intro B
  have F : (∑' (x : T), if cond x = true then 0 else body x) ≠ ⊤ := by
    by_contra h
    simp [h] at B
  rw [← B]
  rw [ENNReal.add_sub_cancel_right F]
