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
  . simp
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

theorem repeat_closed_form (body : RandomM T) (cond : T → Bool) (fuel : ℕ) (x : T) (h1 : cond x) :
  ∑' (i : T), body i * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) fuel i x
    = ∑ i in range fuel, body x * (∑' (i : {i | cond i = false}), body i)^i := by
  induction fuel
  . simp
  . rename_i fuel IH
    unfold prob_while_cut
    unfold WhileFunctional
    simp only [decide_eq_true_eq, Bind.bind, Pure.pure, ite_apply, bind_apply, pure_apply, mul_ite,
      mul_one, mul_zero]
    rw [tsum_split_ite']
    rw [ENNReal.tsum_mul_right]
    have B := tsum_split_coe_right cond (fun i => @ite ℝ≥0∞ (x = ↑i) (propDecidable (x = ↑i)) (body ↑i) 0)
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

theorem convergence (body : RandomM T) (cond : T → Bool) (x : T) :
  ⨆ fuel, ∑ i in range fuel, body x * (∑' (i : {i | cond i = false}), body i)^i
    = body x * (1 - ∑' (i : ↑{i | cond i = false}), body ↑i)⁻¹ := by
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
    rw [finset_sum_iSup_nat (repeat_monotone body cond x)]
  rw [iSup_comm]
  conv =>
    right
    right
    intro j
    rw [← ENNReal.tsum_eq_iSup_sum]


def u₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ℝ :=
  (body x).toReal * (1 - ∑' (x : T), if cond x then body x else 0).toReal^n

def u₂ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ENNReal :=
  body x * (1 - ∑' (x : T), if cond x then body x else 0)^n

def s₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₁ cond body x m

def s₂ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₂ cond body x m

theorem s₁_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₁ cond body x (x_1 + 1)) Filter.atTop
  (nhds (ENNReal.toReal ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0))) := by
  sorry

theorem s₂_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (fun x_1 => s₂ cond body x x_1) Filter.atTop
  (nhds ((if cond x = true then body x else 0) / ∑' (x : T), if cond x = true then body x else 0)) := by
  sorry

theorem split (cond : T → Bool) (body : RandomM T) (x : T) :
  ∑' (a : T),
      body a *
        ite (cond a = false)
          (fun b => ∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) n a b)
          (fun a' => if a' = a then 1 else 0) x
  =
  (∑' (a : { v : T // cond v = false}),
    body a * ∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun x => body) n a x)
  +
  (∑' (a : { v : T // cond v = true}), body a * if x = a then 1 else 0) := sorry

theorem ite_simp (cond : T → Bool) (body : RandomM T) (x : T) :
  (∑' (a : { v // cond v = true }), body ↑a * @ite ENNReal (x = ↑a) (propDecidable (x = ↑a)) 1 0) = body x := by sorry

theorem the_eq (cond : T → Bool) (body : RandomM T) (x : T) (a : T) (h : ¬ cond a) (n : ℕ) :
  (prob_while_cut (fun v => decide (cond v = false)) (fun x => body) (n + 1) a x)
  =
  s₂ cond body x n := by
  induction n
  . simp [prob_while_cut, WhileFunctional, s₂, u₂, h]
  . rename_i n IH
    revert IH
    simp [prob_while_cut, WhileFunctional]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [h]
    intro IH
    rw [split]
    rw [IH]
    clear IH
    rw [ENNReal.tsum_mul_right]
    rw [ite_simp]
    simp [s₂]
    rw [sum_range_succ]
    rw [← s₂]
    simp [u₂]
    sorry -- Looks reasonable

theorem pwc_convergence_0 (body : RandomM T) (cond : T → Bool) (x : T) (a : T) (h : ¬ cond a) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    . rw [Filter.tendsto_congr (the_eq cond body x a h)]
      simp [s₂_convergence]

theorem exists_seq_same_ind (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) (i : ℕ) :
  (∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (i + 1) b x := by
  simp [prob_while_cut, WhileFunctional, h]

theorem exists_seq_same_limit (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) (l : ENNReal) :
  Filter.Tendsto (fun i => (∑' (a : T), body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) i a x)) Filter.atTop (nhds l)
  ↔
  Filter.Tendsto (fun i => prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x) Filter.atTop (nhds l) := by
  conv =>
    right
    rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
  refine Filter.tendsto_congr ?h
  intro x1
  apply exists_seq_same_ind
  trivial

theorem exists_seq_same (body : RandomM T) (cond : T → Bool) (x : T) (b : T) (h : ¬ cond b) :
  (∑' (a : T), body a * ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x)
  =
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i b x := by
  refine (iSup_eq_of_tendsto ?hf ?_).symm
  . simp [prob_while_cut_monotonic]
  . rw [← exists_seq_same_limit]
    . sorry
    . trivial

@[simp]
theorem prob_until_apply (body : RandomM T) (cond : T → Bool) (x : T) (ex : ∃ b : T, ¬ cond b) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  cases ex
  rename_i b h
  rw [exists_seq_same body cond x b h]
  rw [pwc_convergence_0]
  trivial

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  sorry
