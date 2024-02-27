/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.While
import Mathlib.Probability.ConditionalProbability

noncomputable section

open SubPMF ProbabilityTheory Nat ENNReal BigOperators Finset

variable {T : Type} [MeasurableSpace T]

noncomputable def prob_until (body : RandomM T) (cond : T → Bool) : RandomM T := do
  let v ← body
  prob_while (λ v : T => ¬ cond v) (λ _ : T => body) v

def u₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) : ℝ :=
  (body x).toReal * (1 - ∑' (x : T), if cond x then body x else 0).toReal^n

def s₁ (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) := ∑ m in range n, u₁ cond body x (m + 1)

theorem s₁_convergence (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (s₁ cond body x) Filter.atTop (nhds ((body x).toReal / (∑' (x : T), if cond x then body x else 0).toReal)) := by
  unfold s₁
  unfold u₁
  refine HasSum.tendsto_sum_nat ?h
  sorry

theorem foobar (cond : T → Bool) (body : RandomM T) (x : T) :
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n init x) Filter.atTop (nhds ((if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0))) := by
  apply Filter.Tendsto.apply
  sorry

theorem the_eq (cond : T → Bool) (body : RandomM T) (x : T) (n : ℕ) (scond : n > 0) (init : T) (h : ¬ cond init) :
  ∑' a : T, body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n a x
  =
  prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (n + 1) init x := by
  revert init
  induction n
  . contradiction
  . rename_i n IH
    intro init COND
    unfold prob_while_cut
    unfold WhileFunctional
    simp at COND
    simp [COND]
    congr
    ext a
    split
    . rename_i COND'
      simp
      have OR : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
      cases OR
      . rename_i N_0
        subst N_0
        clear IH scond
        simp [prob_while_cut, WhileFunctional, COND']
      . rename_i N_N0
        simp at IH
        have IH' := IH N_N0 a COND'
        clear IH
        simp [IH']
    . rename_i COND'
      unfold prob_while_cut
      unfold WhileFunctional
      simp
      simp [COND']

theorem tendsto2 (body : RandomM T) (cond : T → Bool) (x : T) (v : ENNReal) :
  Filter.Tendsto (λ n => prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) (n + 1) init x) Filter.atTop (nhds v)
  ↔
  Filter.Tendsto (λ n => ∑' a : T, body a * prob_while_cut (fun v => decide (cond v = false)) (fun _ => body) n a x) Filter.atTop (nhds v) := by
  apply Filter.tendsto_congr
  intro i
  rw [the_eq]
  sorry
  sorry -- need to take close look, condition not true at the beginnig and loop condition

@[simp]
theorem prob_until_apply [Fintype T] (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while]
  rw [tsum_fintype]
  conv =>
    left
    right
    intro b
    rw [ENNReal.mul_iSup]
  rw [ENNReal.finset_sum_iSup_nat]
  apply iSup_eq_of_tendsto
  . sorry
  . sorry
  . intro a
    apply Monotone.const_mul'
    apply prob_while_cut_monotonic

theorem pwc_convergence (body : RandomM T) (cond : T → Bool) (x : T) :
  ⨆ i, prob_while_cut (fun v => decide (cond v = false)) (fun x => body) i a x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  apply iSup_eq_of_tendsto
  . simp [prob_while_cut_monotonic]
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)]
    sorry

@[simp]
theorem prob_until_apply' (body : PMF T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  simp [prob_until, prob_while, pwc_convergence, ENNReal.tsum_mul_right]

@[simp]
theorem prob_until_apply_2 (body : RandomM T) (cond : T → Bool) (x : T) :
  prob_until (body : RandomM T) (cond : T → Bool) x =
  (if cond x then body x else 0) / (∑' (x : T), if cond x then body x else 0) := by
  sorry
