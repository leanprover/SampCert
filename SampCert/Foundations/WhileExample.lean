/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SampCert.Foundations.Basic

noncomputable section

open PMF Nat Finset BigOperators

theorem half_in_unit : (1 : ENNReal) / 2 ≤ 1 := sorry
def loop_cond (b : Bool) : Bool := ¬ b
def loop_body (_ : Bool) : RandomM Bool := bernoulli (1/2) half_in_unit

def loop : RandomM Bool := prob_while loop_cond loop_body false

def f (n : ℕ) := ((1 : ℝ) / (2 : ℝ))^n

@[simp]
theorem f_apply_0 : 1 + f 0 = 2 := by
  unfold f
  simp
  exact one_add_one_eq_two

def bbb (n : ℕ) := ∑ m in range n, f (m + 1)

theorem bbb_proof :
  Filter.Tendsto bbb Filter.atTop (nhds 1) := by
  refine HasSum.tendsto_sum_nat ?h
  rw [hasSum_nat_add_iff 1]
  simp
  apply hasSum_geometric_two

@[simp]
def half := (1 : ENNReal) / (2 : ENNReal)

def h (n : ℕ) := half^n
def ddd (n : ℕ) := ∑ m in range n, h (m + 1)

theorem ddd_succ (n : ℕ) : ddd (succ n) = ddd n + half^(n+1) := by
  simp [ddd,h,half,sum_range_succ]

theorem ddd_no_top (n : ℕ) : ddd n ≠ ⊤ := by
  induction n
  . simp [ddd]
  . rename_i n IH
    simp [ddd] at *
    rw [@sum_range_succ]
    simp
    intro a
    cases a
    . contradiction
    . rename_i hh
      simp [h] at hh


#check hasSum_geometric_two.tsum_eq


theorem ddd_proof :
  Filter.Tendsto ddd Filter.atTop (nhds 1) := sorry

theorem the_eq (n : ℕ) :
  prob_while_cut loop_cond loop_body (n + 1) false true = ddd n := by
  induction n
  . simp [prob_while_cut, WhileFunctional, loop_body, loop_cond, tsum_bool, ddd]
  . rename_i n IH
    revert IH
    simp [prob_while_cut, WhileFunctional, loop_body, loop_cond, tsum_bool]
    intro IH
    simp [IH]
    clear IH
    simp [ddd]
    simp [sum_range_succ]
    rw [← ddd]
    simp [h]
    induction n -- I would rather not prove this inlined but I can't hoist this goal and get its coercion right
    . simp [ddd]
    . rename_i n IH
      simp [ddd_succ]
      rw [_root_.pow_succ]
      rw [@mul_add]
      rw [@add_right_comm]
      rw [IH]
      clear IH
      rw [_root_.pow_succ]
      rw [_root_.pow_succ]
      rw [_root_.pow_succ]

theorem int1 :
  Filter.Tendsto (λ n => prob_while_cut loop_cond loop_body (n + 1) false true) Filter.atTop (nhds 1)
  ↔ Filter.Tendsto ddd Filter.atTop (nhds 1) := by
  apply Filter.tendsto_congr
  simp [the_eq]

theorem int2 :
  Filter.Tendsto (λ n => prob_while_cut loop_cond loop_body n false true) Filter.atTop (nhds 1)
  ↔ Filter.Tendsto (λ n => prob_while_cut loop_cond loop_body (n + 1) false true) Filter.atTop (nhds 1) := by
  apply Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)

theorem loop_apply_true : loop true = 1 := by
  unfold loop
  unfold prob_while
  apply iSup_eq_of_tendsto
  . apply prob_while_cut_monotonic
  . simp [int1, int2, ddd_proof]
