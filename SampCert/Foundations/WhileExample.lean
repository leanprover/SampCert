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
  sorry -- 1 + 1 = 2

def bbb (n : ℕ) := ∑ m in range n, f (m + 1)

theorem bbb_proof :
  Filter.Tendsto bbb Filter.atTop (nhds 1) := by
  refine HasSum.tendsto_sum_nat ?h
  rw [hasSum_nat_add_iff 1]
  simp
  apply hasSum_geometric_two

def h (n : ℕ) := ((1 : ENNReal) / (2 : ENNReal))^n
def ddd (n : ℕ) := ∑ m in range n, h (m + 1)

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
    sorry

#check tsum_eq_add_tsum_ite

-- For a limit, should be allowed to ignore any finite prefix of the sequence

#check iSup_eq_of_forall_le_of_forall_lt_exists_gt
#check IsLUB.iSup_eq
#check iSup_eq_of_tendsto

theorem loop_apply_true : loop true = 1 := by
  unfold loop
  unfold prob_while
  apply iSup_eq_of_tendsto
  . sorry -- could be proved once and for all
  . refine ENNReal.tendsto_nhds_of_Icc ?_
    intro ε COND
    refine Filter.eventually_atTop.mpr ?_
    sorry

-- In general, if the pwc eventually behaves like a series that converges to x,
-- then the pmf is x
