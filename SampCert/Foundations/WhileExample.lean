/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SampCert.Foundations.Basic

noncomputable section

open PMF Nat Finset BigOperators

theorem half_in_unit : (1 : ENNReal) / 2 ≤ 1 := by
  exact ENNReal.half_le_self
def loop_cond (b : Bool) : Bool := ¬ b
def loop_body (_ : Bool) : RandomM Bool := bernoulli (1/2) half_in_unit

def loop : RandomM Bool := prob_while loop_cond loop_body false

def u₁ (n : ℕ) : ℝ := (1/2)^n

@[simp]
theorem u₁_simple : 1 + u₁ 0 = 2 := by
  unfold u₁
  simp
  exact one_add_one_eq_two

def s₁ (n : ℕ) := ∑ m in range n, u₁ (m + 1)

theorem s₁_convergence :
  Filter.Tendsto s₁ Filter.atTop (nhds 1) := by
  refine HasSum.tendsto_sum_nat ?h
  rw [hasSum_nat_add_iff 1]
  simp only [range_one, sum_singleton, u₁_simple]
  apply hasSum_geometric_two


def u₂ (n : ℕ) : ENNReal := (1/2)^n

theorem u₂_no_top (n : ℕ) : u₂ n ≠ ⊤ := by
  simp [u₂]

def s₂ (n : ℕ) := ∑ m in range n, u₂ (m + 1)

theorem no_top (n : ℕ) : s₂ n ≠ ⊤ := by
  induction n
  . simp [s₂]
  . rename_i n IH
    simp [s₂] at *
    rw [@sum_range_succ]
    simp
    intro a
    cases a
    . contradiction
    . rename_i hh
      simp [u₂] at hh

theorem s₂_succ (n : ℕ) : s₂ (succ n) = s₂ n + (1/2)^(n+1) := by
  simp [s₂,u₂,sum_range_succ]

theorem seed_eq :
  ENNReal.toReal 2⁻¹ = 2⁻¹ := by
  rw [ENNReal.toReal_inv]
  exact rfl

theorem u_eq :
  ENNReal.toReal (u₂ n) = u₁ n := by
  induction n
  . simp [u₂, u₁]
  . rename_i n IH
    simp [u₂, u₁]
    simp [_root_.pow_succ]
    simp [u₂, u₁] at IH
    rw [← IH]
    rw [mul_comm]
    simp [seed_eq]

theorem s_eq_2 :
  (fun n => ENNReal.toReal (s₂ n)) = s₁ := by
  ext n
  induction n
  . simp [s₂,s₁]
  . rename_i n IH
    simp [s₂, s₁]
    simp [sum_range_succ]
    rw [← s₂, ← s₁]
    rw [← IH]
    rw [ENNReal.toReal_add, u_eq]
    . apply no_top n
    . apply u₂_no_top

theorem s₂_convergence:
  Filter.Tendsto s₂ Filter.atTop (nhds 1) := by
  refine (ENNReal.tendsto_toReal_iff ?hf ?hx).mp ?_
  . intro i
    apply no_top i
  . simp
  . rw [s_eq_2] -- simplify here
    apply s₁_convergence


theorem the_eq (n : ℕ) :
  prob_while_cut loop_cond loop_body (n + 1) false true = s₂ n := by
  induction n
  . simp [prob_while_cut, WhileFunctional, loop_body, loop_cond, tsum_bool, s₂]
  . rename_i n IH
    revert IH
    simp [prob_while_cut, WhileFunctional, loop_body, loop_cond, tsum_bool]
    intro IH
    simp [IH]
    clear IH
    simp [s₂]
    simp [sum_range_succ]
    rw [← s₂]
    simp [u₂]
    induction n -- I would rather not prove this inlined but I can't hoist this goal and get its coercion right
    . simp [s₂]
    . rename_i n IH
      simp [s₂_succ]
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
  ↔ Filter.Tendsto s₂ Filter.atTop (nhds 1) := by
  apply Filter.tendsto_congr
  simp [the_eq]

theorem int2 :
  Filter.Tendsto (λ n => prob_while_cut loop_cond loop_body n false true) Filter.atTop (nhds 1)
  ↔ Filter.Tendsto (λ n => prob_while_cut loop_cond loop_body (n + 1) false true) Filter.atTop (nhds 1) := by
  apply Iff.symm (Filter.tendsto_add_atTop_iff_nat 1)

theorem loop_apply_true : loop true = 1 := by
  unfold loop
  apply while_apply
  simp [int1, int2, s₂_convergence]

theorem loop_apply_false : loop false = 0 := sorry

@[simp]
theorem loop_normalizes : ∑ b : Bool, loop b = 1 := by
  rw [Fintype.sum_bool]
  simp [loop_apply_true,loop_apply_false]

def loopPMF : PMF Bool := PMF.ofFintype loop loop_normalizes
