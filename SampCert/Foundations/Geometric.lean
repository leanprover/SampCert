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
def loop_cond (st : (Bool × ℕ)) : Bool := st.1
def loop_body (st : (Bool × ℕ)) : RandomM (Bool × ℕ) := do
  let x ← bernoulli (1/2) half_in_unit
  return (x,st.2 + 1)

def geometric : RandomM ℕ := do
  let st ← prob_while loop_cond loop_body (true,0)
  return st.2

theorem blob1 :
  prob_while_cut loop_cond loop_body 0 (true, 0) (false,1) = 0 := by
  simp [prob_while_cut]

theorem blob2 :
  prob_while_cut loop_cond loop_body 1 (true, 0) (false,1) = 0 := by
  simp [prob_while_cut, WhileFunctional, ite_apply]

theorem blob3 :
  prob_while_cut loop_cond loop_body 2 (true, 0) (false,1) = (1 : ENNReal) / 2 := by
  simp [prob_while_cut, WhileFunctional, ite_apply, loop_cond, loop_body]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp
  conv =>
    left
    right
    intro b
    rw [tsum_bool]
  simp
  sorry -- OK

theorem blob4 :
  prob_while_cut loop_cond loop_body 3 (true, 0) (false,1) = (1 : ENNReal) / 2 := by
  simp [prob_while_cut, WhileFunctional, ite_apply, loop_cond, loop_body]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp
  conv =>
    left
    right
    right
    intro b
    rw [tsum_bool]
    rw [tsum_bool]
    simp
  conv =>
    left
    left
    right
    intro b
    rw [tsum_bool]
    simp
  sorry -- OK
