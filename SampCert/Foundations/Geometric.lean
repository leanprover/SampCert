/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SampCert.Foundations.Basic

noncomputable section

namespace Geometric

open Classical PMF Nat Finset BigOperators

theorem half_in_unit : (1 : ENNReal) / 2 ≤ 1 := by
  exact ENNReal.half_le_self
def loop_cond (st : (Bool × ℕ)) : Bool := st.1
def loop_body (st : (Bool × ℕ)) : RandomM (Bool × ℕ) := do
  let x ← bernoulli (1/2) half_in_unit
  return (x,st.2 + 1)

theorem ite_simpl (x a : ℕ) (v : ENNReal) :
  (@ite ENNReal (x = a) (propDecidable (x = a)) 0 (@ite ENNReal (x = a) (instDecidableEqNat x a) v 0)) = 0 := by
  split
  . simp
  . simp

@[simp]
theorem geometric_zero (st₁ st₂ : Bool × ℕ) :
  prob_while_cut loop_cond loop_body 0 st₁ st₂ = 0 := by
  simp [prob_while_cut]

theorem geometric_succ_true (fuel n : ℕ) (st : Bool × ℕ) :
  prob_while_cut loop_cond loop_body (succ fuel) (true,n) st =
  2⁻¹ * prob_while_cut loop_cond loop_body fuel (false, n + 1) st +
    2⁻¹ * prob_while_cut loop_cond loop_body fuel (true, n + 1) st := by
  cases st
  rename_i b m
  simp [prob_while_cut, WhileFunctional, loop_cond, loop_body, ite_apply, ENNReal.tsum_prod', tsum_bool]
  conv =>
    left
    . congr
      . rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
        right
        right
        intro x
        rw [ite_simpl]
      . rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
        right
        right
        intro x
        rw [ite_simpl]
  simp

@[simp]
theorem geometric_succ_false (fuel n : ℕ) (st : Bool × ℕ) :
  prob_while_cut loop_cond loop_body (succ fuel) (false,n) st =
  if st = (false,n) then 1 else 0 := by
  cases st
  rename_i b m
  simp [prob_while_cut, WhileFunctional, loop_cond, loop_body, ite_apply, ENNReal.tsum_prod', tsum_bool]

def geometric : RandomM ℕ := do
  let st ← prob_while loop_cond loop_body (true,0)
  return st.2

@[simp]
theorem loop_body_apply_true_true (K₁ K₂ : ℕ) :
  loop_body (true, K₁) (true, K₂) = if K₂ = K₁ + 1 then 2⁻¹ else 0 := by
  simp [tsum_bool,loop_body]

@[simp]
theorem loop_body_apply_true_false (K₁ K₂ : ℕ) :
  loop_body (true, K₁) (false, K₂) = if K₂ = K₁ + 1 then 2⁻¹ else 0 := by
  simp [tsum_bool,loop_body]

@[simp]
theorem loop_body_init_apply_false' (st : Bool × ℕ) :
  loop_body st (false, 0) = 0 := by
  simp [tsum_bool,loop_body]
  intro
  contradiction

@[simp]
theorem loop_body_shift (K₁ K₂ : ℕ ) (b₁ b₂ : Bool) :
  loop_body (b₁, K₁) (b₂, K₁ + 1) =
  loop_body (b₁, K₁ + K₂) (b₂, K₁ + K₂ + 1) := by
  simp [loop_body]

@[simp]
theorem geometric_monotone_counter (fuel n : ℕ) (st : Bool × ℕ) (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  prob_while_cut loop_cond loop_body fuel st (false, n) = 0 := by
  revert st
  induction fuel
  . simp
  . rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    simp [prob_while_cut, WhileFunctional, loop_cond, loop_body, ite_apply]
    split
    . rename_i h
      subst h
      simp only [tsum_bool]
      simp
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact Nat.eq_or_lt_of_le h2
        cases OR
        . rename_i h
          subst h
          exact Nat.ne_of_gt le.refl
        . rename_i h
          exact Nat.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by exact
        (bne_iff_ne (true, stn + 1) (false, n)).mp rfl
      rw [IH _ A]
      rw [IH _ B]
      . simp
      . simp
        exact le.step h2
      . simp
        exact le.step h2
    . rename_i h
      simp at h
      have h3 := h1 h
      simp [h, h3]
      exact Ne.symm (h1 h)

theorem ite_simpl' (x a : ℕ) (v : ENNReal) :
  (@ite ENNReal (x = a) (propDecidable (x = a)) 0 (@ite ENNReal (a = x) (instDecidableEqNat a x) v 0)) = 0 := by
  split
  . simp
  . simp
    intro
    rename_i h
    subst h
    contradiction

theorem pwc_progress (fuel n : ℕ) :
  prob_while_cut loop_cond loop_body (fuel + 2) (true,n) (false,n + fuel + 1) = (1/2)^(fuel + 1) := by
  revert n
  induction fuel
  . intro n
    simp [geometric_succ_true]
  . rename_i fuel IH
    intro n
    rw [geometric_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    simp [A]
    have B : n + succ fuel + 1 = (n + 1) + fuel + 1 := by exact Nat.add_right_comm n (succ fuel) 1
    simp [B]
    simp [IH (n + 1)]
    rw [← _root_.pow_succ]

theorem pwc_progress' (n : ℕ) (h : ¬ n = 0) :
  prob_while_cut loop_cond loop_body (n + 1) (true, 0) (false, n) = 2⁻¹ ^ n := by
  have prog := pwc_progress (n - 1) 0
  simp at prog
  have A : n - 1 + 1 = n := by exact succ_pred h
  rw [A] at prog
  have B : n - 1 + 2 = n + 1 := by exact succ_inj.mpr A
  rw [B] at prog
  trivial

theorem pwc_advance_gen (fuel fuel' n : ℕ) (h1 : fuel ≥ fuel') :
  prob_while_cut loop_cond loop_body (1 + fuel + 2) (true,n) (false,n + fuel' + 1)
  =
  prob_while_cut loop_cond loop_body (fuel + 2) (true,n) (false,n + fuel' + 1) := by
  revert fuel' n
  induction fuel
  . intro fuel' n h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [geometric_succ_true]
  . rename_i fuel IH
    intro fuel' n h1
    conv =>
      congr
      . rw [geometric_succ_true]
      . rw [geometric_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (n + 1) Pre
    cases fuel'
    . simp at *
    . rename_i fuel'
      have C : succ fuel' - 1 = fuel' := by exact rfl
      rw [C] at IH'
      have D : n + 1 + fuel' + 1 = n + succ fuel' + 1 := by exact
        (Nat.add_right_comm n (succ fuel') 1).symm
      rw [D] at IH'
      rw [IH']
      exact rfl

theorem pwc_advance_gen' (n m : ℕ) (h1 : ¬ m = 0) (h2 : n ≥ m) :
  prob_while_cut loop_cond loop_body (n + 2) (true,0) (false,m)
  =
  prob_while_cut loop_cond loop_body (n + 1) (true,0) (false,m) := by
  have prog := pwc_advance_gen (n - 1) (m - 1) 0
  have P : ¬ n = 0 := by
      by_contra
      rename_i h
      subst h
      simp at h2
      subst h2
      contradiction
  have A : 1 + (n - 1) + 2 = n + 2 := by
    conv =>
      left
      left
      rw [add_comm]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [A] at prog
  have B : 0 + (m - 1) + 1 = m := by
    rw [add_assoc]
    rw [Nat.zero_add]
    exact succ_pred h1
  rw [B] at prog
  have C : n - 1 + 2 = n + 1 := by
    have C' : 2 = 1 + 1 := by rfl
    rw [C']
    rw [← add_assoc]
    rw [Nat.add_right_cancel_iff]
    exact succ_pred P
  rw [C] at prog
  apply prog
  exact Nat.sub_le_sub_right h2 1

theorem pwc_characterization (n extra : ℕ) (h : ¬ n = 0) :
  prob_while_cut loop_cond loop_body (extra + (n + 1)) (true,0) (false,n) = 2⁻¹ ^ n := by
  revert n
  induction extra
  . simp
    intro n h
    apply pwc_progress' _ h
  . rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    have A : extra + (n + 1) = (extra + n) + 1 := by exact rfl
    rw [A] at IH'
    rw [← pwc_advance_gen'] at IH'
    . have B : succ extra + (n + 1) = extra + n + 2 := by exact succ_add_eq_add_succ extra (n + 1)
      rw [B]
      trivial
    . trivial
    . exact Nat.le_add_left n extra

theorem geometric_pwc_sup (n : ℕ) :
  ⨆ i, prob_while_cut loop_cond loop_body i (true, 0) (false, n) = if n = 0 then 0 else (1/2)^n := by
  refine iSup_eq_of_tendsto ?hf ?_
  . apply prob_while_cut_monotonic
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat (n + 1))]
    split
    . rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [geometric_monotone_counter]
    . rename_i h
      conv =>
        congr
        intro E
        rw [pwc_characterization _ _ h]
      rw [tendsto_const_nhds_iff]
      simp

theorem if_simpl (x n : ℕ) :
  (@ite ENNReal (x = n) (propDecidable (x = n)) 0 (@ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (2⁻¹ ^ x * (@ite ENNReal (n = x) (propDecidable (n = (false, x).2)) 1 0)))) = 0 := by
  split
  . simp
  . split
    . simp
    . split
      . rename_i h
        subst h
        contradiction
      . simp

@[simp]
theorem geometric_returns_false (n fuel k : ℕ) (b : Bool) :
  prob_while_cut loop_cond loop_body fuel (b, k) (true,n) = 0 := by
  revert n b k
  induction fuel
  . intro n
    simp
  . rename_i fuel IH
    intro n k b
    simp [prob_while_cut,WhileFunctional,loop_body,loop_cond]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [ite_apply]
    split
    . rename_i h
      subst h
      simp [IH]
    . rename_i h
      simp at h
      subst h
      simp [IH]

theorem geometric_apply (n : ℕ) :
  geometric n = if n = 0 then 0 else (1/2)^n := by
  simp [geometric]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [prob_while]
  simp [geometric_pwc_sup]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  conv =>
    left
    right
    right
    intro x
    rw [if_simpl]
  simp

end Geometric
