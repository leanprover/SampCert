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

-- Not clear that this is a very elegant way to prove it,
-- it may be possible and informative to prove a weaker version
theorem geometric_returns_false (n fuel k : ℕ) (b : Bool) :
  prob_while_cut loop_cond loop_body fuel (b, k) (true,n) = 0 := by
  revert n b k
  induction fuel
  . intro n
    simp [prob_while_cut]
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

theorem zero_case_gen (fuel : ℕ) (st : Bool × ℕ) (h : st ≠ (false,0)) :
  prob_while_cut loop_cond loop_body fuel st (false, 0) = 0 := by
  revert st
  induction fuel
  . simp [prob_while_cut]
  . rename_i fuel IH
    intro st h
    simp [prob_while_cut, WhileFunctional]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [ite_apply]
    split
    . simp
      constructor
      . intro b
        cases b
        . left
          simp
        . right
          apply IH
          simp
      . intro b
        right
        apply IH
        simp
    . rename_i h'
      simp at h
      split
      . rename_i h''
        rw [h''] at h
        contradiction
      . simp

-- In the inductive case, the execution of the loop body and bind
-- will sum over all the states of the inner pwc
-- So we need the IH to be stated in terms of a general state
-- And the states that do not apply should simplify to something useful
-- for the left argument of the bind

theorem ite_simpl (x a : ℕ) (v : ENNReal) :
  (@ite ENNReal (x = a) (propDecidable (x = a)) 0 (@ite ENNReal (x = a) (instDecidableEqNat x a) v 0)) = 0 := by
  split
  . simp
  . simp

theorem ite_simpl' (x a : ℕ) (v : ENNReal) :
  (@ite ENNReal (x = a) (propDecidable (x = a)) 0 (@ite ENNReal (a = x) (instDecidableEqNat a x) v 0)) = 0 := by
  split
  . simp
  . simp
    intro
    rename_i h
    subst h
    contradiction

theorem pwc_false_to_false (fuel K n : ℕ) :
  prob_while_cut loop_cond loop_body fuel (false, K) (false, n) =
  prob_while_cut loop_cond loop_body fuel (false, K + 1) (false, n + 1) := by
  cases fuel
  . simp [prob_while_cut]
  . simp [prob_while_cut, WhileFunctional, loop_cond]

theorem pwc_shift' (fuel K₁ n : ℕ) (b : Bool) :
  prob_while_cut loop_cond loop_body fuel (b, K₁) (false, n)
  =
  prob_while_cut loop_cond loop_body fuel (b, K₁ + 1) (false, n + 1) := by
  revert K₁ n
  induction fuel
  . simp [prob_while_cut]
  . rename_i fuel IH
    intro K₁ n
    unfold prob_while_cut
    unfold WhileFunctional
    split
    -- Left execution continued
    . split
      -- right execution continues -> induction
      . rename_i h1 h2
        simp [loop_cond] at *
        subst h1
        clear h2
        -- loop_body constrains the state (a) bound in the sums
        simp [ENNReal.tsum_prod', tsum_bool]
        conv =>
          congr
          . congr
            . rw [ENNReal.tsum_eq_add_tsum_ite (K₁ + 1)]
              right
              right
              intro x
              rw [ite_simpl]
            . rw [ENNReal.tsum_eq_add_tsum_ite (K₁ + 1)]
              right
              right
              intro x
              rw [ite_simpl]
          . congr
            . rw [ENNReal.tsum_eq_add_tsum_ite (K₁ + 1 + 1)]
              right
              right
              intro x
              rw [ite_simpl]
            . rw [ENNReal.tsum_eq_add_tsum_ite (K₁ + 1 + 1)]
              right
              right
              intro x
              rw [ite_simpl]
        simp
        have IH' := IH (K₁ + 1) n
        clear IH
        rw [← IH']
        clear IH'
        refine
          (Mathlib.Tactic.LinearCombination.pf_add_c ?succ.inl.inl.p
              (2⁻¹ * prob_while_cut loop_cond loop_body fuel (true, K₁ + 1) (false, n))).symm
        refine (Mathlib.Tactic.LinearCombination.c_mul_pf ?succ.inl.inl.p.p 2⁻¹).symm

        -- We now need to deal with the case where the starting state is false
        apply pwc_false_to_false

      -- Right execution stopped -> contradiction
      . simp
        rename_i h1 h2
        simp [loop_cond] at *
        subst h1
        contradiction
    -- Left execution stopped
    . split
      -- Right execution continued -> contradiction
      . simp
        rename_i h1 h2
        simp [loop_cond] at *
        subst h1
        contradiction
      -- Right execution stopped
      . simp

theorem pwc_shift (fuel K₁ K₂ n : ℕ) (b : Bool) :
  prob_while_cut loop_cond loop_body fuel (b, K₁) (false, n)
  =
  prob_while_cut loop_cond loop_body fuel (b, K₁ + K₂) (false, n + K₂) := by
  revert K₁ n
  induction K₂
  . simp
  . rename_i K₂ IH
    intro K₁ n
    have IH' := IH (K₁ + 1) (n + 1)
    clear IH
    have A := pwc_shift' fuel K₁ n b
    rw [A, IH']
    clear A IH'
    have B : K₁ + 1 + K₂ = K₁ + succ K₂ := succ_add_eq_add_succ K₁ K₂
    have C : n + 1 + K₂ = n + succ K₂ := succ_add_eq_add_succ n K₂
    simp [B,C]

theorem false_to_false (fuel n K : ℕ) :
  prob_while_cut loop_cond loop_body fuel (false, n) (false, n + 1 + K) = 0 := by
  cases fuel
  . simp [prob_while_cut]
  . simp [prob_while_cut, WhileFunctional, loop_cond]
    intro h
    sorry

-- property should count the number of flips
-- and distinguish with starting counter?
-- or maybe I could consider the fuel being consumed?

-- prob_while_cut loop_cond loop_body (succ fuel) st (false, n)
-- = k * prob_while_cut loop_cond loop_body fuel ?? ...

theorem pwc_progress (fuel n : ℕ) :
  prob_while_cut loop_cond loop_body (fuel + 2) (true,n) (false,n + fuel + 1)
  = (1/2)^(fuel + 1) := by
  revert n
  induction fuel
  . intro n
    simp [prob_while_cut, WhileFunctional, loop_cond, loop_body]
    simp [ENNReal.tsum_prod',tsum_bool]
    rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
    simp
    conv =>
      left
      right
      right
      intro x
      rw [ite_simpl']
    simp
  . rename_i fuel IH
    intro n
    unfold prob_while_cut
    unfold WhileFunctional
    simp
    unfold SubPMF.pure
    unfold SubPMF.bind
    simp only [loop_cond, loop_body]
    simp [ENNReal.tsum_prod',tsum_bool]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    simp [A]
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
      right
      right
      intro x
      rw [ite_simpl]
    simp
    have B : n + succ fuel + 1 = (n + 1) + fuel + 1 := by exact Nat.add_right_comm n (succ fuel) 1
    simp [B]
    simp [IH (n + 1)]
    conv =>
      left
      left
      rw [ENNReal.tsum_eq_add_tsum_ite (n + 1)]
      right
      right
      intro x
      rw [ite_simpl]
    simp
    have C : n + 1 + fuel + 1 = n + 1 + 1 + fuel := by exact Nat.add_right_comm (n + 1) fuel 1
    rw [C]
    rw [false_to_false]
    simp
    rw [← _root_.pow_succ]

theorem geometric_pwc_sup (n : ℕ) :
  ⨆ i, prob_while_cut loop_cond loop_body i (true, 0) (false, n) = if n = 0 then 0 else (1/2)^n := by
  refine iSup_eq_of_tendsto ?hf ?_
  . apply prob_while_cut_monotonic
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat (n + 2))]
    split
    . rename_i h
      subst h
      simp
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n H
      simp [zero_case_gen]
    . rename_i h
      sorry

@[simp]
theorem sum_range_low (n : ℕ) :
  (∑ i in range n, (@ite ENNReal (i = 0) (instDecidableEqNat i 0) 0 (2⁻¹ ^ i * @ite ENNReal (n = ↑i) (propDecidable (n = ↑i)) 1 0))) = 0 := by
  induction n
  . simp
  . rename_i n IH
    simp
    intro x H
    have A : succ n = x ↔ false := by
      by_contra h
      simp at h
      subst h
      simp at H
    simp [A]

@[simp]
theorem ite_sum_singleout (n : ℕ) :
  (∑' (b : ℕ), (@ite ENNReal (b = 0) (instDecidableEqNat b 0) 0 (2⁻¹ ^ b * @ite ENNReal (n = ↑b) (propDecidable (n = ↑b)) 1 0)) ) =  (@ite ENNReal (n = 0) (propDecidable (n = 0)) 0 (2⁻¹ ^ n)):= by
  rw [← @sum_add_tsum_nat_add' _ _ _ _ _ _ (n + 1)]
  . have A : ∀ i : ℕ, (n = i + (n + 1)) ↔ false := by sorry
    conv =>
      left
      right
      right
      intro i
      simp [A]
    simp
    clear A
    simp [sum_range_succ]
    split
    . simp
    . simp
  . exact ENNReal.summable

theorem final (n : ℕ) :
  geometric n = if n = 0 then 0 else (1/2)^n := by
  simp [geometric]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [prob_while]
  conv =>
    left
    right
    right
    intro b
    left
    right
    intro i
    rw [geometric_returns_false]
  conv =>
    left
    right
    simp
  simp only [add_zero]
  simp [geometric_pwc_sup]
  split
  . simp
  . simp

end Geometric
