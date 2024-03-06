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

#check WhileFunctional loop_cond loop_body


theorem test_prop_1 (b : Bool) (K : ℕ) :
  loop_body (b,K) (false,K) = 0 := by
  simp [loop_body]

theorem test_prop_2 (b : Bool) (K : ℕ) :
  loop_body (b,K) (false,K+1) = 2⁻¹ := by
  simp [tsum_bool,loop_body]

theorem test_prop_3 (b : Bool) (K : ℕ) :
  loop_body (b,K) (true,K+1) = 2⁻¹ := by
  simp [tsum_bool,loop_body]

theorem test_prop_4 (b : Bool) (K : ℕ) :
  loop_body (b,K) (false,K+4) = 0 := by
  simp [tsum_bool,loop_body]

-- ¬ st.1 → st.2 > 0
theorem invariant (fuel : ℕ) :
  prob_while_cut loop_cond loop_body fuel (true, 0) (false, 0) = 0 := by
  sorry

theorem zero_case (fuel : ℕ) :
  prob_while_cut loop_cond loop_body fuel (true, 0) (false, 0) = 0 := by
  sorry -- actually interesting to prove because it needs to show that K
  -- always increases

theorem core (n : ℕ) :
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
      simp [zero_case]
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
  simp [core]
  split
  . simp
  . simp

end Geometric
