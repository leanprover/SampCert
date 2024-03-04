/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Uniform

open PMF SubPMF Finset BigOperators

noncomputable def BernoulliSample (num : Nat) (den : PNat) (_ : num ≤ den) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

@[simp]
theorem BernoulliSample_apply_true (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample num den wf true = num / den := by
  unfold BernoulliSample
  simp
  conv =>
    left
    right
    intro a
    rw [UniformSample_apply_ite _ _ _ wf]
  simp
  rw [ENNReal.div_eq_inv_mul]

-- Two possible proofs:
-- 1. Direct
-- 2. Remembering that Uniform is a PMF
@[simp]
theorem BernoulliSample_apply_false (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample num den wf false = (den - num) / den := by
  unfold BernoulliSample
  simp
  -- need to split the sum as behavior is different for a < den or a ≥ den
  sorry

#check sum_add_tsum_nat_add'

theorem BernoulliSample_normalizes (num : Nat) (den : PNat) (wf : num ≤ den) :
  ∑ b : Bool, BernoulliSample num den wf b = 1 := by
  simp
  rw [ENNReal.div_add_div_same]
  rw [AddCommMonoid.add_comm]
  induction num
  . simp
    sorry
  . rename_i n IH
    have A : n ≤ ↑den := by exact Nat.le_of_lt_succ (Nat.le.step wf)
    have IH' := IH A
    clear IH A wf
    sorry


noncomputable def BernoulliSamplePMF (num : Nat) (den : PNat) (wf : num ≤ den) : PMF Bool := PMF.ofFintype (BernoulliSample num den wf) (BernoulliSample_normalizes num den wf)

theorem ndle1 (num : Nat) (den : PNat) (wf : num ≤ den) :
  (num : ENNReal) / (den : ENNReal) ≤ 1 := by sorry

theorem BernoulliSample_distr (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSamplePMF num den wf = bernoulli (num / den) (ndle1 num den wf) := by
  ext x
  sorry

noncomputable def BernoulliSample' (num : Nat) (den : PNat) (_ : num ≤ den) : RandomM Bool := do
  let d ← uniformOfFintype (Fin den)
  return d < num

@[simp]
theorem BernoulliSample'_apply_true (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample' num den wf true = num / den := by
  simp [BernoulliSample']
  sorry

@[simp]
theorem BernoulliSample'_apply_false (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample' num den wf false = 1 - (num / den) := by
  simp [BernoulliSample']
  sorry


theorem BernoulliSample'_normalizes (num : Nat) (den : PNat) (wf : num ≤ den) :
  ∑ b : Bool, BernoulliSample' num den wf b = 1 := by
  simp
  rw [add_tsub_cancel_iff_le]
  induction num
  . simp
  . rename_i n IH
    have A : n ≤ ↑den := by exact Nat.lt_succ.mp (Nat.le.step wf)
    have IH' := IH A
    clear IH A wf
    simp
    sorry
