/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform

open Pmf

noncomputable def BernoulliSample (num : Nat) (den : PNat) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

-- #check Finset.filter_gt_eq_Iio
theorem BernoulliSampleCorrect (num : Nat) (den : PNat) :
  BernoulliSample num den true = num / den := by
  simp
  unfold BernoulliSample
  rw [UniformSampleCorrect]
  simp
  rw [tsum_fintype]
  --rw [sum_ite]
  --simp
  sorry
