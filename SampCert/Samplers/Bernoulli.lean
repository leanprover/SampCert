/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform

open PMF

noncomputable def BernoulliSample (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

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
