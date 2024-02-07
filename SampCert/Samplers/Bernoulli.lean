/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform

open PMF Finset

noncomputable def BernoulliSample (num : Nat) (den : PNat) : RandomM Bool := do
  let d ← UniformSample den
  return d < num

theorem BernoulliSample_apply_true (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample num den true = num / den := by
  unfold BernoulliSample
  simp
  conv =>
    left
    right
    intro a
    rw [UniformSample_apply _ _ sorry]
  have H := sum_simple num (1 / ↑↑den)
  have H2 : 1 / (den : ENNReal) * (num : ENNReal) = num / den := sorry
  rw [H2] at H
  rw [← H]
