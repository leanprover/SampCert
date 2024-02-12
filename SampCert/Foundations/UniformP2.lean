/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Random
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Nat.Log
import SampCert.Foundations.Util
import SampCert.Foundations.SubPMF



open Nat Classical SubPMF PMF
-- Assumption: the Dafny version indeed has this spec

noncomputable def UniformPowerOfTwoSample (n : PNat) : RandomM Nat :=
  toSubPMF (uniformOfFintype (Fin (2 ^ (log 2 n))))

@[simp]
theorem test1 (b x : ℕ) :
  ((if (x = ↑b : Prop) then 1 else 0): ENNReal)
  = if ↑b = x then 1 else 0 := by
  split
  . rename_i h
    subst h
    simp
  . rename_i h
    split
    . rename_i h2
      rw [h2] at h
      contradiction
    . trivial

@[simp]
theorem test (b x : ℕ) :
  (∑' (b : Fin b), if x = ↑b then 1 else 0)
  = ∑' (b : Fin b), if ↑b = x then 1 else 0 := by
  congr
  ext y
  split
  . rename_i h
    subst h
    simp
  . rename_i h
    split
    . rename_i h2
      rw [h2] at h
      contradiction
    . trivial

@[simp]
theorem UniformPowerOfTwoSample_apply (n : PNat) (x : Nat) (h : x < 2 ^ (log 2 n)) :
  (UniformPowerOfTwoSample n) x = 1 / (2 ^ (log 2 n)) := by
  unfold UniformPowerOfTwoSample
  simp
  rw [tsum_fintype]
  rw [← @Finset.mul_sum]
  rw [@Fin.sum_univ_def]
  sorry -- looks good
