/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic

open PMF Classical Finset

noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n) sorry
  return r

@[simp]
theorem UniformSample_apply (n : PNat) (x : Nat) (support : x < n) :
  UniformSample n x = 1 / n := by
  unfold UniformSample
  simp
  split
  . sorry
  . contradiction

theorem UniformSample_apply_ite (a b : ℕ) (c : PNat) (i1 : b ≤ c) :
  (if a < b then (UniformSample c) a else 0) = if a < b then 1 / (c : ENNReal) else 0 := by
  split
  rename_i i2
  rw [UniformSample_apply]
  exact Nat.lt_of_lt_of_le i2 i1
  trivial

-- theorem UniformSampleCorrect (n : PNat) :
--   UniformSample n = uniformOfFintype (Fin n) := by
--   ext x
--   unfold UniformSample
--   simp
--   -- rw [prob_until_apply (UniformPowerOfTwoSample (2 * n)) (fun x => decide (x < PNat.val (2 * n))) sorry]
--   -- simp
--   -- unfold UniformPowerOfTwoSample
--   -- unfold UniformPowerOfTwoSample'
--   -- simp
--   -- rw [tsum_fintype]
--   -- rw [tsum_fintype]
--   -- rw [tsum_fintype]
--   -- -- conv =>
--   -- --   left
--   -- --   left
--   -- --   right
--   -- --   intro b
--   -- --   simp
--   -- --   rw [uniformOfFintype_apply]
--   sorry
