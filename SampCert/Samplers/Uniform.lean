/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import Mathlib.Data.ENNReal.Basic

open PMF Classical Finset Nat ENNReal

noncomputable def UniformSample (n : PNat) : RandomM Nat := do
  let r ← prob_until (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
  return r

theorem rw1 (n : PNat) :
   (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : ENNReal)
   = (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : NNReal)  := by
  simp

theorem rw2 (n : PNat) : ((↑↑n)⁻¹ : ENNReal) = ((↑↑n)⁻¹ : NNReal) := by
  simp

@[simp]
theorem double_large_enough (n : PNat) (x : Nat) (support : x < n) :
  x < 2 ^ (log 2 ↑(2 * n)) := by
  have A : ∀ m : ℕ, m < 2 ^ (log 2 ↑(2 * m)) := by
    intro m
    cases m
    . simp
    . rename_i m
      have H1 := @Nat.lt_pow_succ_log_self 2 le.refl (succ m)
      have H2 := @Nat.log_mul_base 2 (succ m) le.refl (succ_ne_zero m)
      rw [Nat.mul_comm]
      rw [H2]
      exact H1
  exact Nat.lt_trans support (A ↑n)

@[simp]
theorem rw_ite (n : PNat) (x : Nat) :
  (if x < n then (UniformPowerOfTwoSample (2 * n)) x else 0)
  = if x < n then 1 / 2 ^ log 2 ((2 : PNat) * n) else 0 := by
  split
  rw [UniformPowerOfTwoSample_apply]
  simp
  apply double_large_enough
  trivial
  trivial

@[simp]
theorem UniformSample_apply (n : PNat) (x : Nat) (support : x < n) :
  UniformSample n x = 1 / n := by
  unfold UniformSample
  simp only [Bind.bind, Pure.pure, SubPMF.bind_pure, prob_until_apply_2, decide_eq_true_eq, rw_ite,
   one_div, sum_simple]
  split
  . rw [rw1 n]
    rw [rw2 n]
    have H := div_mul_eq_div_mul_one_div (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹) : NNReal) (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹) : NNReal) (n : NNReal)
    congr
    rw [H]
    simp
  . contradiction


theorem UniformSample_apply_ite (a b : ℕ) (c : PNat) (i1 : b ≤ c) :
  (if a < b then (UniformSample c) a else 0) = if a < b then 1 / (c : ENNReal) else 0 := by
  split
  rename_i i2
  rw [UniformSample_apply]
  exact Nat.lt_of_lt_of_le i2 i1
  trivial
