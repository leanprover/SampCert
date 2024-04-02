/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential
import SampCert.Samplers.Laplace

open Classical PMF Nat Real

noncomputable def DiscreteGaussianSampleLoop (num den t : PNat) : RandomM (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSample t 1
  let y : Nat := Int.natAbs Y
  let n : Nat := (y * t * den - num)^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

@[simp]
theorem ite_simpl_1' (num den t : PNat) (x : ℤ) (n : ℕ) :
  @ite ENNReal (x = ↑n) (propDecidable (x = ↑n)) 0
  (@ite ENNReal (↑n = x) (Int.instDecidableEqInt (↑n) x)
  (ENNReal.ofReal ((rexp ((t : ℝ))⁻¹ - 1) / (rexp ((t : ℝ))⁻¹ + 1) * rexp (-(Complex.abs ↑x / ↑↑t))) *
    ENNReal.ofReal (rexp (-(↑(↑(Int.natAbs x) * (t : NNReal) * (den : NNReal) - (num : NNReal)) ^ 2 / ((2 : ℕ+) * ↑↑num * ↑↑t ^ 2 * ↑↑den)))))
  0) = 0 := by
  split
  . simp
  . rename_i h
    simp [h]
    intro h
    subst h
    contradiction

@[simp]
theorem DiscreteGaussianSampleLoop_apply_true (num den t : ℕ+) (n : ℕ) :
  (DiscreteGaussianSampleLoop num den t) (n, true) =
    ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1) * rexp (-(n / t))) *
    ENNReal.ofReal (rexp (-((n * t * den - num) ^ 2 / ((2 : ℕ+) * num * t ^ 2 * den)))) := by
  simp [DiscreteGaussianSampleLoop, tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
  simp (config := { contextual := true })
  sorry

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

noncomputable def DiscreteGaussianSample (num : PNat) (den : PNat) : RandomM ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , Add1 ti ⟩
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2)
  return r.1

@[simp]
theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (x : ℤ) :
  (DiscreteGaussianSample num den) x =
  ENNReal.ofReal ((exp (- x^2 / (2 * ((num : ℝ) / (den : ℝ))^2))) / (∑' (y : ℤ), exp (- y^2 / (2 * ((num : ℝ) / (den : ℝ))^2)))) := by
  simp [DiscreteGaussianSample, ENNReal.tsum_prod', tsum_bool]
