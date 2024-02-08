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

open PMF Nat Real

noncomputable def DiscreteGaussianSampleLoop (num den t : PNat) : RandomM (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSample t 1
  let y : Nat := Int.natAbs Y
  let n : Nat := (y * t * den - num)^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

noncomputable def DiscreteGaussianSample (num : PNat) (den : PNat) : RandomM ℤ := do
  let ti : Nat := floor (num.val / den)
  let t : PNat := ⟨ ti + 1 , Add1 ti ⟩
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2) sorry
  return r.1

theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (x : ℤ) (_ : σ = (num : ℝ) / (den : ℝ)) :
  (DiscreteGaussianSample num den) x =
  ENNReal.ofReal ((exp (- x^2 / (2 * σ^2))) / (∑' (y : ℤ), exp (- y^2 / (2 * σ^2)))) := sorry
