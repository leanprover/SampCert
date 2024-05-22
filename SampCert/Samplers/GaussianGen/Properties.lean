/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Samplers.GaussianGen.Code
import SampCert.Samplers.Gaussian.Properties
import SampCert.Util.Gaussian.DiscreteGaussian
import SampCert.Util.Gaussian.GaussPeriodicity

noncomputable section

open Classical PMF Nat Real

namespace SLang

theorem if_simple_GaussianGen (x_1 x μ : ℤ) :
  (@ite ENNReal (x_1 = x - μ) (propDecidable (x_1 = x - μ)) 0
  (@ite ENNReal (x = x_1 + μ) (x.instDecidableEq (x_1 + μ))
  (ENNReal.ofReal (gauss_term_ℝ (↑↑num / ↑↑den) 0 ↑x_1 / ∑' (x : ℤ), gauss_term_ℝ (↑↑num / ↑↑den) 0 ↑x)) 0)) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      subst h2
      simp at h1
    . simp

theorem DiscreteGaussianGenSample_apply (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteGaussianGenSample num den μ) x =
  ENNReal.ofReal (discrete_gaussian ((num : ℝ) / (den : ℝ)) μ x) := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  simp [DiscreteGaussianGenSample, discrete_gaussian]
  rw [ENNReal.tsum_eq_add_tsum_ite (x - μ)]
  simp
  conv =>
    left
    right
    right
    intro y
    rw [if_simple_GaussianGen]
  simp only [tsum_zero, add_zero]
  congr 2
  . simp [gauss_term_ℝ]
  . rw [SG_periodic' A]

end SLang
