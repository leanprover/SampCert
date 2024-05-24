/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Samplers.LaplaceGen.Code
import SampCert.Samplers.Laplace.Basic

noncomputable section

open Classical PMF Nat Real

namespace SLang

@[simp]
theorem DiscreteLaplaceGenSample_apply (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
  ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs (x - μ) / ((num : NNReal) / (den : NNReal)))))) := by
  simp [DiscreteLaplaceGenSample]
  rw [tsum_eq_single (x - μ) (by aesop)]
  simp

theorem DiscreteLaplaceSampleGen_normalizes (num den : PNat) (μ : ℤ) :
  ∑' x : ℤ, (DiscreteLaplaceGenSample num den μ) x = 1 := by
  simp only [DiscreteLaplaceGenSample, Bind.bind, Pure.pure, bind_apply, pure_apply, mul_ite,
    mul_one, mul_zero]
  conv =>
    left
    right
    intro x
    rw [tsum_eq_single (x - μ) (by aesop)]
  simp only [sub_add_cancel, ↓reduceIte]

  simp only [DiscreteLaplaceSample, Bind.bind, Pure.pure, SLang.bind_apply]
  have A := DiscreteLaplaceSampleLoop_normalizes num den
  conv =>
    left
    right
    intro x
    right
    intro a
    rw [prob_until_apply_norm _ _ _ A]
  simp only [ENNReal.tsum_prod']

  rw [ENNReal.tsum_comm]
  conv =>
    left
    right
    intro b
    rw [ENNReal.tsum_comm]
    right
    intro c
    rw [ENNReal.tsum_mul_left]
    right
    simp

  conv =>
    left
    right
    intro b
    right
    intro x
    left
    rw [mul_comm]
  conv =>
    left
    right
    intro b
    right
    intro x
    rw [mul_assoc]
  conv =>
    left
    right
    intro b
    rw [ENNReal.tsum_mul_left]
  conv =>
    left
    rw [ENNReal.tsum_mul_left]

  simp only [not_and, decide_implies, decide_not, dite_eq_ite, Bool.if_true_right,
    Bool.decide_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, tsum_bool,
    true_or, ↓reduceIte, Bool.true_eq_false, false_or, ite_not, ite_mul, zero_mul,
    Bool.false_eq_true]

  sorry



end SLang
