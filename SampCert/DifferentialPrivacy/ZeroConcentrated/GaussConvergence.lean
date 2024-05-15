/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.DiscreteGaussian

open Classical Nat Real

@[simp]
theorem GaussConvergenceNatPos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) n := by
  have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) n)
  replace A := A.1 (summable_gauss_term' h μ)
  cases A
  simpa only

@[simp]
theorem GaussConvergenceNatNeg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((-(n + 1)) : ℤ) := by
  have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun (n : ℤ) => (gauss_term_ℝ σ μ) n)
  replace A := A.1 (summable_gauss_term' h μ)
  cases A
  simpa only
