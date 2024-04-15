/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import SampCert.Foundations.UtilMathlib
import SampCert.DiffPrivacy.GaussBound

open Classical Nat Real

@[simp]
theorem GaussConvergence (μ ss : ℝ) (h : ss > 0) :
  Summable fun (n : ℤ) => sg' ss μ n := by
  unfold sg'
  conv =>
    right
    intro i
    rw [division_def]

  have A : ∀ n : ℤ, (-(n - μ) ^ 2 * (2 * ss)⁻¹) = (- n^2 * (2 * ss)⁻¹) + (2 * μ * n * (2 * ss)⁻¹) + (- μ^2 * (2 * ss)⁻¹) := by
    intro n
    ring_nf

  conv =>
    right
    intro i
    rw [A]
    rw [exp_add]

  apply Summable.mul_right

  clear A

  have B : 0 < (Complex.I * ↑(2 * ss)⁻¹ * ↑π⁻¹).im := by
    simp only [mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
      Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.inv_re, Complex.ofReal_re,
      Complex.normSq_ofReal, div_self_mul_self', Complex.re_ofNat, Complex.normSq_ofNat,
      Complex.inv_im, Complex.ofReal_im, neg_zero, zero_div, Complex.im_ofNat, mul_zero, sub_zero,
      zero_mul, Complex.I_im, add_zero, sub_self, one_mul, zero_add, gt_iff_lt, inv_pos, h,
      mul_pos_iff_of_pos_left, ofNat_pos, pi_pos]

  have C := @summable_jacobiTheta₂_term_iff (μ * (2 * ss)⁻¹ * π⁻¹ * Complex.I⁻¹) (Complex.I * (2 * ss)⁻¹ * π⁻¹)
  replace C := C.symm.1 B
  clear B

  unfold jacobiTheta₂_term at C
  apply (RCLike.summable_ofReal ℂ).mp

  apply Summable.congr C
  clear C

  intro b
  have D := Complex.ofReal_exp (-↑b ^ 2 * (2 * ss)⁻¹ + 2 * μ * ↑b * (2 * ss)⁻¹)
  have E : ∀ x : ℝ, Complex.ofReal' x = @RCLike.ofReal ℂ Complex.instRCLikeComplex x := fun x => rfl
  rw [← E, D]
  clear D E

  congr 1
  rw [add_comm]
  simp only [mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.inv_I, mul_neg, neg_mul, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_int_cast]
  congr 1
  . ring_nf
    simp only [Complex.I_sq, mul_neg, mul_one, neg_mul, one_div]
    ring_nf
    congr 1
    rw [← mul_rotate]
    congr 1
    ring_nf
    have T : (π : ℂ) ≠ 0 := by
      simp [pi_ne_zero]
    rw [mul_inv_cancel T]
    simp only [one_mul]
  . ring_nf
    simp only [Complex.I_sq, mul_neg, mul_one, neg_mul, neg_neg]
    rw [← mul_rotate]
    congr 1
    ring_nf
    congr 1
    have T : (π : ℂ) ≠ 0 := by
      simp [pi_ne_zero]
    rw [mul_inv_cancel T]
    simp only [one_mul]

@[simp]
theorem GaussConvergence' (μ ss : ℝ) (h : ss > 0) :
  Summable fun (n : ℕ) => sg' ss μ n := by
  have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun (n : ℤ) => sg' ss μ n)
  replace A := A.1 (GaussConvergence μ ss h)
  cases A
  simpa only
