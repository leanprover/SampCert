/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import SampCert.Foundations.UtilMathlib

open Classical Nat Real

@[simp]
theorem GaussConvergence (ss : ℝ) (h : ss > 0):
  Summable fun (i : ℤ) => rexp (-i ^ 2 / (2 * ss)) := by
  conv =>
    right
    intro i
    rw [division_def]
  have A := @summable_exp_mul_sq (Complex.I / (2 * π * ss))
  have B : ∀ n : ℤ, (π : ℂ) * Complex.I * ↑n ^ 2 * (Complex.I / (2 * ↑π * ss))
    = -n ^ 2 / (2 * ss) := by
    intro n
    rw [division_def]
    rw [mul_inv]
    rw [mul_inv]
    rw [division_def]
    rw [mul_inv]
    rw [← mul_rotate]
    conv =>
      rw [mul_comm]
    rw [neg_mul_comm]
    congr 1
    rw [← mul_assoc]
    rw [← mul_assoc]
    rw [← mul_assoc]
    rw [← mul_rotate]
    rw [← mul_assoc]
    rw [← mul_assoc]
    rw [← mul_assoc]
    simp only [Complex.I_mul_I, neg_mul, one_mul, inv_inv, mul_inv_rev, neg_inj]
    rw [mul_assoc]
    rw [mul_assoc]
    congr 1
    rw [mul_comm]
    rw [mul_assoc]
    have B : (π : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr ?_
      exact pi_ne_zero
    rw [mul_inv_cancel B]
    simp only [mul_one]

  simp only [B] at A
  clear B
  conv =>
    right
    intro i
    rw [← division_def]

  have C : ∀ n : ℤ, Complex.exp (-n ^ 2 / (2 * ss)) = rexp (-n ^ 2 / (2 * ss)) := by
    intro n
    simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_int_cast, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_nat_cast]

  have D : 0 < (Complex.I / (2 * (π : ℂ) * (ss : ℂ))).im := by
    rw [Complex.div_im]
    simp only [Complex.I_im, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, one_mul, map_mul,
      Complex.normSq_ofNat, Complex.normSq_ofReal, map_div₀, map_pow, Complex.normSq_nat_cast,
      Complex.I_re, zero_div]
    rw [division_def]
    rw [mul_inv]
    rw [mul_pos_iff]
    left
    constructor
    . rw [mul_pos_iff]
      left
      simp only [gt_iff_lt, zero_lt_two, mul_pos_iff_of_pos_left]
      constructor
      . exact pi_pos
      . exact h
    . simp only [mul_inv_rev, inv_inv]
      rw [mul_pos_iff]
      left
      simp only [gt_iff_lt, inv_pos, zero_lt_two, mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_right,
        mul_self_pos, ne_eq, inv_eq_zero, cast_eq_zero, PNat.ne_zero, not_false_eq_true, pow_pos,
        cast_pos, PNat.pos, and_true]
      constructor
      . exact pi_ne_zero
      . exact OrderIso.mulLeft₀.proof_1 ss h

  have Y := A D
  clear A D
  revert Y
  conv =>
    left
    right
    intro n
    rw [C]
  clear C
  intro Y
  apply (RCLike.summable_ofReal ℂ).mp Y
