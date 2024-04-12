/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Defs.Filter
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Topology.ContinuousFunction.Algebra

noncomputable section

open Classical Nat BigOperators Real
open FourierTransform GaussianFourier Filter Asymptotics Complex
open ContinuousMap Function

attribute [local instance] Real.fact_zero_lt_one

def sg (ss μ : ℝ) : ℝ → ℂ := fun x : ℝ => rexp (- ((x - μ)^2) / (2 * ss))
def fourier_sg (ss : ℝ) : ℝ → ℂ := fun x : ℝ ↦ (((π)⁻¹ * (ss)⁻¹ * (2 : ℝ)⁻¹) ^ (2 : ℝ)⁻¹)⁻¹ * rexp ( - 2 * π^2 * ss * x^2)

theorem CharFourierSG (ss : ℝ) (h : ss > 0) :
  𝓕 (sg ss 0) = fourier_sg ss := by

  unfold fourier_sg

  have P : 0 < (π * (2 : ℂ) * ss)⁻¹.re  := by
    simp [h, pi_pos]

  have X := @fourierIntegral_gaussian_pi' (π * 2 * ss)⁻¹ P 0
  rw [mul_inv] at X
  rw [mul_inv] at X
  rw [neg_mul_comm] at X
  rw [mul_assoc] at X
  rw [neg_mul_eq_mul_neg] at X
  rw [← mul_assoc] at X
  have T : (π : ℂ) ≠ 0 := by
    simp [pi_ne_zero]
  rw [mul_inv_cancel T] at X
  simp at X
  rw [← mul_inv] at X

  have R : (fun (x : ℝ) => cexp (-(((2 : ℂ) * ss)⁻¹ * x ^ 2))) = (fun (x : ℝ) => cexp (-x ^ 2 / (2 * ss))) := by
    ext y
    congr
    rw [neg_div]
    congr 1
    rw [mul_comm]
    rw [division_def]

  unfold sg
  simp

  rw [R] at X
  rw [X]
  ext t
  congr 1
  . simp
    ring_nf
    simp
    rw [ext_iff]
    constructor
    . simp
      rw [rpow_def]
      simp
    . simp
      have A : ((π)⁻¹ * (ss)⁻¹ * (2 : ℂ)⁻¹).im = 0 := by
        simp
      rw [cpow_inv_two_im_eq_sqrt]
      . simp
        have P1 : |π| = π := by
          rw [_root_.abs_of_nonneg]
          rw [le_iff_lt_or_eq]
          left
          apply pi_pos
        have P2 : |ss| = ss := by
          rw [_root_.abs_of_nonneg]
          rw [le_iff_lt_or_eq]
          left
          simp [h]
        rw [P1, P2]
        simp
      . rw [← A]
        simp
  . rw [division_def]
    simp
    ring_nf

theorem SGPoi (ss : ℝ) (h : ss > 0) (x : ℝ) :
  (∑' (n : ℤ), sg ss 0 (x + n)) = ∑' (n : ℤ), 𝓕 (sg ss 0) n * (@fourier 1 n) (x : UnitAddCircle) := by

  let g : ℝ → ℂ := fun x ↦ Complex.exp (- (x^2) / (2 * ss))

  have A : Continuous g := by
    apply Complex.continuous_exp.comp
    apply Continuous.div_const
    apply Continuous.neg
    apply Continuous.pow
    exact Complex.continuous_ofReal

  have B : 𝓕 g = fun x : ℝ ↦ (((π)⁻¹ * (ss)⁻¹ * (2 : ℂ)⁻¹) ^ (2 : ℂ)⁻¹)⁻¹ * Complex.exp ( - 2 * π^2 * ss * x^2) := by
    have P : 0 < (π * (2 : ℂ) * ss)⁻¹.re  := by
      simp [h, pi_pos]

    have X := @fourierIntegral_gaussian_pi' (π * 2 * ss)⁻¹ P 0
    rw [mul_inv] at X
    rw [mul_inv] at X
    rw [neg_mul_comm] at X
    rw [mul_assoc] at X
    rw [neg_mul_eq_mul_neg] at X
    rw [← mul_assoc] at X
    have T : (π : ℂ) ≠ 0 := by
      simp [pi_ne_zero]
    rw [mul_inv_cancel T] at X
    simp at X
    rw [← mul_inv] at X

    simp only [g]

    have R : (fun (x : ℝ) => cexp (-(((2 : ℂ) * ss)⁻¹ * x ^ 2))) = (fun (x : ℝ) => cexp (-x ^ 2 / (2 * ss))) := by
      ext y
      congr
      rw [neg_div]
      congr 1
      rw [mul_comm]
      rw [division_def]

    rw [R] at X
    rw [X]
    ext t
    congr 1
    . simp
      ring_nf
    . rw [division_def]
      simp
      ring_nf

  have C : g =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
    apply IsLittleO.isBigO
    have P : (-(1 : ℂ) / (2 * ss)).re < 0 := by
      simp [div_eq_mul_inv, h]

    have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-1 / (2 * ss)) P 0 (-2)
    simp only [zero_mul, add_zero] at X
    revert X
    conv =>
      enter [1, 2, x, 1]
      rw [mul_comm]
      rw [mul_div]
      rw [mul_neg]
      rw [mul_one]
    intro X
    trivial

  have D : (𝓕 g) =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
    apply IsLittleO.isBigO
    rw [B]
    apply IsLittleO.const_mul_left
    have P : (-(2 : ℂ) * π ^ 2 * ss).re < 0 := by
      simp [h, pow_two, pi_ne_zero]

    have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-2 * ↑π ^ 2 * ss) P 0 (-2)
    simp only [zero_mul, add_zero] at X
    trivial

  have E := Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay A one_lt_two C D

  have F : (sg ss 0) = g := by
    ext x
    simp [sg]
  rw [F]

  apply E

def sg' (ss μ : ℝ) : ℝ → ℝ := fun x : ℝ => rexp (- ((x - μ)^2) / (2 * ss))
def fourier_sg' (ss : ℝ) : ℝ → ℝ := fun x : ℝ ↦ (((π)⁻¹ * (ss)⁻¹ * (2 : ℝ)⁻¹) ^ (2 : ℝ)⁻¹)⁻¹ * rexp ( - 2 * π^2 * ss * x^2)

instance myfun (ss : ℝ) : C(ℝ,ℂ) where
  toFun := (sg ss 0)
  continuous_toFun := by
    unfold sg
    simp
    apply Continuous.cexp
    apply Continuous.div_const
    apply Continuous.neg
    apply Continuous.pow
    exact continuous_ofReal

theorem SGFourierSummable (ss μ : ℝ) (h : ss > 0) :
  Summable fun (n : ℤ) => ‖𝓕 (sg ss 0) n * (@fourier 1 n) (-μ)‖ := by
  rw [summable_norm_iff]

  -- I'm repeating myself, I need to lift this
  have A : (𝓕 (sg ss 0)) =O[cocompact ℝ] (fun (x : ℝ) => ((|x| ^ (-2 : ℝ)) : ℝ)) := by
    apply IsLittleO.isBigO
    rw [CharFourierSG ss h]
    unfold fourier_sg
    apply IsLittleO.const_mul_left
    have P : (-(2 : ℂ) * π ^ 2 * ss).re < 0 := by
      simp [h, pow_two, pi_ne_zero]
    have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-2 * ↑π ^ 2 * ss) P 0 (-2)
    simp only [zero_mul, add_zero] at X
    simp at X
    simp [X]

  have B : Summable fun n : ℤ => 𝓕 (sg ss 0) n := by

    have X : Summable fun (x : ℤ) => (|x| ^ (-(2 : ℝ)) : ℝ) := by
      have S := @Real.summable_abs_int_rpow 2 one_lt_two
      simp at S
      simp [S]

    have Y : ((fun (z : ℤ) => 𝓕 (sg ss 0) z) =O[cofinite] fun (x : ℤ) => (|x| ^ (-(2 : ℝ)) : ℝ)) := by
      have P2 := @IsBigO.comp_tendsto ℝ ℤ ℂ ℝ _ _ (𝓕 (sg ss 0)) (fun (x : ℝ) => ((|x| ^ (-2 : ℝ)) : ℝ)) (cocompact ℝ) A Int.cast cofinite Int.tendsto_coe_cofinite

      have Q1 : (𝓕 (sg ss 0) ∘ Int.cast) = (fun (z : ℤ) => 𝓕 (sg ss 0) ↑z) := rfl
      have Q2 : ((fun (x : ℝ) => |x| ^ (-(2 : ℝ))) ∘ Int.cast) = fun x => @Int.cast ℝ instIntCast |x| ^ (-(2 : ℝ)) := by
        funext x
        simp

      rw [Q1] at P2
      rw [Q2] at P2

      exact P2

    have Z := @summable_of_isBigO ℤ ℂ _ _ (fun z : ℤ => 𝓕 (sg ss 0) z) (fun x : ℤ => |x| ^ (-2 : ℝ)) X Y
    trivial

  have C : Continuous (sg ss 0) := by
    unfold sg
    simp
    apply Continuous.cexp
    apply Continuous.div_const
    apply Continuous.neg
    apply Continuous.pow
    exact continuous_ofReal

  let F : C(UnitAddCircle, ℂ) :=
    ⟨((myfun ss).periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩

  have D : ∀ n : ℤ, fourierCoeff F n = 𝓕 (sg ss 0) n := by
    intro n
    apply Real.fourierCoeff_tsum_comp_add
    have hb : (1 : ℝ) < 2 := one_lt_two
    have hf : IsBigO (cocompact ℝ) (sg ss 0) fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
      apply IsLittleO.isBigO
      have P : (-(1 : ℂ) / (2 * ss)).re < 0 := by
        simp [div_eq_mul_inv, h]

      have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-1 / (2 * ss)) P 0 (-2)
      simp only [zero_mul, add_zero] at X
      revert X
      conv =>
        enter [1, 2, x, 1]
        rw [mul_comm]
        rw [mul_div]
        rw [mul_neg]
        rw [mul_one]
      intro X
      unfold sg
      simp at X
      simp [X]

    exact (fun K => summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨_ , C⟩  (zero_lt_one.trans hb) hf K).comp_tendsto
    Int.tendsto_coe_cofinite))

  conv =>
    right
    intro n
    rw [← D]

  have T2 : Summable (fourierCoeff F) := by
    convert B
    apply D

  unfold Summable
  existsi (F (-μ))

  apply has_pointwise_sum_fourier_series_of_summable T2 (-↑μ)

theorem SGBound (ss μ : ℝ) (h : ss > 0) :
  (∑' (n : ℤ), sg' ss μ n) ≤ ∑' (n : ℤ), sg' ss 0 n := by

  have A : (∑' (n : ℤ), sg' ss μ n) = (∑' (n : ℤ), sg' ss 0 ((- μ) + n)) := by
    apply tsum_congr
    intro b
    simp [sg, sg']
    congr
    rw [neg_add_eq_sub]

  have B : (∑' (n : ℤ), sg' ss 0 (-μ + ↑n)) = |∑' (n : ℤ), sg' ss 0 (-μ + ↑n)| := by
    rw [_root_.abs_of_nonneg]
    apply tsum_nonneg
    intro i
    simp [sg', exp_nonneg]

  have C : |∑' (n : ℤ), sg' ss 0 (-μ + ↑n)| = Complex.abs (∑' (n : ℤ), sg' ss 0 (-μ + ↑n)) := by
    rw [← abs_ofReal]
    congr
    rw [ofReal_tsum]

  have D : Complex.abs (∑' (n : ℤ), sg' ss 0 (-μ + ↑n)) = Complex.abs (∑' (n : ℤ), sg ss 0 (-μ + ↑n)) := by
    congr

  have E : Complex.abs (∑' (n : ℤ), sg ss 0 (-μ + ↑n)) = Complex.abs (∑' (n : ℤ), 𝓕 (sg ss 0) n * (fourier n) (-μ : UnitAddCircle)) := by
    have X := SGPoi ss h (-μ)
    congr 1

  have F : (∑' (i : ℤ), Complex.abs (𝓕 (sg ss 0) i) * Complex.abs ((@fourier 1 i) (-μ))) = ∑' (i : ℤ), Complex.abs (𝓕 (sg ss 0) i) := by
    have X : ∀ i, ∀ x : AddCircle 1, ‖fourier i x‖ = 1 := fun i => fun x => abs_coe_circle _
    conv =>
      left
      right
      intro i
      right
      rw [← Complex.norm_eq_abs]
      rw [X i]
    simp

  have G : (∑' (i : ℤ), Complex.abs (𝓕 (sg ss 0) i)) = ∑' (i : ℤ), 𝓕 (sg ss 0) i := by
    rw [ofReal_tsum]
    congr
    ext a
    rw [CharFourierSG]
    unfold fourier_sg
    simp
    congr 1
    . simp
      have A : 0 ≤ (π⁻¹ * ss⁻¹ * (2 : ℝ)⁻¹) := by
        simp
        rw [mul_nonneg_iff]
        left
        simp
        constructor
        . rw [le_iff_lt_or_eq]
          left
          apply pi_pos
        . rw [le_iff_lt_or_eq]
          left
          simp [h]
      exact rpow_nonneg A 2⁻¹
    . rw [Complex.abs_exp]
      simp
      congr 1
      have X : ((π : ℂ) ^ 2).im = 0 := by
        refine abs_re_eq_abs.mp ?_
        simp
        rw [sq]
        simp
        rw [pow_two]
      rw [X]
      simp
      congr
      . rw [pow_two]
        simp
      . rw [pow_two]
        simp
    . exact h

  have H : (∑' (n : ℤ), 𝓕 (sg ss 0) n) = ∑' (n : ℤ), sg ss 0 n := by
    have X := SGPoi ss h 0
    revert X
    conv =>
      left
      right
      right
      intro n
      right
      rw [QuotientAddGroup.mk_zero]
      rw [fourier_eval_zero n]
    intro X
    simp at X
    simp [X]

  have I : (∑' (n : ℤ), sg ss 0 n) = ∑' (n : ℤ), sg' ss 0 n := by
    rw [ofReal_tsum]
    congr

  have J : Complex.abs (∑' (i : ℤ), 𝓕 (sg ss 0) i * (@fourier 1 i) (-μ)) ≤ ∑' (i : ℤ), Complex.abs (𝓕 (sg ss 0) i) * Complex.abs ((@fourier 1 i) (-μ)) := by
    rw [← Complex.norm_eq_abs]
    have S := SGFourierSummable ss μ h
    have Y := @norm_tsum_le_tsum_norm _ _ _ (fun (n : ℤ) => 𝓕 (sg ss 0) n * (@fourier 1 n) (-μ)) S
    simp only [smul_neg,  ofReal_one, div_one, Complex.norm_eq_abs, norm_mul] at Y
    trivial

  rw [A, B, C, D, E]
  rw [F] at J
  apply le_trans J
  refine real_le_real.mp ?_
  rw [G, H, I]
  simp only [real_le_real, le_refl]

theorem SG_1_periodic (ss μ : ℝ) (h : ss > 0) :
  (∑' (n : ℤ), sg ss μ n) = ∑' (n : ℤ), sg ss (μ + 1) n := by
  have A : ∀ n : ℤ, sg ss (μ + 1) n = sg ss μ (n - 1) := by
    intro n ; simp [sg]
    ring_nf
  conv => enter [2,1, n] ; rw [A]
  clear A
  sorry

--#check tsum_of_add_one_of_neg_add_one
