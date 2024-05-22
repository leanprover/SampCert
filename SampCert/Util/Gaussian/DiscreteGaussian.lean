/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

noncomputable section

open Classical Complex Real Nat Filter Asymptotics FourierTransform
open Continuous

attribute [local instance] Real.fact_zero_lt_one

def gauss_term_ℝ (σ μ : ℝ) (x : ℝ) : ℝ :=
  Real.exp ((-(x - μ)^2) / (2 * σ^2))

instance gauss_term_ℂ (σ μ : ℝ) : C(ℝ,ℂ) where
  toFun := fun x : ℝ => ((gauss_term_ℝ σ μ x) : ℂ)
  continuous_toFun := by
    unfold gauss_term_ℝ
    simp
    apply Continuous.cexp
    apply Continuous.div_const
    apply Continuous.neg
    apply Continuous.pow
    apply Continuous.sub
    . apply continuous_ofReal
    . apply continuous_const

theorem gauss_term_swap (σ μ : ℝ) (n : ℝ) :
  (gauss_term_ℂ σ μ n) = gauss_term_ℝ σ μ n := by
  simp [gauss_term_ℂ, gauss_term_ℝ]

-- def fourier_gauss_term (σ : ℝ) (x : ℝ) : ℂ :=
--  Real.exp (- 2 * (π * σ * x)^2) / ((((π * (σ:ℝ)^2 * (2 : ℝ))⁻¹) ^ (2 : ℝ)⁻¹) : ℝ)

def fourier_gauss_term (σ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (- 2 * (π * σ * x)^2) / (((π * (σ:ℂ)^2 * (2 : ℂ))⁻¹) ^ (2 : ℂ)⁻¹)

def discrete_gaussian (σ μ : ℝ) (x : ℝ) : ℝ :=
  gauss_term_ℝ σ μ x / ∑' x : ℤ, gauss_term_ℝ σ μ x

def NotSureYet (σ : ℝ) : C(UnitAddCircle, ℂ) :=
    ⟨((gauss_term_ℂ σ 0).periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩

theorem gauss_term_jacobi (σ μ : ℝ) :
  (fun n : ℤ => gauss_term_ℂ σ μ n) = fun n : ℤ => (jacobiTheta₂_term n (μ * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹ * Complex.I⁻¹) (Complex.I * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹)) * Complex.exp (-μ ^ 2 / (2 * σ^2)) := by
  ext n
  simp [gauss_term_ℂ, gauss_term_ℝ, jacobiTheta₂_term]
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  simp [pi_ne_zero]
  ring_nf

theorem jacobi_tau_positive {σ : ℝ} (h : σ ≠ 0) :
  0 < (Complex.I * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹).im := by
  simp [pi_pos, h, sq]

theorem summable_gauss_term {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun n : ℤ => gauss_term_ℂ σ μ n := by
  rw [gauss_term_jacobi]
  apply Summable.mul_right
  rw [summable_jacobiTheta₂_term_iff]
  apply jacobi_tau_positive h

theorem summable_gauss_term' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun n : ℤ => gauss_term_ℝ σ μ n := by
  rw [← Complex.summable_ofReal]
  conv =>
    right
    intro n
    rw [← gauss_term_swap]
  apply summable_gauss_term h

theorem asymptotics_gauss_term {σ : ℝ} (h : σ ≠ 0) :
  gauss_term_ℂ σ 0 =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
  apply IsLittleO.isBigO
  unfold gauss_term_ℂ gauss_term_ℝ
  simp only [ContinuousMap.coe_mk, ofReal_zero, sub_zero]
  have Y : ∀ x : ℝ, -1 / (2 * σ ^ 2) * x ^ 2 = -x ^ 2 / (2 * σ ^ 2) := by
    intro x
    ring_nf
  conv =>
    left
    intro x
    rw [Complex.ofReal_exp]
    rw [← Y]
  have P : (-(1 : ℂ) / (2 * σ^2)).re < 0 := by
    simp [div_eq_mul_inv, sq, h]
  have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-1 / (2 * σ^2)) P 0 (-2)
  simp only [zero_mul, add_zero] at X
  simp only [ofReal_mul, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat,
    ofReal_pow]
  trivial

theorem gauss_term_shift (σ μ : ℝ) (n τ : ℤ) :
  gauss_term_ℂ σ μ (n + τ) = gauss_term_ℂ σ (μ - τ) n := by
  simp [gauss_term_ℂ, gauss_term_ℝ]
  congr 4
  ring_nf

theorem fourier_gauss_term_correspondance {σ : ℝ} (h : σ ≠ 0) :
  (𝓕 (gauss_term_ℂ σ 0)) = fourier_gauss_term σ := by
  have P : 0 < (π * (2 : ℂ) * σ^2)⁻¹.re  := by
    simp [sq, h, pi_pos]
  have X := @fourierIntegral_gaussian_pi' (π * 2 * σ^2)⁻¹ P 0
  have A : gauss_term_ℂ σ 0 = fun x : ℝ => cexp (-π * (π * (2 : ℂ) * σ ^ 2)⁻¹ * x ^ 2 + 2 * π * 0 * x) := by
    ext x
    simp [gauss_term_ℂ, gauss_term_ℝ]
    congr 1
    ring_nf
    simp [pi_ne_zero]
  rw [A]
  rw [X]
  unfold fourier_gauss_term
  ext x
  ring_nf
  simp
  ring_nf
  simp

theorem asymptotics_fourier_gauss_term {σ : ℝ} (h : σ ≠ 0) :
  (𝓕 (gauss_term_ℂ σ 0)) =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
  rw [fourier_gauss_term_correspondance h]
  apply IsLittleO.isBigO
  unfold fourier_gauss_term
  conv =>
    left
    intro x
    rw [division_def]
    rw [mul_comm]
  apply IsLittleO.const_mul_left
  have P : (-(2 : ℂ) * π ^ 2 * σ^2).re < 0 := by
    simp [h, pow_two, pi_ne_zero]

  have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-2 * π ^ 2 * σ^2) P 0 (-2)
  simp only [zero_mul, add_zero] at X
  have Y : ∀ x : ℝ, -2 * π ^ 2 * σ ^ 2 * x ^ 2 = (-(2 : ℂ) * (π * σ * x) ^ 2) := by
    intro x
    simp
    ring_nf
  conv =>
    left
    intro x
    rw [← Y]
  trivial

theorem poisson_gauss_term {σ : ℝ} (h : σ ≠ 0) (x : ℝ) :
  (∑' n : ℤ, gauss_term_ℂ σ 0 (x + n)) = ∑' (n : ℤ), (𝓕 (gauss_term_ℂ σ 0)) n * (@fourier 1 n) x := by
  have B := asymptotics_gauss_term h
  have C := asymptotics_fourier_gauss_term h
  have D : (1 : ℝ) < 2 := one_lt_two
  have X := @Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay (gauss_term_ℂ σ 0) ((gauss_term_ℂ σ 0).continuous_toFun) 2 D B C x
  rw [← X]

theorem summable_fourier_gauss_term {σ : ℝ} (h : σ ≠ 0) :
  Summable fun n : ℤ => 𝓕 (gauss_term_ℂ σ 0) n := by
  have A := Real.summable_abs_int_rpow one_lt_two
  have B := @IsBigO.comp_tendsto ℝ ℤ ℂ ℝ _ _ (𝓕 (gauss_term_ℂ σ 0)) (fun (x : ℝ) => ((|x| ^ (-2 : ℝ)) : ℝ)) (cocompact ℝ) (asymptotics_fourier_gauss_term h) Int.cast cofinite Int.tendsto_coe_cofinite
  have C := @summable_of_isBigO ℤ ℂ _ _ (fun z : ℤ => 𝓕 (gauss_term_ℂ σ 0) z) (fun x : ℤ => |(x : ℝ)| ^ (-2 : ℝ)) A B
  exact C

theorem fourier_coeff_correspondance {σ : ℝ} (h : σ ≠ 0) (n : ℤ) :
  fourierCoeff (NotSureYet σ) n = 𝓕 (gauss_term_ℂ σ 0) n := by
  apply Real.fourierCoeff_tsum_comp_add
  apply (fun K => summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
  ((isBigO_norm_restrict_cocompact ⟨_ , ((gauss_term_ℂ σ 0).continuous_toFun)⟩  (zero_lt_one.trans one_lt_two) (asymptotics_gauss_term h) K).comp_tendsto
  Int.tendsto_coe_cofinite))

theorem summable_fourier_gauss_term' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℤ) => 𝓕 (gauss_term_ℂ σ 0) n * (@fourier 1 n) (-μ) := by
  have A : Summable fun n : ℤ => fourierCoeff (NotSureYet σ) n := by
    conv =>
      right
      intro n
      rw [fourier_coeff_correspondance h]
    apply summable_fourier_gauss_term h
  have B := has_pointwise_sum_fourier_series_of_summable A (- μ)
  existsi ((NotSureYet σ) (-μ))
  conv =>
    left
    intro n
    rw [← fourier_coeff_correspondance h]
  exact B

theorem gauss_term_pos (σ μ : ℝ) (n : ℤ) :
  0 < (gauss_term_ℝ σ μ) n := by
  unfold gauss_term_ℝ
  apply exp_pos

theorem gauss_term_noneg (σ μ : ℝ) (n : ℤ) :
  0 ≤ (gauss_term_ℝ σ μ) n := by
  unfold gauss_term_ℝ
  apply le_of_lt (gauss_term_pos σ μ n)

theorem sum_gauss_term_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  0 < (∑' (x : ℤ), (gauss_term_ℝ σ μ) x) := by
  apply tsum_pos (summable_gauss_term' h μ) _ 0
  . apply gauss_term_pos
  . intro i
    apply gauss_term_noneg

theorem sum_gauss_term_nonneg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x) := by
  apply le_of_lt (sum_gauss_term_pos h μ)

theorem sum_gauss_term_ne_zero {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  ∑' (n : ℤ), gauss_term_ℝ σ μ n ≠ 0 := by
  apply Ne.symm (_root_.ne_of_lt (sum_gauss_term_pos h μ))

theorem discrete_gaussian_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (n : ℤ) :
  0 < discrete_gaussian σ μ n := by
  unfold discrete_gaussian
  rw [div_pos_iff]
  left
  constructor
  . apply gauss_term_pos
  . apply sum_gauss_term_pos h μ

theorem discrete_gaussian_nonneg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (n : ℤ) :
  0 ≤ discrete_gaussian σ μ n := by
  apply le_of_lt (discrete_gaussian_pos h μ n)

theorem discrete_gaussian_summable {σ : ℝ} (h : σ ≠ 0) :
  Summable fun (n : ℤ) => discrete_gaussian σ 0 n := by
  unfold discrete_gaussian
  apply Summable.div_const
  apply summable_gauss_term' h

theorem discrete_gaussian_summable' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  Summable fun (n : ℤ) => discrete_gaussian σ μ n := by
  unfold discrete_gaussian
  apply Summable.div_const
  apply summable_gauss_term' h

theorem discrete_gaussian_normalizes {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  (∑' n : ℤ, discrete_gaussian σ μ n) = 1 := by
  unfold discrete_gaussian
  rw [tsum_div_const]
  rw [div_eq_one_iff_eq]
  apply sum_gauss_term_ne_zero h
