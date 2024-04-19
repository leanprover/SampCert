/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

noncomputable section

open Classical Complex Real Nat Filter Asymptotics FourierTransform
open Continuous

def gauss_term (σ μ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((-(x - μ)^2) / (2 * σ^2))

def fourier_gauss_term (σ : ℝ) (x : ℝ) : ℂ :=
  Complex.exp (- 2 * (π * σ * x)^2) / (((π * (σ:ℂ)^2 * (2 : ℂ))⁻¹) ^ (2 : ℂ)⁻¹)

def discrete_gaussian (σ μ : ℝ) (x : ℤ) : ℂ :=
  gauss_term σ μ x / ∑' x : ℤ, gauss_term σ μ x

theorem continuous_gauss_term (σ μ : ℝ) :
  Continuous (gauss_term σ μ) := by
  unfold gauss_term
  apply Continuous.cexp
  apply Continuous.div_const
  apply Continuous.neg
  apply Continuous.pow
  apply Continuous.sub
  . apply continuous_ofReal
  . apply continuous_const

theorem gauss_term_jacobi (σ μ : ℝ) :
  (fun n : ℤ => gauss_term σ μ n) = fun n : ℤ => (jacobiTheta₂_term n (μ * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹ * Complex.I⁻¹) (Complex.I * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹)) * Complex.exp (-μ ^ 2 / (2 * σ^2)) := by
  ext n
  simp [gauss_term, jacobiTheta₂_term]
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  simp [pi_ne_zero]
  ring_nf

theorem jacobi_tau_positive {σ : ℝ} (h : σ ≠ 0) :
  0 < (Complex.I * ((2 : ℂ) * σ^2)⁻¹ * π⁻¹).im := by
  simp [pi_pos, h, sq]

theorem summable_gauss_term {σ : ℝ} (μ : ℝ) (h : σ ≠ 0) :
  Summable fun n : ℤ => gauss_term σ μ n := by
  rw [gauss_term_jacobi]
  apply Summable.mul_right
  rw [summable_jacobiTheta₂_term_iff]
  apply jacobi_tau_positive h

theorem asymptotics_gauss_term {σ : ℝ} (μ : ℝ) (h : σ ≠ 0) :
  gauss_term σ 0 =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
  apply IsLittleO.isBigO
  unfold gauss_term
  simp only [ofReal_zero, sub_zero]
  have Y : ∀ x : ℂ, -1 / (2 * ↑σ ^ 2) * x ^ 2 = -x ^ 2 / (2 * σ ^ 2) := by
    intro x
    ring_nf
  conv =>
    left
    intro x
    rw [← Y]
  have P : (-(1 : ℂ) / (2 * σ^2)).re < 0 := sorry
  have X := @cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (-1 / (2 * σ^2)) P 0 (-2)
  simp only [zero_mul, add_zero] at X
  trivial

theorem gauss_term_shift (σ μ : ℝ) (n τ : ℤ) :
  gauss_term σ μ (n + τ) = gauss_term σ (μ - τ) n := by
  simp [gauss_term]
  congr 4
  ring_nf

theorem fourier_gauss_term_correspondance {σ : ℝ} (h : σ ≠ 0) :
  (𝓕 (gauss_term σ 0)) = fourier_gauss_term σ := by
  have P : 0 < (π * (2 : ℂ) * σ^2)⁻¹.re  := sorry
  have X := @fourierIntegral_gaussian_pi' (π * 2 * σ^2)⁻¹ P 0
  have A : gauss_term σ 0 = fun x : ℝ => cexp (-π * (π * (2 : ℂ) * σ ^ 2)⁻¹ * x ^ 2 + 2 * π * 0 * x) := by
    ext x
    simp [gauss_term]
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

theorem asymptotics_fourier_gauss_term :
  (𝓕 (gauss_term σ 0)) =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
  sorry

theorem poisson_gauss_term {σ : ℝ} (h : σ ≠ 0) (x : ℝ) :
  (∑' (n : ℤ), gauss_term σ 0 (x + n)) = ∑' (n : ℤ), 𝓕 (gauss_term σ 0) n * (@fourier 1 n) (x : UnitAddCircle) := by
  sorry

theorem summable_fourier_gauss_term (ss μ : ℝ) (h : ss > 0):
  Summable fun (n : ℤ) => 𝓕 (gauss_term σ 0) n * (@fourier 1 n) (-μ) := by
  sorry

theorem sum_gauss_term_1_periodic {σ : ℝ} (μ : ℝ) (h : σ ≠ 0) :
  (∑' (n : ℤ), gauss_term σ μ n) = ∑' (n : ℤ), gauss_term σ (μ + 1) n := by
  sorry
