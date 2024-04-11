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

  have X := @fourier_transform_gaussian_pi' (π * 2 * ss)⁻¹ P 0
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
      have B : ((2 : ℂ)⁻¹).im = 0 := by
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

    have X := @fourier_transform_gaussian_pi' (π * 2 * ss)⁻¹ P 0
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
