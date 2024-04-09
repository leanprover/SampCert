import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Defs.Filter

noncomputable section

open Classical Nat BigOperators Real
open FourierTransform GaussianFourier Filter Asymptotics Complex

def sg (ss μ : ℝ) : ℝ → ℂ := fun x : ℝ => rexp (- ((x - μ)^2) / (2 * ss))

theorem SGPoi (ss : ℝ) (h : ss > 0) (x : ℝ) :
  (∑' (n : ℤ), sg ss 0 (x + n)) = ∑' (n : ℤ), 𝓕 (sg ss 0) n * (@fourier 1 n) (x : UnitAddCircle) := by

  let g : ℝ → ℂ := fun x ↦ Complex.exp (- (x^2) / (2 * ss))

  have A : Continuous g := by
    apply Complex.continuous_exp.comp
    apply Continuous.div_const
    apply Continuous.neg
    apply Continuous.pow
    exact Complex.continuous_ofReal

  have B : 𝓕 g = fun x : ℝ ↦ (((π)⁻¹ * (↑ss)⁻¹ * (2 : ℂ)⁻¹) ^ (2 : ℂ)⁻¹)⁻¹ * Complex.exp ( - 2 * π^2 * ss * x^2) := by
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

def sg' (ss μ : ℝ) : ℝ → ℝ := fun x : ℝ => rexp (- ((x - μ)^2) / (2 * ss))

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
  rw [A, B, C, D, E]
  clear A B C D E

  have CRUX : Complex.abs (∑' (i : ℤ), 𝓕 (sg ss 0) i * (@fourier 1 i) (-μ)) ≤ ∑' (i : ℤ), Complex.abs (𝓕 (sg ss 0) i) * Complex.abs ((@fourier 1 i) (-μ)) := by
    rw [← Complex.norm_eq_abs]
    have X : Summable fun (n : ℤ) => ‖𝓕 (sg ss 0) n * (@fourier 1 n) (-μ)‖ := sorry
    have Y := @norm_tsum_le_tsum_norm _ _ _ (fun (n : ℤ) => 𝓕 (sg ss 0) n * (@fourier 1 n) (-μ)) X
    simp only [smul_neg,  ofReal_one, div_one, Complex.norm_eq_abs, norm_mul] at Y
    trivial

  have A' : (∑' (n : ℤ), sg' ss 0 ↑n) = ∑' (n : ℤ), sg ss 0 ↑n := by
    rw [ofReal_tsum]
    congr
  have B' : (∑' (n : ℤ), sg ss 0 ↑n) = ∑' (n : ℤ), 𝓕 (sg ss 0) ↑n := by
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
    trivial






  sorry
