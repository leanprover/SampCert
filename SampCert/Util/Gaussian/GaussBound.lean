/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Gaussian.DiscreteGaussian

/-!
# Gauss Bound

This file contains a proof that the sum of Gaussian terms with any mean (over the integers)
is bounded above by the sum of mean-zero Gaussian terms.

The argument transforms the series into a Fourier series, and eliminates the Fourier basis functions by
bounding them above by their absolute value. This has the effect of shifting the mean to zero; since
the sum of Fourier coefficients equals the sum of mean-zero Gaussian terms. The Poisson summation formula
justifies the transformation between series of ``gauss_term_ℝ ...`` and ``𝓕 (gauss_term_ℂ ...)``.
-/

noncomputable section

open Classical Nat BigOperators Real
open FourierTransform GaussianFourier Filter Asymptotics Complex
open ContinuousMap Function


/-
This is copied from MathLib; it was made private in the release of 4.10 with the suggestion that it would be
auto-generated in 4.11. It wasn't clear if it would become public again at that point.

See: https://github.com/leanprover-community/mathlib4/pull/15340
-/
theorem local_ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => Complex.ext h.1 h.2⟩

/--
The sum of any gaussian function over ℤ is bounded above by the sum of the mean-zero gaussian function over ℤ.
-/
theorem sum_gauss_term_bound {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  (∑' (n : ℤ), ((gauss_term_ℝ σ μ) n)) ≤ ∑' (n : ℤ), ((gauss_term_ℝ σ 0) n) := by
  have A : (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = (∑' (n : ℤ), (gauss_term_ℝ σ 0) ((- μ) + n)) := by
    apply tsum_congr
    intro b
    simp [gauss_term_ℝ]
    congr
    rw [neg_add_eq_sub]

  have B : (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)) = |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)| := by
    rw [_root_.abs_of_nonneg]
    apply tsum_nonneg
    intro i
    simp [gauss_term_ℝ, exp_nonneg]

  have C : |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n)| = ‖((∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]

  have D : ‖((∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + ↑n) : ℝ) : ℂ)‖ = ‖(∑' (n : ℤ), ((gauss_term_ℝ σ 0) (-μ + ↑n) : ℂ))‖ := by
    rw [ofReal_tsum]

  have E : ‖(∑' (n : ℤ), ((gauss_term_ℝ σ 0) (-μ + ↑n) : ℂ))‖ = ‖(∑' (n : ℤ), 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) n * (fourier n) (-μ : UnitAddCircle))‖ := by
    have X := poisson_gauss_term h (-μ)
    have eq1 : (∑' (n : ℤ), ((gauss_term_ℝ σ 0) (-μ + ↑n) : ℂ)) = ∑' (n : ℤ), (gauss_term_ℂ σ 0) (-μ + ↑n) := by
      apply tsum_congr; intro b; simp [gauss_term_ℂ, gauss_term_ℝ]
    rw [eq1, X]
    push_cast
    rfl

  have F : (∑' (i : ℤ), ‖𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i‖ * ‖((@fourier 1 i) (-μ))‖) = ∑' (i : ℤ), ‖𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i‖ := by
    have X : ∀ i, ∀ x : AddCircle 1, ‖fourier i x‖ = 1 := fun _ => fun _ => Circle.norm_coe _
    conv =>
      left
      arg 1
      intro i
      right
      rw [X i]
    simp

  have G : (∑' (i : ℤ), (‖𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i‖ : ℂ)) = ∑' (i : ℤ), 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i := by
    apply tsum_congr
    intro a
    rw [fourier_gauss_term_correspondance h]
    unfold fourier_gauss_term
    simp [sq]
    congr 1
    · rw [Complex.norm_exp]
      simp [sq]
    · have A : 0 ≤ (2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹ := by
        apply rpow_nonneg
        rw [mul_nonneg_iff]
        left
        simp [pi_pos]
        rw [← pow_two]
        rw [inv_pow]
        rw [inv_nonneg]
        exact sq_nonneg σ
      have H : ‖(((2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹ : ℝ) : ℂ)‖ = (2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg A]
      have X : Complex.ofReal ((2⁻¹ * ((↑σ)⁻¹ * (↑σ)⁻¹ * (↑π)⁻¹)) ^ (2 : ℝ)⁻¹) = (2⁻¹ * ((σ : ℂ)⁻¹ * (σ : ℂ)⁻¹ * (π : ℂ)⁻¹)) ^ (2 : ℂ)⁻¹ := by
        rw [← ofReal_ofNat]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_inv]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        rw [local_ext_iff]
        constructor
        · rw [rpow_def]
          simp
        · simp
          rw [cpow_inv_two_im_eq_sqrt]
          · simp
            ring_nf
            simp
            rw [← Real.sqrt_zero]
            congr 1
            have P1 : |π| = π := by
              rw [_root_.abs_of_nonneg]
              rw [le_iff_lt_or_eq]
              left
              apply pi_pos
            rw [P1]
            rw [← mul_add]
            simp
            right
            ring_nf
          · simp
      rw [← X]
      rw [H]

  have H : (∑' (n : ℤ), 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) n) = ∑' (n : ℤ), (gauss_term_ℂ σ 0) n := by
    have X := poisson_gauss_term h 0
    have X' : (∑' (n : ℤ), (gauss_term_ℂ σ 0) (↑n : ℝ)) =
        ∑' (n : ℤ), 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) n := by
      have Y := X
      simp only [zero_add] at Y
      rw [Y]
      apply tsum_congr
      intro n
      rw [show ((0 : ℝ) : UnitAddCircle) = 0 from by push_cast; rfl]
      simp [fourier_eval_zero n]
    exact X'.symm

  have I : (∑' (n : ℤ), ((gauss_term_ℂ σ 0) n : ℂ)) = ((∑' (n : ℤ), (gauss_term_ℝ σ 0) n : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    apply tsum_congr
    intro b
    simp [gauss_term_ℂ, gauss_term_ℝ]

  have J : ‖(∑' (i : ℤ), 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i * (@fourier 1 i) (-μ))‖ ≤ ∑' (i : ℤ), ‖𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i‖ * ‖((@fourier 1 i) (-μ))‖ := by
    have S := summable_fourier_gauss_term' h μ
    rw [← summable_norm_iff] at S
    have Y := @norm_tsum_le_tsum_norm _ _ _ (fun (n : ℤ) => 𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) n * (@fourier 1 n) (-μ)) S
    simp only [smul_neg, ofReal_one, div_one, norm_mul] at Y
    apply Y

  rw [A, B, C, D, E]
  rw [F] at J
  apply le_trans J
  have step : ((∑' (i : ℤ), ‖𝓕 ((gauss_term_ℂ σ 0 : ℝ → ℂ)) i‖ : ℝ) : ℂ) = ((∑' (n : ℤ), (gauss_term_ℝ σ 0) n : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    rw [G, H, I]
  exact_mod_cast (Complex.ofReal_inj.mp step).le
