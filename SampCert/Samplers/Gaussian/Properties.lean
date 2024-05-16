/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import SampCert.Samplers.Laplace.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import SampCert.Util.UtilMathlib
import SampCert.Samplers.Gaussian.Code
import SampCert.Util.Gaussian.DiscreteGaussian

noncomputable section

open Classical PMF Nat Real

namespace SLang

theorem ite_simpl_gaussian_1 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) false
  else 0) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      subst h2
      contradiction
    . simp

theorem ite_simpl_gaussian_2 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) true
  else 0) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      subst h2
      contradiction
    . simp

@[simp]
theorem DiscreteGaussianSampleLoop_normalizes (num den t : ℕ+) :
  ∑' x, (DiscreteGaussianSampleLoop num den t) x = 1 := by
  simp only [DiscreteGaussianSampleLoop, Bind.bind, Int.natCast_natAbs, Pure.pure, SLang.bind_apply,
    SLang.pure_apply, tsum_bool, ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
    and_true, and_false, ↓reduceIte, add_zero, zero_add]
  conv =>
    left
    right
    intro a
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      right
      intro x
      rw [ite_simpl_gaussian_1]
    . rw [ENNReal.tsum_eq_add_tsum_ite a]
      right
      right
      intro x
      rw [ite_simpl_gaussian_2]
  simp only [↓reduceIte, tsum_zero, add_zero]
  conv =>
    left
    right
    intro a
    rw [← mul_add]
    rw [← tsum_bool]
    rw [BernoulliExpNegSample_normalizes]
  simp only [mul_one]
  rw [DiscreteLaplaceSample_normalizes]

@[simp]
theorem ite_simpl_1' (num den t : PNat) (x : ℤ) (n : ℤ) :
  (@ite ENNReal (x = n) (propDecidable (x = n)) 0
  (@ite ENNReal (n = x) (Int.instDecidableEqInt n x)
  (ENNReal.ofReal ((rexp (↑↑t)⁻¹ - 1) / (rexp (↑↑t)⁻¹ + 1) * rexp (-(|↑x| / ↑↑t))) *
    ENNReal.ofReal (rexp (-(↑(Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num)) ^ 2 / ((2 : ℕ+) * ↑↑num * ↑↑t ^ 2 * ↑↑den)))))
  0)) = 0 := by
  split
  . simp
  . rename_i h
    simp [h]
    intro h
    subst h
    contradiction

@[simp]
theorem DiscreteGaussianSampleLoop_apply_true (num den t : ℕ+) (n : ℤ) :
  (DiscreteGaussianSampleLoop num den t) (n, true)
    = ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1)) * ENNReal.ofReal (rexp (-(Int.natAbs n / t)) *
    rexp (-((Int.natAbs (Int.sub (|n| * t * den) ↑↑num)) ^ 2 / ((2 : ℕ+) * num * ↑↑t ^ 2 * den)))) := by
  simp only [DiscreteGaussianSampleLoop, Bind.bind, Int.natCast_natAbs, Pure.pure, SLang.bind_apply,
    DiscreteLaplaceSample_apply, NNReal.coe_nat_cast, PNat.one_coe, cast_one, NNReal.coe_one,
    div_one, one_div, Int.cast_abs, SLang.pure_apply, Prod.mk.injEq, mul_ite,
    mul_one, mul_zero, tsum_bool, and_false, ↓reduceIte, and_true, BernoulliExpNegSample_apply_true,
    cast_pow, NNReal.coe_pow, PNat.mul_coe, PNat.pow_coe, cast_mul, NNReal.coe_mul, zero_add]
  rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
  simp (config := { contextual := true }) only [↓reduceIte, ite_simpl_1', tsum_zero, add_zero]
  rw [ENNReal.ofReal_mul]
  have A : 0 ≤ rexp (-(|↑n| / ↑↑t)) := by apply exp_nonneg
  . conv =>
      left
      rw [mul_assoc]
      right
      rw [← ENNReal.ofReal_mul A]
    congr
    rw [cast_natAbs]
    simp only [Int.cast_abs]
  . rw [div_nonneg_iff] -- always the same
    left
    simp only [sub_nonneg, one_le_exp_iff, inv_nonneg, cast_nonneg, true_and]
    apply Right.add_nonneg
    . apply exp_nonneg
    . simp only [zero_le_one]

theorem if_simpl_2' (x_1 x : ℤ) (a : ENNReal) :
  @ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (a * (@ite ENNReal (x = x_1) (propDecidable (x = (x_1, true).1))) 1 0) = 0 := by
  split
  . simp
  . split
    . rename_i h1 h2
      subst h2
      contradiction
    . simp

theorem alg_auto (num den : ℕ+) (x : ℤ) :
  ENNReal.ofReal (
  rexp (-((Int.natAbs x) / ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1))) *
    rexp (-((Int.natAbs (Int.sub (|x| * (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den + 1) * den ^ 2) (num ^ 2))) ^ 2 /
          ((2 : ℕ+) * num ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2 * den ^ 2))))
  = ENNReal.ofReal (rexp (-((num ^ 2) / (2 * den ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2)))) *
      ENNReal.ofReal (rexp (- ((x ^ 2 * den ^ 2) /(2 * num ^ 2)))) := by
  let τ := (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ)
  have Tau : (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) = τ := rfl
  rw [Tau]

  have Tau_ne0 : τ ≠ 0 := by
    rw [ne_iff_lt_or_gt]
    right
    apply cast_add_one_pos

  rw [← ENNReal.ofReal_mul]
  . congr 1
    simp [← exp_add]
    simp [division_def]
    rw [(neg_add _ _).symm]
    rw [(neg_add _ _).symm]
    congr 1
    have A : ∀ x : ℤ, (Int.natAbs x)^2 = (x : ℝ)^2 := by
      intro x
      rw [cast_natAbs]
      rw [sq_eq_sq_iff_abs_eq_abs]
      simp
    rw [A]
    clear A
    have A : ∀ x y : ℤ, ((Int.sub x y) : ℝ) = (x : ℝ) - (y : ℝ) := by
      intro x y
      rw [← @Int.cast_sub]
      rfl
    rw [A]
    clear A

    rw [pow_two]
    rw [sub_mul]
    rw [mul_sub]
    rw [mul_sub]
    rw [sub_mul]
    rw [sub_mul]
    rw [sub_mul]
    simp

    have X : (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den) + (1 : ℝ) = (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) := by
      rfl
    rw [X]
    clear X

    have X : ((Int.natAbs x) : ℝ) = Complex.abs (x : ℂ) := by
      rw [cast_natAbs]
      simp
    rw [X]
    clear X
    rw [Tau]

    let α := (num : ℝ) ^ 2
    have Alpha : ((num : ℕ+) : ℝ) ^ 2 = α := rfl
    rw [Alpha]

    let β := (den : ℝ) ^ 2
    have Beta : ((den : ℕ+) : ℝ) ^ 2  = β := rfl
    rw [Beta]

    let y := Complex.abs (x : ℂ)
    have Y : Complex.abs (x : ℂ)  = y := rfl
    rw [← Complex.abs_ofReal]
    have Cast : ∀ x : ℤ, @Int.cast ℂ Ring.toIntCast x = Complex.ofReal' (@Int.cast ℝ Ring.toIntCast x) := by
      simp
    rw [← Cast]
    rw [Y]

    have A : y * τ * β * α * (β⁻¹ * ((τ ^ 2)⁻¹ * (α⁻¹ * ((2: ℝ))⁻¹)))
      = y * ((2: ℕ+): ℝ)⁻¹ * τ⁻¹ := by
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      conv =>
        right
        rw [mul_assoc]
      congr 1
      simp [← mul_assoc]
      conv =>
        right
        rw [mul_comm]
      congr 1
      conv =>
        left
        left
        left
        rw [mul_assoc]
        rw [mul_assoc]
        right
        rw [mul_comm]
        rw [mul_assoc]
        right
        simp
      rw [mul_one]
      conv =>
        left
        rw [mul_assoc]
        rw [mul_assoc]
        right
        rw [mul_comm]
        rw [mul_assoc]
        simp
      rw [pow_two]
      rw [mul_inv]
      rw [← mul_assoc]
      rw [mul_inv_cancel Tau_ne0]
      simp

    rw [A]
    clear A

    have B : α * (y * τ * β) * (β⁻¹ * ((τ ^ 2)⁻¹ * (α⁻¹ * ((2: ℝ))⁻¹)))
      = y * ((2: ℕ+): ℝ)⁻¹ * τ⁻¹ := by
      rw [mul_rotate]
      rw [mul_assoc]
      conv =>
        left
        right
        rw [mul_assoc]
        right
        rw [mul_assoc]
        right
        rw [mul_comm]
        rw [← mul_assoc]
        simp
      rw [mul_assoc]
      conv =>
        left
        right
        rw [← mul_assoc]
        simp
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      rw [← mul_assoc]
      conv =>
        right
        rw [mul_comm]
      congr 1
      rw [pow_two]
      rw [mul_inv]
      rw [← mul_assoc]
      rw [mul_inv_cancel Tau_ne0]
      simp

    rw [B]
    clear B

    have C : (y * τ * β * (y * τ * β) * (β⁻¹ * ((τ ^ 2)⁻¹ * (α⁻¹ * ((2: ℝ))⁻¹))))
      = y ^ 2 * β * α⁻¹ * (((2: ℕ+): ℝ))⁻¹ := by
      rw [pow_two]
      rw [pow_two]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      rw [mul_comm]
      conv =>
        right
        rw [mul_comm]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      rw [mul_comm]
      congr 1
      conv =>
        left
        right
        right
        right
        right
        rw [← mul_assoc]
        rw [mul_comm]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      congr 1
      rw [mul_inv]
      rw [← mul_assoc]
      conv =>
        left
        left
        rw [mul_assoc]
        right
        rw [mul_comm]
        rw [(mul_inv_cancel Tau_ne0)]
      rw [mul_one]
      conv =>
        left
        left
        left
        rw [mul_assoc]
        right
        simp
      rw [mul_one]
      rw [(mul_inv_cancel Tau_ne0)]
      simp

    rw [C]
    clear C

    have D : α * α * (β⁻¹ * ((τ ^ 2)⁻¹ * (α⁻¹ * ((2: ℝ))⁻¹)))
      = α * β⁻¹ * (τ ^ 2)⁻¹ * (((2: ℕ+): ℝ))⁻¹ := by
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      rw [← mul_assoc]
      congr 1
      rw [mul_assoc]
      rw [mul_assoc]
      rw [mul_comm]
      rw [← mul_assoc]
      rw [mul_assoc]
      simp

    rw [D]
    clear D

    rw [(sub_add (_ - _) _ _).symm]
    rw [sub_eq_neg_add]
    rw [sub_eq_neg_add]
    rw [← add_assoc]
    rw [← add_assoc]
    rw [← add_assoc]

    have E : y * τ⁻¹ + -(y * (((2: ℕ+): ℝ))⁻¹ * τ⁻¹) + -(y * (((2: ℕ+): ℝ))⁻¹ * τ⁻¹) = 0 := by
      rw [add_assoc]
      rw [(neg_add _ _).symm]
      conv =>
        left
        right
        right
        congr
        . rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          right
          rw [mul_comm]
        . rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          right
          rw [mul_comm]
      rw [(add_mul _ _ _).symm]
      have X : (1/(2: ℕ+)) + (1/(2 : ℕ+)) = (1 : ℝ) := by
        simp
        rw [← two_mul]
        exact mul_inv_cancel_of_invertible 2
      conv =>
        left
        right
        right
        left
        rw [inv_eq_one_div]
      rw [X]
      rw [one_mul]
      simp

    rw [E]
    rw [zero_add]

    rw [add_comm]
    congr 1
    . rw [← mul_assoc]
      rw [← mul_assoc]
      congr 1
      rw [mul_comm]
      rw [← mul_assoc]
      congr 1
      rw [mul_comm]
    . rw [← mul_assoc]
      congr 3
      rw [← Y]
      simp

  . simp [exp_nonneg]


theorem alg_auto' (num den : ℕ+) (x : ℤ) :
  -((x : ℝ) ^ 2 * (den : ℝ) ^ 2 / ((2 : ℝ) * (num : ℝ) ^ 2)) = -(x : ℝ) ^ 2 / ((2 : ℝ) * ((num : ℝ) ^ 2 / (den : ℝ) ^ 2)) := by
  ring_nf ; simp ; ring_nf

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

@[simp]
theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (x : ℤ) :
  (DiscreteGaussianSample num den) x =
  ENNReal.ofReal (discrete_gaussian ((num : ℝ) / (den : ℝ)) 0 x) := by
  unfold discrete_gaussian
  unfold gauss_term_ℝ
  simp
  simp only [DiscreteGaussianSample, Bind.bind, Pure.pure, SLang.bind_apply]
  have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) { val := ↑num / ↑den + 1, property := (Add1 (↑num / ↑den)  : 0 < ↑num / ↑den + 1) }

  conv =>
    left
    right
    intro a
    left
    rw [prob_until_apply_norm _ _ _ A]
  clear A

  simp only [ENNReal.tsum_prod', tsum_bool, ↓reduceIte, DiscreteGaussianSampleLoop_apply_true,
    PNat.mk_coe, cast_add, cast_one, Int.ofNat_ediv, PNat.pow_coe, cast_pow, zero_add, ite_mul,
    zero_mul, SLang.pure_apply, NNReal.coe_nat_cast, div_pow]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  conv =>
    left
    right
    right
    intro x_1
    rw [if_simpl_2']
  simp only [↓reduceIte, mul_one, tsum_zero, add_zero]

  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.mul_inv]
  . rw [mul_assoc]
    conv =>
      left
      right
      rw [mul_comm]
      rw [mul_assoc]
    rw [← mul_assoc]
    rw [ENNReal.mul_inv_cancel]
    . simp only [one_mul]
      rw [mul_comm]
      rw [← division_def]
      rw [ENNReal.ofReal_div_of_pos]
      . simp only [alg_auto]
        rw [ENNReal.tsum_mul_left]
        rw [ENNReal.div_eq_inv_mul]
        rw [← mul_assoc]
        rw [ENNReal.mul_inv]
        have A : ENNReal.ofReal (rexp (-(↑↑num ^ 2 / (2 * ↑↑den ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2)))) ≠ 0 := by
          refine zero_lt_iff.mp ?ha.h.a
          simp only [ENNReal.ofReal_pos]
          simp only [exp_pos]
        have B  : ENNReal.ofReal (rexp (-(↑↑num ^ 2 / (2 * ↑↑den ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv ↑num ↑den) + 1) ^ 2)))) ≠ ⊤ := by
          exact ENNReal.ofReal_ne_top
        . conv =>
            left
            left
            rw [mul_comm]
            rw [← mul_assoc]
            rw [ENNReal.mul_inv_cancel A B]
          clear A B
          simp only [one_mul]
          rw [mul_comm]
          rw [← division_def]
          congr
          . simp only [alg_auto']
          . conv =>
              left
              right
              intro i
              rw [alg_auto']
            rw [← ENNReal.ofReal_tsum_of_nonneg]
            . intro n
              simp only [exp_nonneg]
            . have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
                simp
              have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
              unfold gauss_term_ℝ at Y
              simp at Y
              exact Y
        . left
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          simp only [exp_pos]
        . left
          exact ENNReal.ofReal_ne_top
      . apply tsum_pos
        . have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
            simp
          have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
          unfold gauss_term_ℝ at Y
          simp at Y
          exact Y
        . intro i
          simp only [exp_nonneg]
        . simp only [exp_pos]
        . exact 0
    . refine pos_iff_ne_zero.mp ?h0.a
      simp only [ENNReal.ofReal_pos]
      rw [div_pos_iff]
      left
      simp only [sub_pos, one_lt_exp_iff, inv_pos]
      constructor
      . apply cast_add_one_pos
      . apply Right.add_pos_of_pos_of_nonneg
        . simp only [exp_pos]
        . simp only [zero_le_one]
    . exact ENNReal.ofReal_ne_top
  . left
    apply zero_lt_iff.mp
    simp only [ENNReal.ofReal_pos]
    rw [div_pos_iff]
    left
    simp only [sub_pos, one_lt_exp_iff, inv_pos]
    constructor
    . apply cast_add_one_pos
    . apply Right.add_pos_of_pos_of_nonneg
      . simp only [exp_pos]
      . simp only [zero_le_one]
  . left
    exact ENNReal.ofReal_ne_top

@[simp]
theorem DiscreteGaussianSample_normalizes (num : PNat) (den : PNat) :
  ∑' x : ℤ, (DiscreteGaussianSample num den) x = 1 := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  conv =>
    left
    right
    intro x
    rw [DiscreteGaussianSample_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  . rw [ENNReal.ofReal_one.symm]
    congr 1
    apply discrete_gaussian_normalizes A
  . intro n
    apply discrete_gaussian_nonneg A 0 n
  . apply discrete_gaussian_summable A 0

end SLang
