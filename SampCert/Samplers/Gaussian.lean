/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import SampCert.Samplers.BernoulliNegativeExponential
import SampCert.Samplers.Laplace

open Classical PMF Nat Real

noncomputable def DiscreteGaussianSampleLoop (num den t : PNat) : RandomM (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSample t 1
  let y : Nat := Int.natAbs Y
  let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

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
  simp only [DiscreteGaussianSampleLoop, Bind.bind, Int.coe_natAbs, Pure.pure, SubPMF.bind_apply,
    SubPMF.pure_apply, tsum_bool, ENNReal.tsum_prod', Prod.mk.injEq, mul_ite, mul_one, mul_zero,
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
  (ENNReal.ofReal ((rexp (↑↑t)⁻¹ - 1) / (rexp (↑↑t)⁻¹ + 1) * rexp (-(Complex.abs ↑x / ↑↑t))) *
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
  simp [DiscreteGaussianSampleLoop, tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
  simp (config := { contextual := true })
  rw [ENNReal.ofReal_mul]
  have A : 0 ≤ rexp (-(Complex.abs ↑n / ↑↑t)) := by apply exp_nonneg
  . conv =>
      left
      rw [mul_assoc]
      right
      rw [← ENNReal.ofReal_mul A]
    congr
    rw [← Complex.int_cast_abs]
    rw [cast_natAbs]
    simp
  . rw [div_nonneg_iff] -- always the same
    left
    simp [exp_nonneg]
    apply Right.add_nonneg
    . apply exp_nonneg
    . simp

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

noncomputable def DiscreteGaussianSample (num : PNat) (den : PNat) : RandomM ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , Add1 ti ⟩
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2)
  return r.1

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
  = ENNReal.ofReal (rexp (-((num ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2) / (2 * den ^ 2)))) *
      ENNReal.ofReal (rexp (- ((x ^ 2 * den ^ 2) /(2 * num ^ 2)))) := by
  sorry

theorem alg_auto' (num den : ℕ+) (x : ℤ) :
  -((x : ℝ) ^ 2 * (den : ℝ) ^ 2 / ((2 : ℝ) * (num : ℝ) ^ 2)) = -(x : ℝ) ^ 2 / ((2 : ℝ) * ((num : ℝ) ^ 2 / (den : ℝ) ^ 2)) := by
  sorry

@[simp]
theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (x : ℤ) :
  (DiscreteGaussianSample num den) x =
  ENNReal.ofReal ((exp (- x^2 / (2 * ((num : NNReal) / (den : NNReal))^2))) / (∑' (y : ℤ), exp (- y^2 / (2 * ((num : NNReal) / (den : NNReal))^2)))) := by
  simp only [DiscreteGaussianSample, Bind.bind, Pure.pure, SubPMF.bind_apply]
  have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) { val := ↑num / ↑den + 1, property := (sorry : 0 < ↑num / ↑den + 1) }

  conv =>
    left
    right
    intro a
    left
    rw [prob_until_apply_norm _ _ _ A]
  clear A

  simp [ENNReal.tsum_prod', tsum_bool]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  conv =>
    left
    right
    right
    intro x_1
    rw [if_simpl_2']
  simp

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
        have A : ENNReal.ofReal (rexp (-(↑↑num ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2 / (2 * ↑↑den ^ 2)))) ≠ 0 := sorry
        have B  : ENNReal.ofReal (rexp (-(↑↑num ^ 2 * (↑(@HDiv.hDiv ℕ ℕ ℕ instHDiv ↑num ↑den) + 1) ^ 2 / (2 * ↑↑den ^ 2)))) ≠ ⊤ := sorry
        . conv =>
            left
            left
            rw [mul_comm]
            rw [← mul_assoc]
            rw [ENNReal.mul_inv_cancel A B]
          clear A B
          simp
          rw [mul_comm]
          rw [← division_def]
          congr
          . simp [alg_auto']
          . conv =>
              left
              right
              intro i
              rw [alg_auto']
            rw [← ENNReal.ofReal_tsum_of_nonneg]
            . intro n
              apply exp_nonneg
            . sorry -- Summable fun i => rexp (-↑i ^ 2 / (2 * (↑↑num ^ 2 / ↑↑den ^ 2)))
        . left
          sorry -- ≠ 0
        . left
          sorry -- ≠ 0
      . sorry -- 0 < ...
    . sorry -- ≠ 0
    . sorry -- ≠ 0
  . left
    sorry -- ≠ ⊤
  . left
    sorry -- ≠ 0

  -- rw [← ENNReal.ofReal_mul]
  -- conv =>
  --   left
  --   right
  --   right
  --   right
  --   intro a
  --   rw [← ENNReal.ofReal_mul sorry]

  -- rw [← ENNReal.ofReal_tsum_of_nonneg]
  -- rw [ENNReal.ofReal_inv_of_pos]
  -- rw [← ENNReal.ofReal_mul]

  -- congr
  -- . rw [mul_assoc]
  --   rw [← exp_add]

  --   let γ := (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ)
  --   have G : γ = (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) := rfl
  --   rw [← G]

  --   let α := (num : ℝ) ^ 2
  --   have A : α = (num : ℝ) ^ 2 := rfl
  --   rw [← A]

  --   let β := (den : ℝ) ^ 2
  --   have B : β = (den : ℝ) ^ 2 := rfl
  --   rw [← B]

  --   sorry

  -- . sorry
  -- . sorry
  -- . sorry
  -- . sorry

  -- . sorry
  -- . sorry
