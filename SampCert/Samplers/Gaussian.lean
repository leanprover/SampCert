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

@[simp]
theorem ite_simpl_1' (num den t : PNat) (x : ℤ) (n : ℤ) :
  @ite ENNReal (x = ↑n) (propDecidable (x = ↑n)) 0
  (@ite ENNReal (↑n = x) (Int.instDecidableEqInt (↑n) x)
  (ENNReal.ofReal ((rexp ((t : ℝ))⁻¹ - 1) / (rexp ((t : ℝ))⁻¹ + 1) * rexp (-(Complex.abs ↑x / ↑↑t))) *
    ENNReal.ofReal (rexp (-(↑(↑(Int.natAbs x) * (t : NNReal) * (den : NNReal) - (num : NNReal)) ^ 2 / ((2 : ℕ+) * ↑↑num * ↑↑t ^ 2 * ↑↑den)))))
  0) = 0 := by
  split
  . simp
  . rename_i h
    simp [h]
    intro h
    subst h
    contradiction

@[simp]
theorem DiscreteGaussianSampleLoop_normalizes (num den t : ℕ+) :
  ∑' x, (DiscreteGaussianSampleLoop num den t) x = 1 := by
  sorry




-- @[simp]
-- theorem DiscreteGaussianSampleLoop_apply_true (num den t : ℕ+) (n : ℤ) :
--   (DiscreteGaussianSampleLoop num den t) (n, true) =
--     ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1) * rexp (-(Int.natAbs n / t))) *
--     ENNReal.ofReal (rexp (-((((Int.natAbs n) * t * den - num) : NNReal) ^ 2 / ((2 : ℕ+) * ↑↑num * t ^ 2 * ↑↑den)))) := by
--   simp [DiscreteGaussianSampleLoop, tsum_bool]
--   rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
--   simp (config := { contextual := true })
--   congr
--   rw [← Complex.int_cast_abs]
--   rw [cast_natAbs]
--   simp

theorem Add1 (n : Nat) : 0 < n + 1 := by
  simp only [add_pos_iff, zero_lt_one, or_true]

-- @[simp]
-- theorem DiscreteGaussianSampleLoop_apply_true' (num den t : ℕ+) (n : ℤ) (h1 : t = ⟨ (num.val / den) + 1 , Add1 t ⟩) :
--   (DiscreteGaussianSampleLoop num den t) (n, true) =
--     ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1) * rexp (-(Int.natAbs n / t))) *
--     ENNReal.ofReal (rexp (-((((Int.natAbs n) * t * den - num)) ^ 2 / ((2 : ℕ+) * ↑↑num * t ^ 2 * ↑↑den)))) := by
--   simp only [DiscreteGaussianSampleLoop, Bind.bind, Pure.pure, SubPMF.bind_apply,
--     DiscreteLaplaceSample_apply, NNReal.coe_nat_cast, PNat.one_coe, cast_one, NNReal.coe_one,
--     div_one, one_div, Int.cast_abs, Complex.int_cast_abs, SubPMF.pure_apply, Prod.mk.injEq, mul_ite,
--     mul_one, mul_zero, tsum_bool, and_false, ↓reduceIte, and_true, BernoulliExpNegSample_apply_true,
--     cast_pow, cast_tsub, cast_mul, NNReal.coe_pow, PNat.mul_coe, PNat.pow_coe, NNReal.coe_mul,
--     zero_add]
--   rw [ENNReal.tsum_eq_add_tsum_ite (n : ℤ)]
--   simp (config := { contextual := true })
--   rw [← ENNReal.ofReal_mul]
--   rw [← ENNReal.ofReal_mul]
--   congr
--   . sorry
--   . subst t
--     simp
--     simp [mul_add]
--     simp [add_mul]
--     have A : ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) : NNReal) * (den : NNReal)
--       =  ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) * den : NNReal) := by
--       simp
--     sorry
--   . sorry
--   . sorry






noncomputable def DiscreteGaussianSample (num : PNat) (den : PNat) : RandomM ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , Add1 ti ⟩
  let num := num^2
  let den := den^2
  let r ← prob_until (DiscreteGaussianSampleLoop num den t) (λ x : Int × Bool => x.2)
  return r.1

theorem if_simpl_2' (x_1 x : ℤ) (a : ENNReal) :
  @ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (a * (@ite ENNReal (x = x_1) (propDecidable (x = (x_1, true).1))) 1 0) = 0 := by
    sorry

-- @[simp]
-- theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (x : ℤ) :
--   (DiscreteGaussianSample num den) x =
--   ENNReal.ofReal ((exp (- x^2 / (2 * ((num : NNReal) / (den : NNReal))^2))) / (∑' (y : ℤ), exp (- y^2 / (2 * ((num : NNReal) / (den : NNReal))^2)))) := by
--   simp only [DiscreteGaussianSample, Bind.bind, Pure.pure, SubPMF.bind_apply]
--   have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2) { val := ↑num / ↑den + 1, property := (sorry : 0 < ↑num / ↑den + 1) }

--   conv =>
--     left
--     right
--     intro a
--     left
--     rw [prob_until_apply_norm _ _ _ A]
--   clear A

--   simp [ENNReal.tsum_prod', tsum_bool]
--   rw [ENNReal.tsum_eq_add_tsum_ite x]
--   conv =>
--     left
--     right
--     right
--     intro x_1
--     rw [if_simpl_2']
--   simp

--   rw [← ENNReal.ofReal_mul]
--   conv =>
--     left
--     right
--     right
--     right
--     intro a
--     rw [← ENNReal.ofReal_mul sorry]

--   rw [← ENNReal.ofReal_tsum_of_nonneg]
--   rw [ENNReal.ofReal_inv_of_pos]
--   rw [← ENNReal.ofReal_mul]

--   congr
--   . rw [mul_assoc]
--     rw [← exp_add]

--     let γ := (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ)
--     have G : γ = (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) := rfl
--     rw [← G]

--     let α := (num : ℝ) ^ 2
--     have A : α = (num : ℝ) ^ 2 := rfl
--     rw [← A]

--     let β := (den : ℝ) ^ 2
--     have B : β = (den : ℝ) ^ 2 := rfl
--     rw [← B]

--     sorry

--   . sorry
--   . sorry
--   . sorry
--   . sorry

--   . sorry
--   . sorry
