/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Renyi Divergence

This file defines the Renyi divergence and equations for evaluating its expectation.
-/


open Real ENNReal

variable {T : Type}

/--
The Renyi divergence.
-/
noncomputable def RenyiDivergence (p q : T → ENNReal) (α : ℝ) : ℝ :=
  (α - 1)⁻¹ * Real.log (∑' x : T, (p x)^α  * (q x)^(1 - α)).toReal

/--
Closed form of the series in the definition of the Renyi divergence.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (h1 : ∀ x : T, q x ≠ 0) (h2 : ∀ x : T, q x ≠ ⊤) :
  (∑' x : T, (p x)^α  * (q x)^(1 - α)) = ∑' x : T, (p x / q x)^α  * (q x) := by
  congr 4
  ext x
  rw [ENNReal.rpow_sub]
  . rw [← ENNReal.mul_comm_div]
    rw [← ENNReal.div_rpow_of_nonneg]
    . rw [ENNReal.rpow_one]
    . apply le_of_lt (lt_trans Real.zero_lt_one h )
  . apply h1 x
  . apply h2 x

/--
Closed form for the Renyi Divergence.
-/
theorem RenyiDivergenceExpectation' (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (h1 : ∀ x : T, q x ≠ 0) (h2 : ∀ x : T, q x ≠ ⊤) :
  (α - 1)⁻¹ * Real.log ((∑' x : T, (p x)^α  * (q x)^(1 - α))).toReal = (α - 1)⁻¹ * Real.log (∑' x : T, (p x / q x)^α  * (q x)).toReal := by
  congr 4
  ext x
  rw [ENNReal.rpow_sub]
  . rw [← ENNReal.mul_comm_div]
    rw [← ENNReal.div_rpow_of_nonneg]
    . rw [ENNReal.rpow_one]
    . apply le_of_lt (lt_trans Real.zero_lt_one h )
  . apply h1 x
  . apply h2 x

/--
The Renyi divergence is monotonic in the value of its sum.
-/
lemma RenyiDivergence_mono_sum (x y : ℝ) (α : ℝ) (h : 1 < α) : Real.exp ((α - 1) * x) ≤ Real.exp ((α - 1) * y) -> (x ≤ y) := by
  intro H
  have H1 : ((α - 1) * x) ≤ ((α - 1) * y) := exp_le_exp.mp H
  -- refine (mul_le_mul_iff_right ?a).mp ?a
  -- apply?
  -- refine ((@ENNReal.mul_le_mul_left x y _ _ ).mp _)
  -- apply mul_lt_mul_left_of_neg
  -- refine (mul_le_mul_left ?a0).mp ?a -- ?????

  -- How annoying

  sorry

lemma RenyiDivergence_exp (p q : T → ENNReal) {α : ℝ} (h : 1 < α) :
  Real.exp ((α - 1) * RenyiDivergence p q α) = (∑' x : T, (p x)^α  * (q x)^(1 - α)).toReal := by
  simp only [RenyiDivergence]
  rw [<- mul_assoc]
  have test : (α - 1) * (α - 1)⁻¹ = 1 := by
    refine mul_inv_cancel ?h
    linarith
  rw [test]
  clear test
  simp
  rw [Real.exp_log]
  apply ENNReal.toReal_pos_iff.mpr
  apply And.intro
  · sorry
  · sorry
