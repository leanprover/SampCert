/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import SampCert.Util.Log
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Renyi Divergence

This file defines the Renyi divergence and equations for evaluating its expectation.
-/


open Real ENNReal PMF

variable {T : Type}

/--
Definition of the Renyi divergence as an EReal.


-/
noncomputable def RenyiDivergence_def (p q : PMF T) (α : ℝ) : EReal :=
  (α - 1)⁻¹  * (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))

/--
Equation for the Renyi divergence series in terms of the Renyi Divergence
-/
lemma RenyiDivergence_def_exp (p q : PMF T) {α : ℝ}
  (h : 1 < α)
  (H1 : 0 < ∑' (x : T), p x ^ α * q x ^ (1 - α))
  (H2 : ∑' (x : T), p x ^ α * q x ^ (1 - α) < ⊤) :
  eexp (((α - 1)) * RenyiDivergence_def p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)) := by
  simp only [RenyiDivergence_def]
  rw [<- mul_assoc]
  have Hinvert : ((↑α - 1) * ↑(α - 1)⁻¹ : EReal) = 1 := by
    clear H1
    clear H2
    have Hsub : ((↑α - 1) : EReal) = (α - 1 : ℝ) := by simp
    rw [Hsub]
    have Hundo_coe (r1 r2 : ℝ) : (r1 : EReal) * (r2 : EReal) = ((r1 * r2 : ℝ) : EReal) := by
      rw [EReal.coe_mul]
    rw [Hundo_coe]
    have Hinv : (α - 1) * (α - 1)⁻¹ = 1 := by
      apply mul_inv_cancel
      linarith
    rw [Hinv]
    simp
  rw [Hinvert]
  clear Hinvert
  simp

-- FIXME: where is this in mathlib?
def AbsolutelyContinuous (p q : T -> ENNReal) : Prop := ∀ x : T, q x = 0 -> p x = 0

/--
Closed form of the series in the definition of the Renyi divergence.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (H : AbsolutelyContinuous p q) :
  (∑' x : T, (p x)^α  * (q x)^(1 - α)) = ∑' x: T, (p x / q x)^α  * (q x) := by
  congr 4
  ext x
  rw [AbsolutelyContinuous] at H
  -- have HK : (q x ≠ 0 ∨ p x = 0) := by
  --   apply Decidable.not_or_of_imp
  --   apply H
  generalize Hvq : q x = vq
  cases vq <;> simp
  · -- q x = ⊤
    rw [ENNReal.zero_rpow_of_pos ?H]
    case H => linarith
    simp
    right
    apply h
  · rename_i vq'
    cases (Classical.em (vq' = 0))
    · -- q x = 0
      -- by abs. cty. p x = 0
      rename_i Hvq'
      have Hp : p x = 0 := by
        apply H
        simp [Hvq, Hvq']
      simp [Hp, Hvq', Hvq]
      left
      linarith
    · -- q x ∈ ℝ+
      rename_i Hvq'
      generalize Hvp : p x = vp
      cases vp <;> simp
      · -- q x ∈ ℝ+, p x = ⊤
        rw [ENNReal.top_rpow_of_pos ?H]
        case H => linarith
        rw [top_mul']
        split
        · exfalso
          rename_i Hcont
          apply Hvq'
          have Hcont' : (vq' : ENNReal) = 0 ∧ 0 < (1-α) ∨ (vq' : ENNReal) = ⊤ ∧ (1-α)< 0 := by
            exact rpow_eq_zero_iff.mp Hcont
          cases Hcont'
          · simp_all only [some_eq_coe, none_eq_top, zero_ne_top]
          · simp_all only [some_eq_coe, none_eq_top, top_rpow_of_neg, coe_ne_top, sub_neg, and_true]
        · rw [top_mul']
          split
          · simp_all only [some_eq_coe, none_eq_top, zero_ne_top]
          · rfl
      · rename_i vp
        cases (Classical.em (vq' = 0))
        · -- q x ∈ ℝ+, p x = 0
          rename_i Hvp'
          simp_all
        · -- q x ∈ ℝ+, p x ∈ ℝ+
          rename_i Hvp'
          rw [ENNReal.rpow_sub]
          . rw [← ENNReal.mul_comm_div]
            rw [← ENNReal.div_rpow_of_nonneg]
            . rw [ENNReal.rpow_one]
            . apply le_of_lt (lt_trans Real.zero_lt_one h )
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_eq_zero]
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_ne_top]

-- FIXME
/--
The Renyi divergence is monotonic in the value of its sum.
-/
lemma RenyiDivergence_mono_sum (x y : ℝ) (α : ℝ) (h : 1 < α) : (Real.exp ((α - 1) * x)) ≤ (Real.exp ((α - 1) * y)) -> (x ≤ y) := by
  intro H
  apply le_of_mul_le_mul_left
  · exact exp_le_exp.mp H
  · linarith

theorem RenyiDivergence_def_nonneg (p q : PMF T) (α : ℝ) : (0 ≤ RenyiDivergence_def p q α) := by
  -- See paper
  sorry

theorem RenyiDivergence_def_zero (p q : PMF T) (α : ℝ) : p = q <-> (0 = RenyiDivergence_def p q α) := by
  -- See paper
  sorry

lemma RenyiDivergence_def_log_sum_nonneg (p q : PMF T) (α : ℝ) : (0 ≤ (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))) := by
  -- Follows from RenyiDivergence_def_nonneg
  sorry



/--
The Renyi divergence.
-/
noncomputable def RenyiDivergence (p q : PMF T) (α : ℝ) : ENNReal :=
  ENNReal.ofEReal (RenyiDivergence_def p q α)

-- MARKUSDE: We evaluate through the ENNReal.ofEReal using ``RenyiDivergence_def_nonneg``, these are some special cases
theorem RenyiDivergence_aux_zero (p q : PMF T) (α : ℝ) : p = q <-> RenyiDivergence p q α = 0
  := sorry



-- Unused
/-
Closed form for the Renyi Divergence.
-/
-- theorem RenyiDivergenceExpectation' (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (h1 : ∀ x : T, q x ≠ 0) (h2 : ∀ x : T, q x ≠ ⊤) :
--   (α - 1)⁻¹ * Real.log ((∑' x : T, (p x)^α  * (q x)^(1 - α))).toReal = (α - 1)⁻¹ * Real.log (∑' x : T, (p x / q x)^α  * (q x)).toReal := by
--   congr 4
--   ext x
--   rw [ENNReal.rpow_sub]
--   . rw [← ENNReal.mul_comm_div]
--     rw [← ENNReal.div_rpow_of_nonneg]
--     . rw [ENNReal.rpow_one]
--     . apply le_of_lt (lt_trans Real.zero_lt_one h )
--   . apply h1 x
--   . apply h2 x
