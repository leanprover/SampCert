/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Code
import SampCert.Samplers.LaplaceGen.Basic

/-!
# Properties of ``privNoisedQueryPure``

This file proves pure differential privacy for ``privNoisedQueryPure``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

lemma natAbs_to_abs (a b : ℤ) :
  (a - b).natAbs = |(a : ℝ) - (b : ℝ)| := by
  rw [Int.cast_natAbs]
  simp only [cast_abs, Int.cast_sub]

lemma normalizing_constant_nonzero (ε₁ ε₂ Δ : ℕ+) :
  (rexp (ε₁ / (Δ * ε₂)) - 1) / (rexp (ε₁ / (Δ * ε₂)) + 1) ≠ 0 := by
  field_simp
  intro h
  have A : 0 < (ε₁ : ℝ) / (Δ * ε₂) := by
    simp
  have B : rexp 0 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
    exact exp_lt_exp.mpr A
  rw [exp_zero] at B
  rw [_root_.div_eq_zero_iff] at h
  rcases h with h | h
  · rw [sub_eq_zero] at h
    have C : 1 ≠ rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
      exact _root_.ne_of_lt B
    rw [h] at C
    contradiction
  · have hp : 0 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) + 1 := by
      have := exp_pos ((ε₁ : ℝ) / (Δ * ε₂))
      linarith
    linarith

/--
Differential privacy bound for a ``privNoisedQueryPure``
-/
theorem privNoisedQueryPure_DP_bound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (privNoisedQueryPure query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x
  simp [privNoisedQueryPure]
  simp [DiscreteLaplaceGenSamplePMF]
  simp [DFunLike.coe, PMF.instFunLike]
  rw [← ENNReal.ofReal_div_of_pos]
  · apply ofReal_le_ofReal
    rw [division_def]
    rw [mul_inv]
    rw [← mul_assoc]
    conv =>
      left
      left
      rw [mul_assoc]
      right
      rw [mul_comm]
    conv =>
      left
      left
      rw [← mul_assoc]
      left
      rw [mul_inv_cancel₀ (normalizing_constant_nonzero ε₁ ε₂ Δ)]
    simp only [one_mul]
    rw [← division_def]
    rw [← exp_sub]
    simp only [sub_neg_eq_add, exp_le_exp]
    rw [neg_div']
    rw [div_add_div_same]
    rw [division_def]
    apply (mul_inv_le_iff₀' _).mpr
    · have B : ((Δ : ℝ) * ε₂ / ε₁) * ((ε₁ : ℝ) / ε₂) = Δ := by
        field_simp
      rw [B]
      clear B

      rw [add_comm]
      ring_nf
      -- Triangle inequality
      have C := abs_sub_abs_le_abs_sub ((x : ℝ) - ((query l₂ : ℤ) : ℝ)) ((x : ℝ) - ((query l₁ : ℤ) : ℝ))
      apply le_trans C
      clear C
      simp

      simp [sensitivity] at bounded_sensitivity
      replace bounded_sensitivity := bounded_sensitivity l₁ l₂ neighbours

      rw [← natAbs_to_abs]
      exact Nat.cast_le.mpr bounded_sensitivity

    · simp
  · rw [_root_.mul_pos_iff]
    left
    constructor
    · rw [_root_.div_pos_iff]
      left
      have A : 1 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
        rw [← exp_zero]
        apply exp_lt_exp.mpr
        simp
      constructor
      · simp [A]
      · apply @lt_trans _ _ _ 2 _
        · simp
        · rw [← one_add_one_eq_two]
          exact (add_lt_add_iff_right 1).mpr A
    · apply exp_pos

def laplace_pureDP_noise_priv (ε₁ ε₂ : ℕ+) (ε : NNReal) : Prop := (ε₁ : NNReal) / ε₂ = ε

/--
Laplace noising mechanism ``privNoisedQueryPure`` produces a pure ``ε₁/ε₂``-DP mechanism from a Δ-sensitive query.
-/
theorem privNoisedQueryPure_DP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (ε : NNReal) (HN : laplace_pureDP_noise_priv ε₁ ε₂ ε) (bounded_sensitivity : sensitivity query Δ) :
    PureDP (privNoisedQueryPure query Δ ε₁ ε₂) ε := by
  unfold laplace_pureDP_noise_priv at HN
  rw [<- HN]
  simp [PureDP]
  apply privNoisedQueryPure_DP_bound
  apply bounded_sensitivity

end SLang
