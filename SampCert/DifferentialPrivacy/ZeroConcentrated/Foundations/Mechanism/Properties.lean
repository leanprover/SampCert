/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Mechanism.Code

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

theorem NoisedQueryDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (NoisedQuery query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  simp [DP, NoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @DiscreteGaussianGenSampleZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A
  replace bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  ring_nf
  simp
  conv =>
    left
    left
    right
    rw [mul_pow]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [← mul_assoc]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [← mul_assoc]
  simp only [inv_pow]
  rw [mul_inv_le_iff']
  . have A : (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := le_refl (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹)
    have B : 0 ≤ (α * ↑↑ε₁ ^ 2 * (↑↑ε₂ ^ 2)⁻¹) := by
      simp
      apply @le_trans ℝ _ 0 1 α (zero_le_one' ℝ) (le_of_lt h1)
    apply mul_le_mul A _ _ B
    . apply sq_le_sq.mpr
      simp only [abs_cast]
      rw [← Int.cast_sub]
      rw [← Int.cast_abs]
      apply Int.cast_le.mpr
      rw [← Int.natCast_natAbs]
      apply Int.ofNat_le.mpr
      trivial
    . apply sq_nonneg
  . rw [pow_two]
    rw [_root_.mul_pos_iff]
    left
    simp

theorem NoisedQuery_NonZeroNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonZeroNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonZeroNQ, NoisedQuery, DiscreteGaussianGenSample]
  intros l n
  exists (n - query l)
  simp
  have A : ((Δ : ℝ) * ε₂ / ε₁) ≠ 0 := by
    simp
  have X := @discrete_gaussian_pos (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) A 0 (n - query l)
  simp at X
  trivial

theorem NoisedQuery_NonTopNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonTopNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonTopNQ, NoisedQuery, DiscreteGaussianGenSample]
  intro l n
  rw [ENNReal.tsum_eq_add_tsum_ite (n - query l)]
  simp
  have X : ∀ x : ℤ, (@ite ℝ≥0∞ (x = n - query l) (propDecidable (x = n - query l)) 0
    (@ite ℝ≥0∞ (n = x + query l) (n.instDecidableEq (x + query l))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x)) 0)) = 0 := by
    intro x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  conv =>
    right
    left
    right
    intro x
    rw [X]
  simp

theorem discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  . simp [gauss_term_ℝ]
    congr 3
    ring_nf
  . rw [SG_periodic h]

theorem NoisedQuery_NonTopSum (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonTopSum (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonTopSum, NoisedQuery, DiscreteGaussianGenSample]
  intro l
  have X : ∀ n: ℤ, ∀ x : ℤ, (@ite ℝ≥0∞ (x = n - query l) (propDecidable (x = n - query l)) 0
    (@ite ℝ≥0∞ (n = x + query l) (n.instDecidableEq (x + query l))
    (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x)) 0)) = 0 := by
    intro n x
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  conv =>
    right
    left
    right
    intro n
    rw [ENNReal.tsum_eq_add_tsum_ite (n - query l)]
    simp
    right
    right
    intro x
    rw [X]
  simp
  have A : (Δ : ℝ) * ε₂ / ε₁ ≠ 0 := by
    simp
  conv =>
    right
    left
    right
    intro n
    rw [discrete_gaussian_shift A]
  simp
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  . rw [discrete_gaussian_normalizes A]
    simp
  . apply discrete_gaussian_nonneg A
  . apply discrete_gaussian_summable' A (query l)

theorem NoisedQuery_NonTopRDNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
  NonTopRDNQ (NoisedQuery query Δ ε₁ ε₂) := by
  simp [NonTopRDNQ, NoisedQuery, DiscreteGaussianGenSample]
  intro α _ l₁ l₂ _
  have A : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₁) (propDecidable (x_1 = x - query l₁)) 0
  (@ite ℝ≥0∞ (x = x_1 + query l₁) (x.instDecidableEq (x_1 + query l₁))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0 )) = 0 := by
    intro x y
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  have B : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₂) (propDecidable (x_1 = x - query l₂)) 0
    (@ite ℝ≥0∞ (x = x_1 + query l₂) (x.instDecidableEq (x_1 + query l₂))
  (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0)) = 0 := by
    intro x y
    split
    . simp
    . split
      . rename_i h1 h2
        subst h2
        simp at h1
      . simp
  conv =>
    right
    left
    right
    intro x
    left
    rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₁)]
    simp
    left
    right
    right
    intro y
    rw [A]
  simp
  conv =>
    right
    left
    right
    intro x
    right
    rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₂)]
    simp
    left
    right
    right
    intro y
    rw [B]
  simp
  clear A B
  have P : (Δ : ℝ) * ε₂ / ε₁ ≠ 0 := by
    simp
  have A : ∀ x : ℤ, ∀ l : List T, 0 < discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l)) := by
    intro x l
    have A' := @discrete_gaussian_pos _ P 0 (x - query l)
    simp at A'
    trivial
  have B : ∀ x : ℤ, 0 ≤ discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l₁)) ^ α := by
    intro x
    have A' := @discrete_gaussian_nonneg _ P 0 (x - query l₁)
    simp at A'
    apply rpow_nonneg A'
  conv =>
    right
    left
    right
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (A x l₁)]
    rw [ENNReal.ofReal_rpow_of_pos (A x l₂)]
    rw [← ENNReal.ofReal_mul (B x)]
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  . simp
  . intro n
    have X := @RenyiSumSG_nonneg _ α P (query l₁) (query l₂) n
    rw [discrete_gaussian_shift P]
    rw [discrete_gaussian_shift P]
    simp [X]
  . have X := @SummableRenyiGauss _ P (query l₁) (query l₂)
    conv =>
      right
      intro x
      rw [discrete_gaussian_shift P]
      rw [discrete_gaussian_shift P]
    simp [X]

theorem NoisedQueryzCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (NoisedQuery query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  simp [zCDP]
  repeat any_goals constructor
  . apply NoisedQueryDP
    exact bounded_sensitivity
  . apply NoisedQuery_NonZeroNQ
  . apply NoisedQuery_NonTopSum
  . apply NoisedQuery_NonTopNQ
  . apply NoisedQuery_NonTopRDNQ


end SLang
