/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code

/-!
# ``privNoisedQuery`` Implementation

This file proves differential privacy for ``privNoisedQuery``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

lemma privNoisedQuery_norm (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) : -- (bounded_sensitivity : sensitivity query Δ) :
  NormalMechanism (privNoisedQuery query Δ ε₁ ε₂) := by
  rw [NormalMechanism]
  intro l
  rw [privNoisedQuery]
  exact DiscreteGaussianGen_sum (Δ * ε₂) ε₁ (query l)

set_option pp.coercions false
-- set_option pp.notation false
-- set_option pp.all true
-- set_option pp.universes false

-- lemma L (x : ℝ) : x = 1 * x := by exact?

/--
The zCDP mechanism with bounded sensitivity satisfies the bound for ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDPBound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDPBound (privNoisedQuery query Δ ε₁ ε₂) (privNoisedQuery_norm query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  simp [zCDPBound, privNoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @discrete_GaussianGenSample_ZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A

  -- Pull out the ENNReal.ofReal, reducing it to a Real case
  -- Simplify this argument, it is a mess
  rw [ENNReal.div_eq_inv_mul]
  have L : (OfNat.ofNat 2 * ((Δ * ε₂).val.cast / ε₁.val.cast) ^ OfNat.ofNat 2)⁻¹ = ENNReal.ofReal ((OfNat.ofNat 2 * ((Δ * ε₂).val.cast / ε₁.val.cast) ^ OfNat.ofNat 2)⁻¹ ) := by
    simp
    rw [← div_pow]
    conv =>
      rhs
      arg 1
      rw [mul_comm]
    rw [ENNReal.mul_inv]
    · rw [ENNReal.ofReal_mul ?G1]
      case G1 =>
        simp
      congr
      · rw [ENNReal.ofReal_inv_of_pos]
        congr
        simp
        exact zero_lt_two
      · rw [ENNReal.inv_pow]
        rw [ENNReal.ofReal_pow ?G]
        case G =>
          apply div_nonneg
          · simp
          · simp
        congr
        repeat rewrite [ENNReal.div_eq_inv_mul]
        rw [ENNReal.mul_inv ?G1 ?G2]
        case G1 =>
          left
          simp
        case G2 =>
          left
          simp
        simp
        rw [div_eq_mul_inv]
        rw [ENNReal.ofReal_mul]
        · simp
          congr
          rw [ENNReal.mul_inv]
          · rw [ENNReal.ofReal_mul]
            · rw [mul_comm]
              congr
              · rw [ENNReal.ofReal_inv_of_pos]
                · congr
                  simp
                · simp
              · rw [ENNReal.ofReal_inv_of_pos]
                · congr
                  simp
                · simp
            · simp
          · left ; simp
          · left ; simp
        · simp
    · left ; simp
    · left ; simp
  rw [L]
  have H1 : OfNat.ofNat 0 ≤ ((OfNat.ofNat (OfNat.ofNat 2) * ((Δ * ε₂).val.cast / ε₁.val.cast) ^ OfNat.ofNat (OfNat.ofNat 2))⁻¹ : ℝ) := by
    simp
    apply div_nonneg
    · simp
    · simp
  have H2 : OfNat.ofNat 0 ≤ α := by linarith
  conv =>
    lhs
    arg 2
    rw [<- ENNReal.ofReal_mul]
    · skip
    . apply H1
  conv =>
    lhs
    rw [<- ENNReal.ofReal_mul]
    · skip
    · apply H2
  clear H1
  clear H2
  apply ofReal_le_ofReal_iff'.mpr


  replace bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  ring_nf
  simp
  conv =>
    left
    left
    left
    rw [mul_pow]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [← mul_assoc]

  -- Almost would be easier just to redo it... from here, the main reduction has already been finished
  left

  -- Move α to left
  conv =>
    rhs
    rw [mul_assoc]
    rw [mul_comm]
  -- Move ε₁^2 to the left
  conv =>
    lhs
    rw [<- mul_assoc]
    arg 1
    rw [mul_assoc]
    arg 2
    rw [mul_comm]
  conv =>
    lhs
    rw [<- mul_assoc]
    rw [<- mul_assoc]
  -- Add factor of 1 on the right
  conv =>
    rhs
    rw [<- (mul_one (α * ε₁ ^ 2 * ((ε₂ : ℝ)^ 2)⁻¹ : ℝ))]
  -- Reassocaite on left
  conv =>
    lhs
    rw [mul_assoc]
  apply mul_le_mul
  · simp only [inv_pow, le_refl]
  · simp
    rw [inv_mul_eq_div]
    rw [div_le_one_iff]
    left
    apply And.intro
    · apply sq_pos_iff.mpr
      simp
    · apply sq_le_sq.mpr
      clear L h2 h1 α
      rw [<- Int.dist_eq]
      rw [Int.dist_eq']
      have X :  ((query l₁ - query l₂).natAbs : ℝ) ≤ (Δ.val : ℝ) := by
        apply Nat.cast_le.mpr
        apply bounded_sensitivity
      rw [abs_eq_natAbs]
      simp only [abs_cast]
      exact X
  · apply mul_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · apply sq_nonneg
    · apply inv_nonneg.mpr
      apply sq_nonneg


/-
All outputs of the zCDP mechanism have finite probability.
-/
-- theorem privNoisedQuery_NonTopNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
--   NonTopNQ (privNoisedQuery query Δ ε₁ ε₂) := by
--   simp [NonTopNQ, privNoisedQuery, DiscreteGaussianGenSample]
--   intro l n
--   rw [ENNReal.tsum_eq_add_tsum_ite (n - query l)]
--   simp
--   have X : ∀ x : ℤ, (@ite ℝ≥0∞ (x = n - query l) (propDecidable (x = n - query l)) 0
--     (@ite ℝ≥0∞ (n = x + query l) (n.instDecidableEq (x + query l))
--   (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x)) 0)) = 0 := by
--     intro x
--     split
--     . simp
--     . split
--       . rename_i h1 h2
--         subst h2
--         simp at h1
--       . simp
--   conv =>
--     right
--     left
--     right
--     intro x
--     rw [X]
--   simp

lemma discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  . simp [gauss_term_ℝ]
    congr 3
    ring_nf
  . rw [shifted_gauss_sum h]

/-
The zCDP mechanism is normalizable.
-/
-- theorem privNoisedQuery_NonTopSum (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
--   NonTopSum (privNoisedQuery query Δ ε₁ ε₂) := by
--   simp [NonTopSum, privNoisedQuery, DiscreteGaussianGenSample]
--   intro l
--   have X : ∀ n: ℤ, ∀ x : ℤ, (@ite ℝ≥0∞ (x = n - query l) (propDecidable (x = n - query l)) 0
--     (@ite ℝ≥0∞ (n = x + query l) (n.instDecidableEq (x + query l))
--     (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x)) 0)) = 0 := by
--     intro n x
--     split
--     . simp
--     . split
--       . rename_i h1 h2
--         subst h2
--         simp at h1
--       . simp
--   conv =>
--     right
--     left
--     right
--     intro n
--     rw [ENNReal.tsum_eq_add_tsum_ite (n - query l)]
--     simp
--     right
--     right
--     intro x
--     rw [X]
--   simp
--   have A : (Δ : ℝ) * ε₂ / ε₁ ≠ 0 := by
--     simp
--   conv =>
--     right
--     left
--     right
--     intro n
--     rw [discrete_gaussian_shift A]
--   simp
--   rw [← ENNReal.ofReal_tsum_of_nonneg]
--   . rw [discrete_gaussian_normalizes A]
--     simp
--   . apply discrete_gaussian_nonneg A
--   . apply discrete_gaussian_summable' A (query l)

/-
The Renyi divergence of the zCDP mechanism is finite on neighbouring inputs.
-/
-- theorem privNoisedQuery_NonTopRDNQ (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) :
--   NonTopRDNQ (privNoisedQuery query Δ ε₁ ε₂) := by
--   simp [NonTopRDNQ, privNoisedQuery, DiscreteGaussianGenSample]
--   intro α _ l₁ l₂ _
--   have A : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₁) (propDecidable (x_1 = x - query l₁)) 0
--   (@ite ℝ≥0∞ (x = x_1 + query l₁) (x.instDecidableEq (x_1 + query l₁))
--   (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0 )) = 0 := by
--     intro x y
--     split
--     . simp
--     . split
--       . rename_i h1 h2
--         subst h2
--         simp at h1
--       . simp
--   have B : ∀ x_1 x : ℤ, (@ite ℝ≥0∞ (x_1 = x - query l₂) (propDecidable (x_1 = x - query l₂)) 0
--     (@ite ℝ≥0∞ (x = x_1 + query l₂) (x.instDecidableEq (x_1 + query l₂))
--   (ENNReal.ofReal (discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 ↑x_1)) 0)) = 0 := by
--     intro x y
--     split
--     . simp
--     . split
--       . rename_i h1 h2
--         subst h2
--         simp at h1
--       . simp
--   conv =>
--     right
--     left
--     right
--     intro x
--     left
--     rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₁)]
--     simp
--     left
--     right
--     right
--     intro y
--     rw [A]
--   simp
--   conv =>
--     right
--     left
--     right
--     intro x
--     right
--     rw [ENNReal.tsum_eq_add_tsum_ite (x - query l₂)]
--     simp
--     left
--     right
--     right
--     intro y
--     rw [B]
--   simp
--   clear A B
--   have P : (Δ : ℝ) * ε₂ / ε₁ ≠ 0 := by
--     simp
--   have A : ∀ x : ℤ, ∀ l : List T, 0 < discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l)) := by
--     intro x l
--     have A' := @discrete_gaussian_pos _ P 0 (x - query l)
--     simp at A'
--     trivial
--   have B : ∀ x : ℤ, 0 ≤ discrete_gaussian (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) 0 (↑x - ↑(query l₁)) ^ α := by
--     intro x
--     have A' := @discrete_gaussian_nonneg _ P 0 (x - query l₁)
--     simp at A'
--     apply rpow_nonneg A'
--   conv =>
--     right
--     left
--     right
--     intro x
--     rw [ENNReal.ofReal_rpow_of_pos (A x l₁)]
--     rw [ENNReal.ofReal_rpow_of_pos (A x l₂)]
--     rw [← ENNReal.ofReal_mul (B x)]
--   rw [← ENNReal.ofReal_tsum_of_nonneg]
--   . simp
--   . intro n
--     have X := @Renyi_sum_SG_nonneg _ α P (query l₁) (query l₂) n
--     rw [discrete_gaussian_shift P]
--     rw [discrete_gaussian_shift P]
--     simp [X]
--   . have X := @Renyi_Gauss_summable _ P (query l₁) (query l₂)
--     conv =>
--       right
--       intro x
--       rw [discrete_gaussian_shift P]
--       rw [discrete_gaussian_shift P]
--     simp [X]

def privNoisedQuery_AC (query : List T -> ℤ) (Δ ε₁ ε₂ : ℕ+) : ACNeighbour (privNoisedQuery query Δ ε₁ ε₂) := by
  rw [ACNeighbour]
  intro l₁ l₂ _
  rw [AbsCts]
  intro n Hk
  exfalso
  simp [privNoisedQuery, DiscreteGaussianGenSample] at Hk
  have Hk := Hk (n - query l₂)
  simp at Hk
  have A : ((Δ : ℝ) * ε₂ / ε₁) ≠ 0 := by simp
  have X := @discrete_gaussian_pos (↑↑Δ * ↑↑ε₂ / ↑↑ε₁) A 0 (n - query l₂)
  simp at X
  linarith

/--
The zCDP mechanism is ``(Δε₂/ε₁)^2``-zCDP.
-/
theorem privNoisedQuery_zCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (privNoisedQuery query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  simp [zCDP]
  apply And.intro
  · exact privNoisedQuery_AC query Δ ε₁ ε₂
  · repeat any_goals constructor
    . apply privNoisedQuery_zCDPBound
      exact bounded_sensitivity


end SLang
