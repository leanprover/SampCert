/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# zCDP Composition

This file builds up to a zCDP bound on composed zCDP queries. In this definition of
composition, query values cannot depend on the value of prior queries.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

variable { T U V : Type }
variable [Inhabited U]
variable [Inhabited V]
variable [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/--
Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privCompose_zCDPBound {nq1 : Mechanism T U} {nq2 : Mechanism T V} {ε₁ ε₂ ε₃ ε₄ : ℕ+}
  (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂))  (h2 : zCDPBound nq2 ((ε₃ : ℝ) / ε₄))
  (Ha1 : ACNeighbour nq1) (Ha2 : ACNeighbour nq2) :
  zCDPBound (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [privCompose, RenyiDivergence, zCDPBound]
  intro α h3 l₁ l₂ h4
  simp [zCDPBound] at h1 h2
  replace h1 := h1 α h3 l₁ l₂ h4
  replace h2 := h2 α h3 l₁ l₂ h4
  simp [RenyiDivergence] at h1 h2
  unfold RenyiDivergence_def
  unfold RenyiDivergence_def at h1 h2
  rw [DFunLike.coe]
  rw [PMF.instFunLike]
  simp
  repeat rw [SLang.toPMF]
  have CG1 (b : U) : nq1 l₂ b ≠ ⊤ := by exact PMF.apply_ne_top (nq1 l₂) b
  have CG2 (b : V) : nq2 l₂ b ≠ ⊤ := by exact PMF.apply_ne_top (nq2 l₂) b
  simp
  rw [tsum_prod' ENNReal.summable (fun b : U => ENNReal.summable)]
  sorry
    /-
    simp
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [compose_sum_rw]
      rw [compose_sum_rw]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h3))]
      rw [ENNReal.mul_rpow_of_ne_top (CG1 b) (CG2 c)]
      rw [mul_assoc]
      right
      rw [mul_comm]
      rw [mul_assoc]
      right
      rw [mul_comm]
    clear CG1
    clear CG2
    conv =>
      left
      right
      right
      right
      right
      intro b
      right
      intro c
      rw [← mul_assoc]
    conv =>
      left
      right
      right
      right
      right
      intro b
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right]
    rw [← elog_mul]

    conv at h1 =>
      lhs
      arg 1
      arg 2
      arg 1
      arg 1
      intro x
      rw [DFunLike.coe]
      rw [PMF.instFunLike]
      rw [SLang.toPMF]
      rw [SLang.toPMF]
      simp
    conv at h2 =>
      lhs
      arg 1
      arg 2
      arg 1
      arg 1
      intro x
      rw [DFunLike.coe]
      rw [PMF.instFunLike]
      rw [SLang.toPMF]
      rw [SLang.toPMF]
      simp

    have log_nonneg_1 : 0 ≤ (∑' (i : U), nq1 l₁ i ^ α * nq1 l₂ i ^ (1 - α)).elog := by
      have Hac1 : AbsCts ((nq1 l₁).toPMF (HNorm1 l₁)) ((nq1 l₂).toPMF (HNorm1 l₂)) := by exact Ha1 l₁ l₂ h4
      have Hnn1 := (RenyiDivergence_def_log_sum_nonneg ((nq1 l₁).toPMF (HNorm1 l₁)) ((nq1 l₂).toPMF (HNorm1 l₂)) Hac1 h3)
      conv at Hnn1 =>
        rhs
        arg 1
        arg 1
        intro x
        rw [DFunLike.coe]
        rw [PMF.instFunLike]
        rw [SLang.toPMF]
        rw [SLang.toPMF]
        simp
      apply Hnn1
    have log_nonneg_2 :  0 ≤ (∑' (i : V), nq2 l₁ i ^ α * nq2 l₂ i ^ (1 - α)).elog := by
      have Hac2 : AbsCts ((nq2 l₁).toPMF (HNorm2 l₁)) ((nq2 l₂).toPMF (HNorm2 l₂)) := by exact Ha2 l₁ l₂ h4
      have Hnn2 := (RenyiDivergence_def_log_sum_nonneg ((nq2 l₁).toPMF (HNorm2 l₁)) ((nq2 l₂).toPMF (HNorm2 l₂)) Hac2 h3)
      conv at Hnn2 =>
        rhs
        arg 1
        arg 1
        intro x
        rw [DFunLike.coe]
        rw [PMF.instFunLike]
        rw [SLang.toPMF]
        rw [SLang.toPMF]
        simp
      apply Hnn2

    -- Split up the series
    rw [ofEReal_mul_nonneg]
    · simp only [ofEReal_real]
      -- In order to distribute ofReal, we need the logarithms to be nonegative
      rw [ofEReal_plus_nonneg log_nonneg_1 log_nonneg_2]

      -- Distribute
      rw [CanonicallyOrderedCommSemiring.left_distrib]
      apply (@le_trans _ _ _ (ENNReal.ofReal (2⁻¹ * (↑↑ε₁ ^ 2 / ↑↑ε₂ ^ 2) * α) +  ENNReal.ofReal (2⁻¹ * (↑↑ε₃ ^ 2 / ↑↑ε₄ ^ 2) * α)))
      · -- apply?
        apply _root_.add_le_add
        · rw [ofEReal_mul_nonneg] at h1
          · apply h1
          · apply EReal.coe_nonneg.mpr
            apply inv_nonneg.mpr
            linarith
          · apply log_nonneg_1
        · rw [ofEReal_mul_nonneg] at h2
          · apply h2
          · apply EReal.coe_nonneg.mpr
            apply inv_nonneg.mpr
            linarith
          · apply log_nonneg_2
      · clear h1 h2
        rw [<- ENNReal.ofReal_add]
        · apply ofReal_le_ofReal_iff'.mpr
          left
          rw [← add_mul]
          rw [mul_le_mul_iff_of_pos_right]
          · rw [← mul_add]
            rw [mul_le_mul_iff_of_pos_left]
            · ring_nf
              simp
            · simp only [inv_pos, Nat.ofNat_pos]
          · linarith
        · apply mul_nonneg
          · apply mul_nonneg
            · simp
            · apply div_nonneg
              · exact sq_nonneg ε₁.val.cast
              · exact sq_nonneg ε₂.val.cast
          · linarith
        · apply mul_nonneg
          · apply mul_nonneg
            · simp
            · apply div_nonneg
              · exact sq_nonneg ε₃.val.cast
              · exact sq_nonneg ε₄.val.cast
          · linarith
    · simp
      linarith
    · apply Left.add_nonneg
      · apply log_nonneg_1
      · apply log_nonneg_2
  -/

/-
Renyi divergence beteeen composed queries on neighbours are finite.
-/
-- theorem privCompose_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : List T → SLang V} (nt1 : NonTopRDNQ nq1) (nt2 : NonTopRDNQ nq2) (nn1 : NonTopNQ nq1) (nn2 : NonTopNQ nq2) :
--   NonTopRDNQ (privCompose nq1 nq2) := by
--   simp [NonTopRDNQ] at *
--   intro α h1 l₁ l₂ h2
--   replace nt1 := nt1 α h1 l₁ l₂ h2
--   replace nt2 := nt2 α h1 l₁ l₂ h2
--   simp [privCompose]
--   rw [ENNReal.tsum_prod']
--   simp
--   conv =>
--     right
--     left
--     right
--     intro x
--     right
--     intro y
--     congr
--     . left
--       rw [compose_sum_rw]
--     . left
--       rw [compose_sum_rw]
--   conv =>
--     right
--     left
--     right
--     intro x
--     right
--     intro y
--     rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h1))]
--     rw [ENNReal.mul_rpow_of_ne_top (nn1 l₂ x) (nn2 l₂ y)]
--     rw [mul_assoc]
--     right
--     rw [mul_comm]
--     rw [mul_assoc]
--     right
--     rw [mul_comm]
--   conv =>
--     right
--     left
--     right
--     intro x
--     right
--     intro y
--     rw [← mul_assoc]
--   conv =>
--     right
--     left
--     right
--     intro x
--     rw [ENNReal.tsum_mul_left]
--   rw [ENNReal.tsum_mul_right]
--   intro H
--   rw [mul_eq_top] at H
--   cases H
--   . rename_i h3
--     cases h3
--     rename_i h4 h5
--     contradiction
--   . rename_i h3
--     cases h3
--     rename_i h4 h5
--     contradiction


def privCompose_AC (nq1 : Mechanism T U) (nq2 : Mechanism T V) (Hac1 : ACNeighbour nq1) (Hac2 : ACNeighbour nq2) :
    ACNeighbour (privCompose nq1 nq2) := by
  rw [ACNeighbour] at *
  intro l₁ l₂ Hn
  have Hac1 := Hac1 l₁ l₂ Hn
  have Hac2 := Hac2 l₁ l₂ Hn
  rw [AbsCts] at *
  intro x
  rcases x with ⟨ u, v ⟩
  intro Hk
  simp [privCompose] at *
  intro i
  cases (Hk i)
  · rename_i Hk
    left
    apply Hac1
    apply Hk
  · rename_i Hk
    right
    intro H
    apply Hac2
    apply Hk
    apply H


/--
``privCompose`` satisfies zCDP
-/
theorem privCompose_zCDP (nq1 : Mechanism T U) (nq2 : Mechanism T V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : zCDP nq2 ((ε₃ : ℝ) / ε₄)) :
    zCDP (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  rcases h with ⟨ Hac1, Hb1 ⟩
  rcases h' with ⟨ Hac2, Hb2 ⟩
  apply And.intro
  · exact privCompose_AC nq1 nq2 Hac1 Hac2
  · exact privCompose_zCDPBound Hb1 Hb2 Hac1 Hac2

end SLang
