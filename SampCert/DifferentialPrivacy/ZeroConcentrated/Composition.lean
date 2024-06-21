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

lemma ENNReal_toReal_NZ (x : ENNReal) (h1 : x ≠ 0) (h2 : x ≠ ⊤) :
  x.toReal ≠ 0 := by
  unfold ENNReal.toReal
  unfold ENNReal.toNNReal
  simp
  constructor ; any_goals trivial

lemma simp_α_1 {α : ℝ} (h : 1 < α) : 0 < α := by
  apply @lt_trans _ _ _ 1 _ _ h
  simp only [zero_lt_one]

/--
The Renyi Divergence between neighbouring inputs of noised queries is nonzero.
-/
theorem Renyi_noised_query_NZ {nq : List T → SLang U} {HNorm : NormalMechanism nq} {α ε : ℝ}
  (h1 : 1 < α) {l₁ l₂ : List T} (h2 : Neighbour l₁ l₂) (h3 : zCDPBound nq HNorm ε)
  (h4 : NonZeroNQ nq) (h5 : NonTopRDNQ nq) (nts : NonTopNQ nq) :
  (∑' (i : U), nq l₁ i ^ α * nq l₂ i ^ (1 - α)).toReal ≠ 0 := by
  simp [zCDPBound] at h3
  replace h3 := h3 α h1 l₁ l₂ h2
  simp [RenyiDivergence] at h3
  simp [NonZeroNQ] at h4
  simp [NonTopRDNQ] at h5
  replace h5 := h5 α h1 l₁ l₂ h2
  have h6 := h4 l₁
  have h7 := h4 l₂
  apply ENNReal_toReal_NZ
  . by_contra CONTRA
    rw [ENNReal.tsum_eq_zero] at CONTRA
    replace CONTRA := CONTRA default
    replace h6 := h6 default
    replace h7 := h7 default
    rw [_root_.mul_eq_zero] at CONTRA
    cases CONTRA
    . rename_i h8
      rw [rpow_eq_zero_iff_of_pos] at h8
      contradiction
      apply simp_α_1 h1
    . rename_i h8
      rw [ENNReal.rpow_eq_zero_iff] at h8
      cases h8
      . rename_i h8
        cases h8
        contradiction
      . rename_i h8
        cases h8
        rename_i h8 h9
        replace nts := nts l₂ default
        contradiction
  . exact h5

set_option pp.coercions false

/--
Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privCompose_zCDPBound {nq1 : List T → SLang U} {nq2 : List T → SLang V} {HNorm1 : ∀ l, HasSum (nq1 l) 1} {HNorm2 : ∀ l, HasSum (nq2 l) 1} {ε₁ ε₂ ε₃ ε₄ : ℕ+}
  (h1 : zCDPBound nq1 HNorm1 ((ε₁ : ℝ) / ε₂))  (h2 : zCDPBound nq2 HNorm2 ((ε₃ : ℝ) / ε₄)) :
  zCDPBound (privCompose nq1 nq2) (privCompose_norm nq1 nq2 HNorm1 HNorm2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [privCompose, RenyiDivergence, zCDPBound]
  intro α h3 l₁ l₂ h4
  have X := h1
  have Y := h2
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
  have CG1 (b : U) : nq1 l₂ b ≠ ⊤ := by
    have HS : (∑'(u : U), nq1 l₂ u) = 1 := by exact HasSum.tsum_eq (HNorm1 l₂)
    have Hs : nq1 l₂ b ≤ (∑'(u : U), nq1 l₂ u) := by exact ENNReal.le_tsum b
    rw [HS] at Hs
    rename_i inst inst_1
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [top_le_iff, one_ne_top]
  have CG2 (b : V) : nq2 l₂ b ≠ ⊤ := by
    have HS : (∑'(u : V), nq2 l₂ u) = 1 := by exact HasSum.tsum_eq (HNorm2 l₂)
    have Hs : nq2 l₂ b ≤ (∑'(u : V), nq2 l₂ u) := by exact ENNReal.le_tsum b
    rw [HS] at Hs
    rename_i inst inst_1
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [top_le_iff, one_ne_top]
  simp
  rw [tsum_prod' ENNReal.summable (fun b : U => ENNReal.summable)]
  . simp
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
      have Hac1 : AbsCts ((nq1 l₁).toPMF (HNorm1 l₁)) ((nq1 l₂).toPMF (HNorm1 l₂)) := by sorry
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
      have Hac2 : AbsCts ((nq2 l₁).toPMF (HNorm2 l₁)) ((nq2 l₂).toPMF (HNorm2 l₂)) := by sorry
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

/--
All outputs of a composed query have finite probability.
-/
theorem privCompose_NonTopNQ {nq1 : List T → SLang U} {nq2 : List T → SLang V} (nt1 : NonTopNQ nq1) (nt2 : NonTopNQ nq2) :
  NonTopNQ (privCompose nq1 nq2) := by
  simp [NonTopNQ] at *
  intro l a b
  replace nt1 := nt1 l a
  replace nt2 := nt2 l b
  simp [privCompose]
  rw [compose_sum_rw]
  rw [mul_eq_top]
  intro H
  cases H
  . rename_i H
    cases H
    contradiction
  . rename_i H
    cases H
    contradiction

/--
Renyi divergence beteeen composed queries on neighbours are finite.
-/
theorem privCompose_NonTopRDNQ {nq1 : List T → SLang U} {nq2 : List T → SLang V} (nt1 : NonTopRDNQ nq1) (nt2 : NonTopRDNQ nq2) (nn1 : NonTopNQ nq1) (nn2 : NonTopNQ nq2) :
  NonTopRDNQ (privCompose nq1 nq2) := by
  simp [NonTopRDNQ] at *
  intro α h1 l₁ l₂ h2
  replace nt1 := nt1 α h1 l₁ l₂ h2
  replace nt2 := nt2 α h1 l₁ l₂ h2
  simp [privCompose]
  rw [ENNReal.tsum_prod']
  simp
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    congr
    . left
      rw [compose_sum_rw]
    . left
      rw [compose_sum_rw]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (lt_trans zero_lt_one h1))]
    rw [ENNReal.mul_rpow_of_ne_top (nn1 l₂ x) (nn2 l₂ y)]
    rw [mul_assoc]
    right
    rw [mul_comm]
    rw [mul_assoc]
    right
    rw [mul_comm]
  conv =>
    right
    left
    right
    intro x
    right
    intro y
    rw [← mul_assoc]
  conv =>
    right
    left
    right
    intro x
    rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
  intro H
  rw [mul_eq_top] at H
  cases H
  . rename_i h3
    cases h3
    rename_i h4 h5
    contradiction
  . rename_i h3
    cases h3
    rename_i h4 h5
    contradiction

/--
``privCompose`` satisfies zCDP
-/
theorem privCompose_zCDP (nq1 : List T → SLang U) (nq2 : List T → SLang V) (ε₁ ε₂ ε₃ ε₄ : ℕ+) (h : zCDP nq1 ((ε₁ : ℝ) / ε₂))  (h' : zCDP nq2 ((ε₃ : ℝ) / ε₄)) :
  zCDP (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  simp [zCDP] at *
  rcases h with ⟨ Hn1, Hb1 ⟩
  rcases h' with ⟨ Hn2, Hb2 ⟩
  exists (privCompose_norm nq1 nq2 Hn1 Hn2)
  exact privCompose_zCDPBound Hb1 Hb2

end SLang
