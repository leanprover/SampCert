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
theorem Renyi_noised_query_NZ {nq : List T → SLang U} {α ε : ℝ} (h1 : 1 < α) {l₁ l₂ : List T} (h2 : Neighbour l₁ l₂) (h3 : zCDPBound nq ε) (h4 : NonZeroNQ nq) (h5 : NonTopRDNQ nq) (nts : NonTopNQ nq) :
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

/--
Composed queries satisfy zCDP Renyi divergence bound.
-/
theorem privCompose_zCDPBound {nq1 : List T → SLang U} {nq2 : List T → SLang V} {ε₁ ε₂ ε₃ ε₄ : ℕ+} (h1 : zCDPBound nq1 ((ε₁ : ℝ) / ε₂))  (h2 : zCDPBound nq2 ((ε₃ : ℝ) / ε₄)) (nn1 : NonZeroNQ nq1) (nn2 : NonZeroNQ nq2) (nt1 : NonTopRDNQ nq1) (nt2 : NonTopRDNQ nq2) (nts1 : NonTopNQ nq1) (nts2 : NonTopNQ nq2) :
  zCDPBound (privCompose nq1 nq2) (((ε₁ : ℝ) / ε₂) + ((ε₃ : ℝ) / ε₄)) := by
  /-
  simp [privCompose, RenyiDivergence, zCDPBound]
  intro α h3 l₁ l₂ h4
  have X := h1
  have Y := h2
  simp [zCDPBound] at h1 h2
  replace h1 := h1 α h3 l₁ l₂ h4
  replace h2 := h2 α h3 l₁ l₂ h4
  simp [RenyiDivergence] at h1 h2
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
      rw [ENNReal.mul_rpow_of_ne_top (nts1 l₂ b) (nts2 l₂ c)]
      rw [mul_assoc]
      right
      rw [mul_comm]
      rw [mul_assoc]
      right
      rw [mul_comm]
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
    rw [ENNReal.toReal_mul]
    rw [Real.log_mul]
    . rw [mul_add]
      have D := _root_.add_le_add h1 h2
      apply le_trans D
      rw [← add_mul]
      rw [mul_le_mul_iff_of_pos_right]
      . rw [← mul_add]
        rw [mul_le_mul_iff_of_pos_left]
        . ring_nf
          simp
        . simp
      . apply lt_trans zero_lt_one h3
    . apply Renyi_noised_query_NZ h3 h4 X nn1 nt1 nts1
    . apply Renyi_noised_query_NZ h3 h4 Y nn2 nt2 nts2
  -/
  sorry

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
  cases h ; rename_i h1 h2 ; cases h2 ; rename_i h2 h3 ; cases h3 ; rename_i h3 h4 ; cases h4 ; rename_i h4 h5
  cases h' ; rename_i h'1 h'2 ; cases h'2 ; rename_i h'2 h'3 ; cases h'3 ; rename_i h'3 h'4 ; cases h'4 ; rename_i h'4 h'5
  repeat any_goals constructor
  . apply privCompose_zCDPBound h1 h'1 h2 h'2 h5 h'5 h4 h'4
  . apply privCompose_NonZeroNQ h2 h'2
  . apply privCompose_NonTopSum h3 h'3
  . apply privCompose_NonTopNQ h4 h'4
  . apply privCompose_NonTopRDNQ h5 h'5 h4 h'4

end SLang
