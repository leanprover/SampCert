/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Properties
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Privacy

noncomputable section

open Classical

namespace SLang

variable (ε₁ ε₂ : ℕ+)

lemma exactDiffSum_sens i : sensitivity (exactDiffSum i) 1 := by
  intro l₁ l₂ H
  cases H
  · rename_i A B C H1 H2
    rw [H1, H2]
    repeat rw [exactDiffSum_append]
    simp [exactDiffSum, exactClippedSum]
    apply Int.le_of_ofNat_le_ofNat
    simp
    cases (Classical.em (C ≤ i))
    · rw [min_eq_left (by linarith)]
      rw [min_eq_left (by linarith)]
      simp
    · cases (Classical.em (C ≤ i + 1))
      · have HC : C = i + 1 := by linarith
        simp_all
      · rw [min_eq_right (by linarith)]
        rw [min_eq_right (by linarith)]
        simp
  · rename_i A C B H1 H2
    rw [H1, H2]
    repeat rw [exactDiffSum_append]
    simp [exactDiffSum, exactClippedSum]
    apply Int.le_of_ofNat_le_ofNat
    simp
    cases (Classical.em (C ≤ i))
    · rw [min_eq_left (by linarith)]
      rw [min_eq_left (by linarith)]
      simp
    · cases (Classical.em (C ≤ i + 1))
      · have HC : C = i + 1 := by linarith
        simp_all
      · rw [min_eq_right (by linarith)]
        rw [min_eq_right (by linarith)]
        simp

lemma privUnboundedMax_DP (ε : NNReal) (Hε : ε = ε₁ / ε₂) :
    PureDPSystem.prop (@privUnboundedMax ε₁ ε₂) ε := by
  suffices H : (privUnboundedMax ε₁ ε₂) = (sv9_aboveThresh_SPMF exactDiffSum 0 lucky_guess ε₁ ε₂) by
    rw [H]
    apply sv9_aboveThresh_pmf_DP
    · apply exactDiffSum_sens
    · trivial
  unfold privUnboundedMax
  unfold sv1_aboveThresh_PMF
  unfold sv9_aboveThresh_SPMF
  apply funext
  intro l
  congr
  erw [<- sv8_sv9_eq, <- sv7_sv8_eq, <- sv6_sv7_eq, <- sv5_sv6_eq,
      <- sv4_sv5_eq, <- sv3_sv4_eq, <- sv2_sv3_eq, <- sv1_sv2_eq]
