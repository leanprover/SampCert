/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]
variable [dpn : DPNoise dps]
variable [HT : Inhabited T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

variable (ε₁ ε₂ : ℕ+) (ε : NNReal) (HN_bin : dpn.noise_priv ε₁ (ε₂ * numBins) (ε / numBins))

omit [DPSystem T] [DPNoise dps] [Inhabited T] in
/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin numBins) : sensitivity (exactBinCount numBins B b) 1 := by
  rw [sensitivity]
  intros _ _ H
  cases H
  all_goals simp_all [exactBinCount, exactBinCount, List.filter_cons]
  all_goals aesop

include HN_bin in
omit [Inhabited T] in
/--
DP bound for a noised bin count
-/
lemma privNoisedBinCount_DP  (b : Fin numBins) :
  dps.prop (privNoisedBinCount numBins B ε₁ ε₂ b) (ε / numBins) := by
  unfold privNoisedBinCount
  apply dpn.noise_prop HN_bin
  apply exactBinCount_sensitivity

include HN_bin in
omit [Inhabited T] in
/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (n : ℕ) (Hn : n < numBins) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n.succ * (ε / numBins)) := by
  induction n
  · unfold privNoisedHistogramAux
    simp
    apply dps.postprocess_prop
    apply dps.compose_prop (add_zero _)
    · apply privNoisedBinCount_DP; apply HN_bin
    · apply dps.const_prop; rfl
  · rename_i _ IH
    simp [privNoisedHistogramAux]
    apply dps.postprocess_prop
    apply dps.compose_prop ?arithmetic
    · apply privNoisedBinCount_DP; apply HN_bin
    · apply IH
    case arithmetic => simp; ring_nf

include HN_bin in
omit [Inhabited T] in
/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) ε := by
  unfold privNoisedHistogram
  apply (DPSystem_prop_ext _ ?HEq ?Hdp)
  case Hdp => apply privNoisedHistogramAux_DP; apply HN_bin
  case HEq => simp [predBins, mul_div_left_comm]

omit HT in
include HN_bin in
/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (τ : ℤ) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) ε := by
  unfold privMaxBinAboveThreshold
  apply dps.postprocess_prop
  apply privNoisedHistogram_DP
  apply HN_bin

end SLang
