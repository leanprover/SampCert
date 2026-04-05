/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.ParHistogram.Code
import SampCert.DifferentialPrivacy.Queries.Histogram.Properties
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privParHistogram`` Properties

This file proves abstract differential privacy for the parallel noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPPar T]
variable [dpn : DPNoise dps.toDPSystem]
variable [HT : Inhabited T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

variable (ε₁ ε₂ : ℕ+) (ε : NNReal) (HN_bin : dpn.noise_priv ε₁ ε₂ ε)

include HN_bin in
/--
DP bound for a noised bin count
-/
lemma privParNoisedBinCount_DP  (b : Fin numBins) :
  dps.prop (privParNoisedBinCount numBins B ε₁ ε₂ b) ε := by
  unfold privParNoisedBinCount
  apply dpn.noise_prop HN_bin
  apply exactBinCount_sensitivity


include HN_bin in
lemma privParNoisedHistogramAux_DP (n : ℕ) (Hn : n < numBins) :
    dps.prop (privParNoisedHistogramAux numBins B ε₁ ε₂ n Hn) ε := by
  induction n
  · unfold privParNoisedHistogramAux
    simp
    apply dps.postprocess_prop
    apply (@DPPar.prop_par _ _ _ _ _ _ ε 0)
    · symm
      apply max_eq_left
      apply _root_.zero_le
    · simp [privParNoisedBinCount]
      apply dpn.noise_prop HN_bin
      apply exactBinCount_sensitivity
    · apply dps.const_prop
      rfl
  · rename_i _ IH
    simp [privParNoisedHistogramAux]
    apply dps.postprocess_prop
    apply DPPar.prop_par ?arithmetic
    · apply privParNoisedBinCount_DP
      apply HN_bin
    · apply IH
    case arithmetic => simp


include HN_bin in
/--
DP bound for a noised histogram
-/
lemma privParNoisedHistogram_DP :
  dps.prop (privParNoisedHistogram numBins B ε₁ ε₂) ε := by
  unfold privParNoisedHistogram
  apply (DPSystem_prop_ext _ ?HEq ?Hdp)
  case Hdp => apply privParNoisedHistogramAux_DP; apply HN_bin
  case HEq => simp [predBins, mul_div_left_comm]
