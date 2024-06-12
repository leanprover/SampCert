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

variable (numBins : ℕ+)
variable (B : Bins T numBins)

-- def exactBinCount (b : Fin num_bins) (l : List T) : ℤ :=
--   List.length (List.filter (fun v => B.bin v = b) l)

/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin numBins) : sensitivity (exactBinCount numBins B b) 1 := by
  rw [sensitivity]
  intros l₁ l₂ HN
  cases HN
  · rename_i l₁' l₂' v' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v' l₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v₁' l₂' v₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    -- There has to be a better way
    cases (Classical.em (B.bin v₁' = b)) <;> cases (Classical.em (B.bin v₂' = b))
    all_goals (rename_i Hrw1 Hrw2)
    all_goals (simp [Hrw1, Hrw2])

/--
DP bound for a noised bin count
-/
lemma privNoisedBinCount_DP (ε₁ ε₂ : ℕ+) (b : Fin numBins) :
  dps.prop (privNoisedBinCount numBins B ε₁ ε₂ b) (ε₁ / ((ε₂ * numBins : PNat))) := by
  unfold privNoisedBinCount
  apply dps.noise_prop
  apply exactBinCount_sensitivity

/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n * (ε₁ / (ε₂ * numBins : PNat))) := by
  sorry

/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) (ε₁ / ε₂) := by
  sorry

/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (ε₁ ε₂ : ℕ+) (τ : ℤ) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) (ε₁ / ε₂) := by
  sorry

end SLang
