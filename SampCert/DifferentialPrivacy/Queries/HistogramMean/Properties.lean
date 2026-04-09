/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.HistogramMean.Code
import SampCert.DifferentialPrivacy.Queries.Histogram.Properties
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Properties
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privMeanHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable (dps : DPSystem ℕ)
variable (dpn : DPNoise dps)
variable (numBins : ℕ+)
variable (B : Bins ℕ numBins)
variable (unbin : Fin numBins -> ℕ+)

instance : MeasurableSpace (Option (Fin ↑numBins) × Option ℚ) := ⊤
instance : DiscreteMeasurableSpace (Option (Fin ↑numBins) × Option ℚ) where
  forall_measurableSet _ := .congr trivial rfl

instance : MeasurableSpace (Option ℚ) := ⊤
instance : DiscreteMeasurableSpace (Option ℚ) where
  forall_measurableSet _ := .congr trivial rfl

instance : MeasurableSpace (Option (Fin ↑numBins)) := ⊤
instance : DiscreteMeasurableSpace (Option (Fin ↑numBins)) where
  forall_measurableSet _ := .congr trivial rfl


/--
DP bound for the adaptive mean
-/
lemma privMeanHistogram_DP (ε₁ ε₂ : ℕ+) (τ : ℤ) (ε₃ ε₄ : ℕ+) (εA εB : NNReal)
      (HN_A : dpn.noise_priv ε₁ (ε₂ * numBins) (εA / numBins))
      (HN_B : dpn.noise_priv ε₃ (2 * ε₄) (εB / 2)):
    dps.prop (privMeanHistogram dps dpn numBins B unbin ε₁ ε₂ τ ε₃ ε₄) (εA + εB) := by
  rw [privMeanHistogram]
  apply dps.postprocess_prop
  apply dps.adaptive_compose_prop
  · apply privMaxBinAboveThreshold_DP
    apply HN_A
  · intro u
    cases u
    · simp only []
      apply (@DPSystem.prop_mono _ _ _ _ 0 εB _)
      · apply dps.const_prop
        rfl
      · apply _root_.zero_le
    · simp only []
      apply dps.postprocess_prop
      apply privNoisedBoundedMean_DP
      apply HN_B
  rfl
end SLang
