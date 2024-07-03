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
variable (numBins : ℕ+)
variable (B : Bins ℕ numBins)
variable (unbin : Fin numBins -> ℕ+)

-- FIXME: Can I get away without these?

instance : MeasurableSpace (Option (Fin ↑numBins) × Option ℚ) where
  MeasurableSet' _ := True
  measurableSet_empty := by simp only
  measurableSet_compl := by simp only [imp_self, implies_true]
  measurableSet_iUnion := by simp only [implies_true, imp_self]

instance : DiscreteMeasurableSpace (Option (Fin ↑numBins) × Option ℚ) where
  forall_measurableSet := by simp only [MeasurableSpace.measurableSet_top, implies_true]

instance : MeasurableSpace (Option ℚ) where
  MeasurableSet' _ := True
  measurableSet_empty := by simp only
  measurableSet_compl := by simp only [imp_self, implies_true]
  measurableSet_iUnion := by simp only [implies_true, imp_self]

instance : DiscreteMeasurableSpace (Option ℚ) where
  forall_measurableSet := by simp only [MeasurableSpace.measurableSet_top, implies_true]

instance : MeasurableSpace (Option (Fin ↑numBins)) where
  MeasurableSet' _ := True
  measurableSet_empty := by simp only
  measurableSet_compl := by simp only [imp_self, implies_true]
  measurableSet_iUnion := by simp only [implies_true, imp_self]

instance : DiscreteMeasurableSpace (Option (Fin ↑numBins)) where
  forall_measurableSet := by simp only [MeasurableSpace.measurableSet_top, implies_true]


/-
DP bound for the adaptive mean
-/
lemma privMeanHistogram_DP (ε₁ ε₂ : ℕ+) (τ : ℤ) (ε₃ ε₄ : ℕ+) :
    dps.prop (privMeanHistogram dps numBins B unbin ε₁ ε₂ τ ε₃ ε₄) (ε₁/ε₂ + ε₃/ε₄) := by
  rw [privMeanHistogram]
  apply dps.postprocess_prop
  apply dps.adaptive_compose_prop
  · apply privMaxBinAboveThreshold_DP
  intro u
  cases u
  · simp only
    apply dps.prop_mono ?G1 ?G2
    case G2 => apply dps.const_prop
    simp only [_root_.zero_le]
  · rename_i mx
    simp only
    apply dps.postprocess_prop
    apply privNoisedBoundedMean_DP
end SLang
