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

instance : Inhabited (Option (Fin ↑numBins) × Option ℚ) where
  default := sorry

instance : MeasurableSpace (Option (Fin ↑numBins) × Option ℚ) where
  MeasurableSet' := sorry
  measurableSet_empty := sorry
  measurableSet_compl := sorry
  measurableSet_iUnion := sorry

instance : DiscreteMeasurableSpace (Option (Fin ↑numBins) × Option ℚ) where
  forall_measurableSet := sorry

instance : Countable (Option (Fin ↑numBins) × Option ℚ) where
 exists_injective_nat' := sorry


instance : Inhabited (Option ℚ) where
  default := sorry

instance : MeasurableSpace (Option ℚ) where
  MeasurableSet' := sorry
  measurableSet_empty := sorry
  measurableSet_compl := sorry
  measurableSet_iUnion := sorry

instance : DiscreteMeasurableSpace (Option ℚ) where
  forall_measurableSet := sorry

instance : Countable (Option ℚ) where
 exists_injective_nat' := sorry


instance : Inhabited (Option (Fin ↑numBins)) where
  default := sorry

instance : MeasurableSpace (Option (Fin ↑numBins)) where
  MeasurableSet' := sorry
  measurableSet_empty := sorry
  measurableSet_compl := sorry
  measurableSet_iUnion := sorry

instance : DiscreteMeasurableSpace (Option (Fin ↑numBins)) where
  forall_measurableSet := sorry

instance : Countable (Option (Fin ↑numBins)) where
 exists_injective_nat' := sorry





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
    -- Either strenghten 0-DP for constants, or prove that DP is monotonic.
    sorry
  · rename_i mx
    simp only
    apply dps.postprocess_prop
    apply privNoisedBoundedMean_DP
end SLang
