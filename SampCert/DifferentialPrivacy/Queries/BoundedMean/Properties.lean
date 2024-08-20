/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

/-!
# ``privNoisedBoundedMean`` Properties

This file proves abstract differential privacy for ``privNoisedBoundedMean``.
-/

open Classical Nat Int Real Rat

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

lemma budget_split (ε₁ ε₂ : ℕ+) :
  (ε₁ : NNReal) / (ε₂ : NNReal) = (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) + (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) := by
  field_simp
  ring_nf

/--
DP bound for noised mean.
-/
theorem privNoisedBoundedMean_DP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedBoundedMean U ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  unfold privNoisedBoundedMean
  rw [bind_bind_indep]
  apply dps.postprocess_prop
  rw [budget_split]
  apply dps.compose_prop
  · apply privNoisedBoundedSum_DP
  · apply privNoisedCount_DP

end SLang
