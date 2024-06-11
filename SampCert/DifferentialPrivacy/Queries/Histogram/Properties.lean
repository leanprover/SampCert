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

-- /-
-- The counting query is 1-sensitive
-- -/
-- theorem exactCount_1_sensitive :
--   @sensitivity T exactCount 1 := by

/-
The noised counting query satisfies DP property
-/
-- @[simp]
-- theorem privNoisedCount_DP (ε₁ ε₂ : ℕ+) :
--   dps.prop (privNoisedCount ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
--   apply dps.noise_prop
--   apply exactCount_1_sensitive

end SLang
