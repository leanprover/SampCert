/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Count.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privNoisedCount`` Properties

This file proves abstract differential privacy for ``privNoisedCount``.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}

/--
The counting query is 1-sensitive
-/
theorem exactCount_1_sensitive :
  @sensitivity T exactCount 1 := by
  simp [exactCount, sensitivity]
  intros l₁ l₂ H
  cases H
  · rename_i a b n h1 h2
    subst h1 h2
    simp
  · rename_i a b n h1 h2
    subst h1 h2
    simp

variable [dps : DPSystem T]
variable [dpn : DPNoise dps]

/--
The noised counting query satisfies DP property
-/
@[simp]
theorem privNoisedCount_DP (ε₁ ε₂ : ℕ+) (ε : NNReal) (HP : dpn.noise_priv ε₁ ε₂ ε) :
  dps.prop (privNoisedCount ε₁ ε₂) ε := by
  unfold privNoisedCount
  apply dpn.noise_prop HP
  apply exactCount_1_sensitive

end SLang
