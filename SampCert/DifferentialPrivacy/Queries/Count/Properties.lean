/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Count.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

theorem CountingQuery1Sensitive :
  @sensitivity T CountingQuery 1 := by
  simp [CountingQuery, sensitivity]
  intros l₁ l₂ H
  cases H
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a b n h1 h2
    subst h1 h2
    simp
  . rename_i a n b m h1 h2
    subst h1 h2
    simp

@[simp]
theorem NoisedCountingQueryDP (ε₁ ε₂ : ℕ+) :
  dps.prop (NoisedCountingQuery ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  apply dps.noise_prop
  apply CountingQuery1Sensitive

end SLang
