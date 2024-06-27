/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.Count.Code
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Code

/-!
# ``privNoisedBoundedMean`` Implementation

This file defines a differentially private bounded mean query.
-/

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

/--
Compute a noised mean using a noised sum and noised count.
-/
def privNoisedBoundedMean (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℚ := do
  let S ← privNoisedBoundedSum U ε₁ (2 * ε₂) l
  let C ← privNoisedCount ε₁ (2 * ε₂) l
  return S / C

end SLang
