/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.Count.Code
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Code

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

def NoisedBoundedAvgQuery (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℚ := do
  let S ← NoisedBoundedSumQuery U ε₁ (2 * ε₂) l
  let C ← NoisedCountingQuery ε₁ (2 * ε₂) l
  return S / C

end SLang
