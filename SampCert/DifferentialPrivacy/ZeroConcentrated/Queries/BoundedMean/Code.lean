/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Composition.Code
import SampCert.DifferentialPrivacy.ZeroConcentrated.Foundations.Postprocessing.Code
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.Count.Code
import SampCert.DifferentialPrivacy.ZeroConcentrated.Queries.BoundedSum.Code

open Classical Nat Int Real

noncomputable section

namespace SLang

def NoisedBoundedAvgQuery (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ := do
  let S ← NoisedBoundedSumQuery U ε₁ (2 * ε₂) l
  let C ← NoisedCountingQuery ε₁ (2 * ε₂) l
  return S / C

end SLang
