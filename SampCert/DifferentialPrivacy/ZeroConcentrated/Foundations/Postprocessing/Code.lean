/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

def PostProcess (nq : List T → SLang U) (pp : U → ℤ) (l : List T) : SLang ℤ := do
  let A ← nq l
  return pp A

end SLang
