/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

def Compose (nq1 nq2 : List T → SLang ℤ) (l : List T) : SLang (ℤ × ℤ) := do
  let A ← nq1 l
  let B ← nq2 l
  return (A,B)

end SLang
