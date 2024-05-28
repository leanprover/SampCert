/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Samplers.LaplaceGen.Code

noncomputable section

namespace SLang

def NoisedQueryPure (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  DiscreteLaplaceGenSample (Δ * ε₂) ε₁ (query l)

end SLang
