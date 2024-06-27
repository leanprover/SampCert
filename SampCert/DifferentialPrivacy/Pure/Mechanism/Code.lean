/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Samplers.LaplaceGen.Properties

/-!
# Noise Mechanism for Pure Differential Privacy
-/

noncomputable section

namespace SLang

/--
Add noise to a a query from the discrete Laplace distribution, to obtain (Δε₁/ε₂)-DP.
-/
def privNoisedQueryPure (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : PMF ℤ := do
  DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (query l)

end SLang
