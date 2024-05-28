/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Samplers.GaussianGen.Code

/-!
# ``privNoisedQuery`` Implementation

Abstract mechanism for adding the proper amount of noise to a query, depending on the sensitivity.
-/

noncomputable section

namespace SLang

/--
Mechanism obtained by postcomposing query with by gaussian noise (of variance ``(Δ ε₁ / ε₂)^2``).
-/
def privNoisedQuery (query : List T → ℤ) (Δ : ℕ+) (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  DiscreteGaussianGenSample (Δ * ε₂) ε₁ (query l)

end SLang
