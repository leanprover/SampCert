/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

def CountingQuery (l : List T) : ℤ := List.length l

def NoisedCountingQuery (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  dps.noise CountingQuery 1 ε₁ ε₂ l

end SLang
