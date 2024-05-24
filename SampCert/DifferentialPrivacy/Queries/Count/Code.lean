/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract

/-!
# Counting Query

This file defines a counting query ``SLang`` term inside a DP system.
-/

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]

/--
Query to count the size of the input
-/
def CountingQuery (l : List T) : ℤ := List.length l

/--
Noised counting mechanism from the DP system
-/
def NoisedCountingQuery (ε₁ ε₂ : ℕ+) (l : List T) : SLang ℤ := do
  dps.noise CountingQuery 1 ε₁ ε₂ l

end SLang
