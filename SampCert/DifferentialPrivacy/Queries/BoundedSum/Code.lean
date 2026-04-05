/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import Mathlib.Algebra.Group.Defs
import Init.Data.Int.Order

/-!
# ``privNoisedBoundedSum`` Implementation

This file defines a differentially private bounded sum query.
-/

namespace SLang

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

/--
Bounded sum query: computes a sum and truncates it at an upper bound.
-/
def exactBoundedSum (U : ℕ+) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n U)) l)

/--
Noised bounded sum query obtained by applying the DP noise mechanism to the bounded sum.
-/
def privNoisedBoundedSum (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : PMF ℤ := do
  dpn.noise (exactBoundedSum U) U ε₁ ε₂ l

end SLang
