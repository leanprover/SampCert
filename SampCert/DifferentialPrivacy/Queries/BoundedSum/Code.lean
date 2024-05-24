/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order

/-!
# Code for bounded sum query
-/

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

/--
Bounded sum query: computes a sum and truncates it at an upper bound.
-/
def BoundedSumQuery (U : ℕ+) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n U)) l)

/--
Noised bounded sum query obtained by applying the DP noise mechanism to the bounded sum.
-/
def NoisedBoundedSumQuery (U : ℕ+) (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℤ := do
  dps.noise (BoundedSumQuery U) U ε₁ ε₂ l

end SLang
